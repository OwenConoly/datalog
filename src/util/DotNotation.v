(** Lean-style generalized field notation.

    For [x : A.t], the expression [x.{foo}] elaborates to [A.foo] applied to [x]
    at its first argument of type [A.t], with any preceding arguments filled by
    unification. Namespace-directed, exactly like Lean 4: the field name is
    resolved against the module path of the head constant of [x]'s type, so it
    covers record projections and any other definition in that module. If that
    misses, the head is unfolded a step and the namespace of whatever it
    abbreviates is tried, so aliases work. If every namespace misses,
    elaboration fails naming each qualid that was tried -- there is no fallback
    to a global search for the bare name. *)

From Stdlib Require Import Strings.String.
From Ltac2 Require Import Ltac2.

From coqutil Require Import Macros.ident_to_string.
From coqutil Require Import Tactics.ident_of_string.
From coqutil Require Import Ltac2Lib.Failf.
From coqutil Require Tactics.reference_to_string.
From coqutil Require Tactics.Records.
From coqutil Require Tactics.RecordEta.
From coqutil Require Ltac2Lib.List.
From coqutil Require Ltac2Lib.String.
From coqutil Require Ltac2Lib.rdelta.

(* Importing Ltac2 flips the default proof mode; the Ltac1 hint wrapper and the
   tests below want Classic. *)
Local Set Default Proof Mode "Classic".

(* Singleton class, so [Dot R name T] is convertible to [R -> T] and [cbv [dot]]
   leaves the bare projection with no residue of the name string. *)
Class Dot (R : Type) (name : string) (T : Type) := dot : R -> T.

(* Postpone rather than attempt while an input is evar-headed. Without this a
   chained [w.{inner}.{a}] is attempted outer-first, and the outer failure --
   its receiver type being the not-yet-known result of the inner one -- sinks
   the whole resolution instead of letting the inner goal go first. *)
#[export] Hint Mode Dot ! ! - : typeclass_instances.

(* Not in coqutil, which has [gfail] (backtracking) and [anomaly]
   (non-backtracking but reported as an anomaly, which a missing field is not).
   A backtracking failure inside a [Hint Extern] is indistinguishable from "no
   instance applies", so the constraint would be silently postponed and the
   message lost. Belongs next to [gfail] in coqutil.Ltac2Lib.Failf. *)
Ltac2 gthrow_with_fmt fmt :=
  Message.Format.kfprintf (fun msg => Control.throw (Tactic_failure (Some msg))) fmt.
Ltac2 Notation "gthrow" fmt(format) := gthrow_with_fmt fmt.

(* Not in coqutil: it has [mkApp], but nothing that makes holes, since
   [Constr.Unsafe.Evar] needs a key. *)
Ltac2 rec apply_holes (f : constr) (n : int) : constr :=
  if Int.equal n 0 then f
  else apply_holes open_constr:($f _) (Int.sub n 1).

(* coqutil's [constr_string_qualname_of_reference] takes a [reference]; the
   path we need to print is the one that did not resolve to one. *)
Ltac2 qualid_to_string (q : ident list) : string :=
  String.join "." (List.map Ident.to_string q).

(* [Var] is deliberately excluded: [Env.path] of a [VarRef] is just [id], so
   dropping the last component leaves the empty qualification and [Env.get]
   would then resolve the field by short name -- a global fallback. *)
Ltac2 has_namespace (h : constr) : bool :=
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constant _ _ => true
  | Constr.Unsafe.Ind _ _ => true
  | Constr.Unsafe.Constructor _ _ => true
  | _ => false
  end.

(* [r] is the receiver's type as written, kept for error messages; [rhead] is
   the head currently being resolved against, which may be an unfolding of
   [r]'s own head. [tried] accumulates the qualids that missed. *)
Ltac2 rec solve_dot_from (r : constr) (rhead : constr) (fld : ident)
                         (tried : string list) : unit :=
  match Constr.Unsafe.kind rhead with
  | Constr.Unsafe.Evar _ _ =>
      (* Backstop for the Hint Mode above: soft-fail so resolution is postponed
         until the surrounding elaboration fixes the receiver's type. *)
      gfail "dot: receiver type not known yet, postponing"
  | _ =>
  let oq :=
    if has_namespace rhead
    then Some (List.append
                 (List.removelast
                    (Env.path (reference_to_string.reference_of_constr rhead)))
                 [fld])
    else None in
  match (match oq with Some q => Env.get q | None => None end) with
  | Some fref =>
      let fc := Env.instantiate fref in
      (* RecordEta's strip_foralls returns the binders; the one in Records.v
         discards them. *)
      let (binders, _) := RecordEta.strip_foralls (Constr.type fc) in
      match List.find_with_index_opt
              (fun b => Constr.equal (Records.head (Constr.Binder.type b)) rhead)
              binders with
      | None =>
          gthrow "dot: %s takes no argument of type %t"
                 (String.join ", " tried) rhead
      | Some p =>
          let (_, n) := p in
          let res := apply_holes fc n in
          exact $res
      end
  | None =>
      let tried := match oq with
                   | Some q => List.append tried [qualid_to_string q]
                   | None => tried
                   end in
      (* Unfolding only after a direct miss is what keeps a defined type-former's
         own namespace: with [Vec.t := list nat], [v.{sum}] must find [Vec.sum]
         rather than reduce to [list] first and pick up [Datatypes.sum].
         [strip_lambdas] covers a parameterized abbreviation, whose unfolding is
         a lambda -- only the head reference is needed, not a well-formed type. *)
      let rhead' := Records.head (Records.strip_lambdas (rdelta.rdelta rhead)) in
      if Constr.equal rhead' rhead then
        match tried with
        | [] =>
            gthrow "dot: cannot resolve .{%s}: receiver type %t is headed by %t, which is not a global name, so there is no namespace to look in"
                   (Ident.to_string fld) r rhead
        | _ :: _ =>
            gthrow "dot: no such name (tried %s) while looking up .{%s} from receiver type %t"
                   (String.join ", " tried) (Ident.to_string fld) r
        end
      else solve_dot_from r rhead' fld tried
  end
  end.

Ltac2 solve_dot () : unit :=
  lazy_match! goal with
  | [ |- Dot ?r ?nm _ ] =>
      solve_dot_from r (Records.head r) (ident_of_constr_string nm) []
  | [ |- _ ] => gthrow "dot: unexpected goal shape"
  end.

Ltac solve_dot_ltac1 := ltac2:(solve_dot ()).

#[export] Hint Extern 1 (Dot _ _ _) => solve_dot_ltac1 : typeclass_instances.

(* [f ident] is what lets an unqualified, possibly-unimported name through the
   parser without being resolved as a term. [.{ }] rather than [.[ ]] because
   the latter is taken by PrimArray and by mathcomp's finmap/tuple, which take a
   term index where this needs an ident, so they would override rather than
   disambiguate. *)
Notation "x .{ f }" := (@dot _ (ident_to_string! f) _ _ x)
  (at level 2, f ident, left associativity, only parsing).

(* Printing. The elaborated term is [@dot A.t "a" nat A.a x], which Coq shows as
   [dot x]; the instance argument is the term the hint resolved to, so printing
   that answers the question [Check] was run to ask.

   The delimiter has to differ from the parsed one: a notation key fixes the
   kind of its arguments, and [f] is an [ident] when parsing but a [constr] when
   printing, so reusing [.{ }] is rejected. [.{{ }}] does not re-parse. True
   round-tripping is out of reach either way -- printing the string "a" as the
   identifier [a] needs one notation per field name. Swap the body for
   [(@dot _ f _ _ x)] to show the name looked up instead of what it found. *)
Notation "x .{{ f }}" := (@dot _ _ _ f x)
  (at level 2, left associativity, only printing, format "x .{{ f }}").

Module Tests.

  Module A.
    Record t := { a : nat ; b : bool }.
    Definition double (x : t) : nat := 2 * a x.
  End A.

  Module B.
    Record t := { a : list nat ; b : nat }.
  End B.

  Module P.
    Record t (X : Type) := { elem : X ; count : nat }.
    Arguments elem {X}.
    Arguments count {X}.
  End P.

  Module Nested.
    Record t := { inner : A.t }.
  End Nested.

  (* Colliding field names, resolved by the receiver's type. *)
  Definition t_a (x : A.t) : nat := x.{a}.
  Definition t_a' (y : B.t) : list nat := y.{a}.
  Definition t_b (x : A.t) : bool := x.{b}.
  Definition t_b' (y : B.t) : nat := y.{b}.

  (* Generalized as in Lean: any definition in the module, not just a field. *)
  Definition t_nonfield (x : A.t) : nat := x.{double}.

  (* [apply_holes]: P.elem's first argument is the type parameter. *)
  Definition t_param (z : P.t bool) : bool := z.{elem}.
  Definition t_param' (z : P.t bool) : nat := z.{count}.

  Definition t_chain (w : Nested.t) : nat := w.{inner}.{a}.
  Definition t_chain' (w : Nested.t) : nat := w.{inner}.{double}.

  (* Postponed while the receiver's type is still an evar. *)
  Definition t_postponed : nat := (fun q => q.{a}) (A.Build_t 3 true).

  Fail Definition t_miss (z : P.t bool) := z.{missing}.
  Fail Definition t_miss' (x : A.t) := x.{c}.
  Fail Definition t_miss'' (w : Nested.t) := w.{inner}.{nope}.
  (* B.t has no [double] even though A.t does. *)
  Fail Definition t_no_fallback (y : B.t) := y.{double}.
  (* A receiver type with no namespace at all. *)
  Fail Definition t_no_namespace (X : Type) (v : X) := v.{a}.

  (* Unfolding: a miss retries against what the head abbreviates. *)
  Definition alias := A.t.
  Definition t_alias (r : alias) : nat := r.{a}.
  Definition t_alias' (r : alias) : nat := r.{double}.

  Definition alias2 := alias.
  Definition t_alias_chain (r : alias2) : nat := r.{a}.

  Definition palias := P.t.
  Definition t_alias_param (r : palias bool) : bool := r.{elem}.
  Definition palias2 (X : Type) := P.t X.
  Definition t_alias_param' (r : palias2 bool) : bool := r.{elem}.

  Section LetAlias.
    Let lalias := A.t.
    Definition t_alias_let (r : lalias) : nat := r.{a}.
  End LetAlias.

  Fail Definition t_alias_miss (r : alias) := r.{nope}.

  (* Unfolding must stay lazy: [Vec.sum] wins over anything reachable by
     reducing [Vec.t] to [list nat]. *)
  Module Vec.
    Definition t := list nat.
    Definition sum (v : t) : nat := Datatypes.length v.
  End Vec.

  Goal forall v : Vec.t, v.{sum} = Vec.sum v.
  Proof. intros. cbv [dot]. reflexivity. Qed.

  (* ...but a name Vec does not have is looked for in [list]'s namespace. *)
  Goal forall v : Vec.t, v.{length} = Datatypes.length v.
  Proof. intros. cbv [dot]. reflexivity. Qed.

  (* Arguments preceding the receiver are filled with holes, which is right when
     the receiver's type determines them (P.elem's [X]) but diverges from Lean
     for a genuinely explicit one -- Lean's [r.addto 5] is [addto 5 r].
     Reproducing that needs implicit-argument status, which Ltac2's Env does not
     expose. The hole is never silently wrong; it surfaces as an uninferable
     placeholder. *)
  Module Q.
    Record t := { qf : nat }.
    Definition addto (k : nat) (r : t) : nat := k + qf r.
  End Q.
  Fail Definition t_explicit_prefix (r : Q.t) : nat := r.{addto}.

  (* No residue of the name string in the elaborated term. *)
  Goal forall x : A.t, x.{a} = A.a x.
  Proof. intros. cbv [dot]. reflexivity. Qed.

  Goal forall p : P.t bool, p.{elem} = P.elem p.
  Proof. intros. cbv [dot]. reflexivity. Qed.

  Module Prim.
    Set Primitive Projections.
    Record t := { pa : nat ; pb : bool }.
  End Prim.

  Goal forall p : Prim.t, p.{pa} = Prim.pa p.
  Proof. intros. cbv [dot]. reflexivity. Qed.

End Tests.
