From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.

From coqutil Require Import Map.Interface Tactics.fwd Datatypes.List Decidable Tactics.destr.

From Datalog Require Import Datalog Tactics List.

Import ListNotations.

(* --- Small list helpers local to this file --- *)

Fixpoint dedup {A} (eqb : A -> A -> bool) (xs : list A) : list A :=
  match xs with
  | [] => []
  | x :: xs' =>
      let rest := dedup eqb xs' in
      if existsb (eqb x) rest then rest else x :: rest
  end.

Fixpoint find_index {A} (eqb : A -> A -> bool) (xs : list A) (x : A) : nat :=
  match xs with
  | [] => 0
  | y :: ys => if eqb x y then 0 else S (find_index eqb ys x)
  end.

Lemma find_index_In {A} (eqb : A -> A -> bool)
  `{Heqb : EqDecider eqb}
  (xs : list A) (x : A) :
  In x xs -> nth_error xs (find_index eqb xs x) = Some x.
Proof.
  induction xs as [|y ys IH]; simpl; [contradiction|].
  destr (eqb x y).
  - intros _. reflexivity.
  - intros [Heq|Hin]; [congruence|]. apply IH. assumption.
Qed.

Lemma find_index_nth_error_NoDup {A} (eqb : A -> A -> bool)
  `{Heqb : EqDecider eqb}
  (xs : list A) (n : nat) (x : A) :
  NoDup xs ->
  nth_error xs n = Some x ->
  find_index eqb xs x = n.
Proof.
  revert n. induction xs as [|y ys IH]; intros n Hnd Hnth; simpl in *.
  - destruct n; discriminate.
  - inversion Hnd; subst.
    destruct n as [|n']; simpl in Hnth.
    + injection Hnth as Hyx.
      destr (eqb x y); [reflexivity|congruence].
    + assert (Hin: In x ys) by (eapply nth_error_In; eassumption).
      destr (eqb x y); [contradiction|].
      f_equal. apply IH; assumption.
Qed.

Lemma find_index_inj {A} (eqb : A -> A -> bool)
  `{Heqb : EqDecider eqb}
  (xs : list A) (x1 x2 : A) :
  NoDup xs ->
  In x1 xs -> In x2 xs ->
  find_index eqb xs x1 = find_index eqb xs x2 ->
  x1 = x2.
Proof.
  intros Hnd H1 H2 Heq.
  apply (find_index_In eqb) in H1, H2.
  rewrite Heq in H1. rewrite H1 in H2. injection H2 as <-. reflexivity.
Qed.

Lemma dedup_In {A} (eqb : A -> A -> bool)
  `{Heqb : EqDecider eqb}
  (xs : list A) (x : A) :
  In x (dedup eqb xs) <-> In x xs.
Proof.
  induction xs as [|y ys IH]; simpl; [reflexivity|].
  destruct (existsb (eqb y) (dedup eqb ys)) eqn:Eex.
  - rewrite IH. split; intros.
    + auto.
    + destruct H as [<-|H]; auto.
      apply existsb_exists in Eex. destruct Eex as [z [Hzin Hzeq]].
      destr (eqb y z); [|discriminate].
      apply IH. assumption.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma dedup_NoDup {A} (eqb : A -> A -> bool)
  `{Heqb : EqDecider eqb}
  (xs : list A) :
  NoDup (dedup eqb xs).
Proof.
  induction xs as [|y ys IH]; simpl; [constructor|].
  destruct (existsb (eqb y) (dedup eqb ys)) eqn:Eex; [assumption|].
  constructor; [|assumption].
  intros Hin.
  apply Bool.not_true_iff_false in Eex. apply Eex.
  apply existsb_exists. exists y. split; [assumption|].
  destr (eqb y y); [reflexivity|congruence].
Qed.

(* --- Generic syntactic maps over rel and var --- *)
(* expr_varmap already exists in Datalog.v and handles vars in exprs. *)
(* Below we define maps that also push through rel. *)

Definition clause_relvarmap {rel1 rel2 var1 var2 fn}
           (fr : rel1 -> rel2) (fv : var1 -> var2)
           (c : clause rel1 var1 fn) : clause rel2 var2 fn :=
  {| clause_rel := fr c.(clause_rel);
     clause_args := map (expr_varmap fv) c.(clause_args) |}.

Definition meta_clause_relvarmap {rel1 rel2 var1 var2 fn}
           (fr : rel1 -> rel2) (fv : var1 -> var2)
           (c : meta_clause rel1 var1 fn) : meta_clause rel2 var2 fn :=
  {| meta_clause_rel := fr c.(meta_clause_rel);
     meta_clause_args := map (option_map (expr_varmap fv)) c.(meta_clause_args) |}.

Definition rule_relvarmap {rel1 rel2 var1 var2 fn agg}
           (fr : rel1 -> rel2) (fv : var1 -> var2)
           (r : rule rel1 var1 fn agg) : rule rel2 var2 fn agg :=
  match r with
  | normal_rule concls hyps =>
      normal_rule (map (clause_relvarmap fr fv) concls)
                  (map (clause_relvarmap fr fv) hyps)
  | meta_rule concls hyps =>
      meta_rule (map (meta_clause_relvarmap fr fv) concls)
                (map (meta_clause_relvarmap fr fv) hyps)
  | agg_rule cr ag hr =>
      agg_rule (fr cr) ag (fr hr)
  end.

Definition fact_relmap {rel1 rel2 T} (fr : rel1 -> rel2)
           (f : fact rel1 T) : fact rel2 T :=
  match f with
  | normal_fact R args => normal_fact (fr R) args
  | meta_fact R args mf_set => meta_fact (fr R) args mf_set
  end.

Section Nattify.
  Context {rel var fn aggregator : Type}.

  Context {rel_eqb : rel -> rel -> bool}
          {rel_eqb_spec : forall x y, BoolSpec (x = y) (x <> y) (rel_eqb x y)}.
  Context {var_eqb : var -> var -> bool}
          {var_eqb_spec : forall x y, BoolSpec (x = y) (x <> y) (var_eqb x y)}.

  (* --- 1. Enumerate atoms appearing in syntax --- *)

  Fixpoint rels_of_expr (e : expr var fn) : list rel :=
    match e with
    | var_expr _ => []
    | fun_expr _ args => flat_map rels_of_expr args
    end.

  Definition rels_of_clause (c : clause rel var fn) : list rel :=
    c.(clause_rel) :: flat_map rels_of_expr c.(clause_args).

  Definition vars_of_clause' (c : clause rel var fn) : list var :=
    flat_map vars_of_expr c.(clause_args).

  Definition rels_of_meta_clause (c : meta_clause rel var fn) : list rel :=
    c.(meta_clause_rel) :: flat_map rels_of_expr (keep_Some c.(meta_clause_args)).

  Definition vars_of_meta_clause' (c : meta_clause rel var fn) : list var :=
    flat_map vars_of_expr (keep_Some c.(meta_clause_args)).

  Definition rels_of_rule (r : rule rel var fn aggregator) : list rel :=
    match r with
    | normal_rule concls hyps =>
        flat_map rels_of_clause (concls ++ hyps)
    | meta_rule concls hyps =>
        flat_map rels_of_meta_clause (concls ++ hyps)
    | agg_rule cr _ hr => [cr; hr]
    end.

  Definition vars_of_rule (r : rule rel var fn aggregator) : list var :=
    match r with
    | normal_rule concls hyps =>
        flat_map vars_of_clause' (concls ++ hyps)
    | meta_rule concls hyps =>
        flat_map vars_of_meta_clause' (concls ++ hyps)
    | agg_rule _ _ _ => []
    end.

  Definition rels_of_prog (p : list (rule rel var fn aggregator)) : list rel :=
    flat_map rels_of_rule p.
  Definition vars_of_prog (p : list (rule rel var fn aggregator)) : list var :=
    flat_map vars_of_rule p.

  (* --- 2. Tables --- *)

  Record nattify_tables :=
    { tbl_rels : list rel;
      tbl_vars : list var }.

  Definition tables_of_prog (p : list (rule rel var fn aggregator)) : nattify_tables :=
    {| tbl_rels := dedup rel_eqb (rels_of_prog p);
       tbl_vars := dedup var_eqb (vars_of_prog p) |}.

  (* --- 3. Encoding atoms as nats --- *)

  Definition encode_rel (t : nattify_tables) (R : rel) : nat :=
    find_index rel_eqb t.(tbl_rels) R.
  Definition encode_var (t : nattify_tables) (v : var) : nat :=
    find_index var_eqb t.(tbl_vars) v.

  (* --- 4. The nattify pass --- *)

  Definition nattify_rule (t : nattify_tables)
             (r : rule rel var fn aggregator) : rule nat nat fn aggregator :=
    rule_relvarmap (encode_rel t) (encode_var t) r.

  Definition nattify_prog (p : list (rule rel var fn aggregator))
    : list (rule nat nat fn aggregator) * nattify_tables :=
    let t := tables_of_prog p in
    (map (nattify_rule t) p, t).

  Definition nattify_fact {T : Type} (t : nattify_tables) (f : fact rel T) : fact nat T :=
    fact_relmap (encode_rel t) f.

  (* === Correctness === *)

  Section Correctness.
    Context {T : Type}.
    Context `{sig : signature fn aggregator T}.
    Context {context : map.map var T} {context_ok : map.ok context}.
    Context {nat_context : map.map nat T} {nat_context_ok : map.ok nat_context}.

    (* nat-context agrees with var-context on table vars. *)
    Definition ctx_corresp (t : nattify_tables)
               (ctx : context) (ctxn : nat_context) : Prop :=
      forall v, In v t.(tbl_vars) ->
                map.get ctxn (encode_var t v) = map.get ctx v.

    Definition translate_ctx (t : nattify_tables) (ctx : context) : nat_context :=
      fold_right (fun v m =>
        match map.get ctx v with
        | Some x => map.put m (encode_var t v) x
        | None => m
        end) map.empty t.(tbl_vars).

    Definition untranslate_ctx (t : nattify_tables) (ctxn : nat_context) : context :=
      fold_right (fun v m =>
        match map.get ctxn (encode_var t v) with
        | Some x => map.put m v x
        | None => m
        end) map.empty t.(tbl_vars).

    Lemma fold_put_other (vs : list var) (encode : var -> nat) (ctx : context) (k : nat) :
      (forall v', In v' vs -> encode v' <> k) ->
      map.get
        (fold_right (fun v0 m =>
          match map.get ctx v0 with
          | Some x => map.put m (encode v0) x
          | None => m
          end) map.empty vs) k = None.
    Proof.
      induction vs as [|v0 vs IH]; intros Hne; simpl.
      - apply map.get_empty.
      - destruct (map.get ctx v0) eqn:Eg.
        + rewrite map.get_put_diff.
          * apply IH. intros v' Hv'. apply Hne. right. assumption.
          * intros Heq. apply (Hne v0); [left; reflexivity|]. symmetry. assumption.
        + apply IH. intros v' Hv'. apply Hne. right. assumption.
    Qed.

    Lemma fold_put_get (vs : list var) (encode : var -> nat) (ctx : context) (v : var) :
      NoDup vs ->
      In v vs ->
      (forall v1 v2, In v1 vs -> In v2 vs -> encode v1 = encode v2 -> v1 = v2) ->
      map.get
        (fold_right (fun v0 m =>
          match map.get ctx v0 with
          | Some x => map.put m (encode v0) x
          | None => m
          end) map.empty vs) (encode v) = map.get ctx v.
    Proof.
      intros Hnd Hin Hinj.
      induction vs as [|v0 vs IH]; simpl in *; [contradiction|].
      inversion Hnd; subst.
      destruct Hin as [Heq|Hin].
      - (* v0 = v: v is the head *)
        subst v.
        destruct (map.get ctx v0) eqn:Eg.
        + rewrite map.get_put_same. reflexivity.
        + apply fold_put_other.
          intros v' Hv' Heqe.
          assert (v0 = v') by (apply Hinj; simpl; auto).
          subst v'. contradiction.
      - (* v is in tail *)
        assert (Hinj' : forall v1 v2, In v1 vs -> In v2 vs -> encode v1 = encode v2 -> v1 = v2).
        { intros v1 v2 Hv1 Hv2 He. apply Hinj; simpl; auto. }
        destruct (map.get ctx v0) eqn:Eg.
        + rewrite map.get_put_diff.
          { apply IH; auto. }
          { intros Heq.
            assert (v = v0).
            { apply Hinj; simpl; auto. }
            subst v0. contradiction. }
        + apply IH; auto.
    Qed.

    Lemma encode_var_inj_on_tbl (t : nattify_tables) :
      NoDup t.(tbl_vars) ->
      forall v1 v2, In v1 t.(tbl_vars) -> In v2 t.(tbl_vars) ->
                    encode_var t v1 = encode_var t v2 -> v1 = v2.
    Proof. cbv [encode_var]. intros. eapply find_index_inj; eauto. Qed.

    Lemma translate_ctx_corresp (t : nattify_tables) (ctx : context) :
      NoDup t.(tbl_vars) ->
      ctx_corresp t ctx (translate_ctx t ctx).
    Proof.
      intros Hnd. cbv [ctx_corresp translate_ctx].
      intros v Hv. apply fold_put_get; auto.
      apply encode_var_inj_on_tbl. assumption.
    Qed.

    Lemma fold_untranslate_get (vs : list var) (encode : var -> nat)
                               (ctxn : nat_context) (v : var) :
      NoDup vs ->
      In v vs ->
      map.get
        (fold_right (fun v0 m =>
          match map.get ctxn (encode v0) with
          | Some x => map.put m v0 x
          | None => m
          end) map.empty vs) v = map.get ctxn (encode v).
    Proof.
      intros Hnd Hin.
      induction vs as [|v0 vs IH]; simpl in *; [contradiction|].
      inversion Hnd; subst.
      destruct Hin as [Heq|Hin].
      - subst v.
        destruct (map.get ctxn (encode v0)) eqn:Eg.
        + rewrite map.get_put_same. reflexivity.
        + assert (Hgone : forall (vs0 : list var),
                   ~ In v0 vs0 ->
                   map.get
                     (fold_right (fun v1 (m : context) =>
                       match map.get ctxn (encode v1) with
                       | Some x => map.put m v1 x
                       | None => m
                       end) map.empty vs0) v0 = None).
          { induction vs0 as [|v1 vs0 IH2]; simpl;
              [intros _; apply map.get_empty|].
            intros Hni.
            destruct (map.get ctxn (encode v1)) eqn:Eg2.
            - rewrite map.get_put_diff.
              { apply IH2. intros Hi. apply Hni. right. assumption. }
              { intros Heq. subst v1. apply Hni. left. reflexivity. }
            - apply IH2. intros Hi. apply Hni. right. assumption. }
          apply Hgone; assumption.
      - destruct (map.get ctxn (encode v0)) eqn:Eg.
        + rewrite map.get_put_diff.
          * apply IH; auto.
          * intros Heq. subst v0. contradiction.
        + apply IH; auto.
    Qed.

    Lemma untranslate_ctx_corresp (t : nattify_tables) (ctxn : nat_context) :
      NoDup t.(tbl_vars) ->
      ctx_corresp t (untranslate_ctx t ctxn) ctxn.
    Proof.
      intros Hnd. cbv [ctx_corresp untranslate_ctx].
      intros v Hv. symmetry. apply fold_untranslate_get; auto.
    Qed.

    Lemma interp_expr_nattify
      (t : nattify_tables) (ctx : context) (ctxn : nat_context)
      (e : expr var fn) (v : T) :
      ctx_corresp t ctx ctxn ->
      incl (vars_of_expr e) t.(tbl_vars) ->
      (interp_expr ctx e v <->
       interp_expr ctxn (expr_varmap (encode_var t) e) v).
    Proof.
      revert v.
      induction e as [v1|f args IHargs] using expr_ind;
        intros v0 Hcorresp Hincl; simpl.
      - (* var_expr *)
        assert (Hin : In v1 t.(tbl_vars)) by (apply Hincl; simpl; auto).
        split; intros Hint; invert Hint; constructor.
        + rewrite Hcorresp by assumption. assumption.
        + rewrite <- Hcorresp by assumption. assumption.
      - (* fun_expr *)
        assert (Hincls :
                  Forall (fun e0 => incl (vars_of_expr e0) t.(tbl_vars)) args).
        { simpl in Hincl. rewrite Forall_forall. intros a Hain.
          intros v Hv. apply Hincl. apply in_flat_map. eauto. }
        split; intros Hint.
        + invert Hint.
          econstructor; [|eassumption].
          rewrite <- Forall2_map_l.
          eapply Forall2_impl_strong; [|eassumption].
          intros a a' Ha Hain _.
          rewrite Forall_forall in IHargs, Hincls.
          eapply IHargs; eauto.
        + invert Hint.
          econstructor.
          2: { eassumption. }
          match goal with
          | H : Forall2 _ (map _ _) _ |- _ =>
              rewrite <- Forall2_map_l in H;
              eapply Forall2_impl_strong; [|exact H]
          end.
          intros a a' Ha Hain _.
          rewrite Forall_forall in IHargs, Hincls.
          eapply IHargs; eauto.
    Qed.

    Lemma interp_clause_nattify
      (t : nattify_tables) (ctx : context) (ctxn : nat_context)
      (c : clause rel var fn) (f : fact rel T) :
      ctx_corresp t ctx ctxn ->
      NoDup t.(tbl_rels) ->
      In c.(clause_rel) t.(tbl_rels) ->
      incl (vars_of_clause' c) t.(tbl_vars) ->
      In (rel_of f) t.(tbl_rels) ->
      (interp_clause ctx c f <->
       interp_clause ctxn
         (clause_relvarmap (encode_rel t) (encode_var t) c)
         (nattify_fact t f)).
    Proof.
      intros Hcorresp Hnd Hcrel_in Hvars_in Hfrel_in.
      assert (Hincl_each :
                Forall (fun a => incl (vars_of_expr a) t.(tbl_vars)) c.(clause_args)).
      { cbv [vars_of_clause'] in Hvars_in.
        rewrite Forall_forall. intros a Hain v Hv.
        apply Hvars_in. apply in_flat_map. eauto. }
      cbv [interp_clause].
      destruct f as [R args|R args mf_set]; simpl in *.
      - (* normal_fact *)
        split; intros (nf_args & Hfa & Heq).
        + injection Heq as Hrel Hargs. subst R. subst args.
          exists nf_args. split; [|reflexivity].
          rewrite <- Forall2_map_l.
          eapply Forall2_impl_strong; [|eassumption].
          intros a a' Ha Hain _.
          rewrite Forall_forall in Hincl_each.
          apply (proj1 (interp_expr_nattify t ctx ctxn a a' Hcorresp (Hincl_each _ Hain))).
          exact Ha.
        + injection Heq as Hrel Hargs. subst nf_args.
          assert (R = c.(clause_rel)).
          { eapply find_index_inj; eauto. }
          subst R. exists args. split; [|reflexivity].
          rewrite <- Forall2_map_l in Hfa.
          eapply Forall2_impl_strong; [|exact Hfa].
          intros a a' Ha Hain _.
          rewrite Forall_forall in Hincl_each.
          apply (proj2 (interp_expr_nattify t ctx ctxn a a' Hcorresp (Hincl_each _ Hain))).
          exact Ha.
      - (* meta_fact: both false *)
        split; intros (nf_args & Hfa & Heq); discriminate.
    Qed.

    Lemma interp_meta_clause_nattify
      (t : nattify_tables) (ctx : context) (ctxn : nat_context)
      (c : meta_clause rel var fn) (f : fact rel T) :
      ctx_corresp t ctx ctxn ->
      NoDup t.(tbl_rels) ->
      In c.(meta_clause_rel) t.(tbl_rels) ->
      incl (vars_of_meta_clause' c) t.(tbl_vars) ->
      In (rel_of f) t.(tbl_rels) ->
      (interp_meta_clause ctx c f <->
       interp_meta_clause ctxn
         (meta_clause_relvarmap (encode_rel t) (encode_var t) c)
         (nattify_fact t f)).
    Proof.
      intros Hcorresp Hnd Hcrel_in Hvars_in Hfrel_in.
      assert (Hincl_each :
                Forall (fun oe =>
                          match oe with
                          | Some e0 => incl (vars_of_expr e0) t.(tbl_vars)
                          | None => True
                          end) c.(meta_clause_args)).
      { cbv [vars_of_meta_clause'] in Hvars_in.
        rewrite Forall_forall. intros [a|] Hain; [|exact I].
        intros v Hv. apply Hvars_in. apply in_flat_map.
        eexists. split; [|eassumption]. apply in_keep_Some. assumption. }
      cbv [interp_meta_clause].
      destruct f as [R args|R mf_args mf_set]; simpl in *.
      - (* normal_fact: both false *)
        split; intros (? & ? & ? & Heq); discriminate.
      - (* meta_fact *)
        split; intros (mf_args' & mf_set' & Hfa & Heq).
        + injection Heq as Hrel Hmargs Hmset.
          subst R. subst mf_args. subst mf_set.
          exists mf_args', mf_set'. split; [|reflexivity].
          rewrite <- Forall2_map_l.
          eapply Forall2_impl_strong; [|eassumption].
          intros [a|] [ay|] Ha Hain _; simpl in Ha |- *;
            try contradiction; try discriminate; try reflexivity.
          rewrite Forall_forall in Hincl_each.
          specialize (Hincl_each _ Hain). simpl in Hincl_each.
          apply (proj1 (interp_expr_nattify t ctx ctxn a ay Hcorresp Hincl_each)).
          exact Ha.
        + injection Heq as Hrel Hmargs Hmset.
          subst mf_args'. subst mf_set'.
          assert (R = c.(meta_clause_rel)).
          { eapply find_index_inj; eauto. }
          subst R. exists mf_args, mf_set. split; [|reflexivity].
          rewrite <- Forall2_map_l in Hfa.
          eapply Forall2_impl_strong; [|exact Hfa].
          intros [a|] [ay|] Ha Hain _; simpl in Ha |- *;
            try contradiction; try discriminate; try reflexivity.
          rewrite Forall_forall in Hincl_each.
          specialize (Hincl_each _ Hain). simpl in Hincl_each.
          apply (proj2 (interp_expr_nattify t ctx ctxn a ay Hcorresp Hincl_each)).
          exact Ha.
    Qed.

    (* --- Rule-level lemmas --- *)

    Lemma nattify_fact_rel_of (t : nattify_tables) (f : fact rel T) :
      rel_of (nattify_fact t f) = encode_rel t (rel_of f).
    Proof. destruct f; reflexivity. Qed.

    Lemma nattify_fact_inj (t : nattify_tables) (f1 f2 : fact rel T) :
      NoDup t.(tbl_rels) ->
      In (rel_of f1) t.(tbl_rels) ->
      In (rel_of f2) t.(tbl_rels) ->
      nattify_fact t f1 = nattify_fact t f2 ->
      f1 = f2.
    Proof.
      intros Hnd H1 H2 Heq.
      destruct f1 as [R1 args1|R1 args1 S1], f2 as [R2 args2|R2 args2 S2];
        simpl in *; try discriminate.
      - injection Heq as Hrel <-.
        f_equal. eapply find_index_inj; eauto.
      - injection Heq as Hrel <- <-.
        f_equal. eapply find_index_inj; eauto.
    Qed.

    Definition decode_fact (default : rel) (t : nattify_tables)
                           (fnat : fact nat T) : fact rel T :=
      match fnat with
      | normal_fact n args => normal_fact (nth n t.(tbl_rels) default) args
      | meta_fact n args mfset => meta_fact (nth n t.(tbl_rels) default) args mfset
      end.

    Lemma nth_find_index {A} (eqb : A -> A -> bool)
      `{Heqb : EqDecider eqb}
      (xs : list A) (x default : A) :
      In x xs -> nth (find_index eqb xs x) xs default = x.
    Proof.
      intros Hin.
      apply (find_index_In eqb) in Hin.
      revert Hin. generalize (find_index eqb xs x) as n.
      induction xs as [|y ys IH]; intros n Hn; [destruct n; discriminate|].
      destruct n; simpl in *.
      - injection Hn as <-. reflexivity.
      - apply IH. assumption.
    Qed.

    Lemma decode_nattify_inverse (default : rel) (t : nattify_tables) (f : fact rel T) :
      In (rel_of f) t.(tbl_rels) ->
      decode_fact default t (nattify_fact t f) = f.
    Proof.
      intros Hin. destruct f as [R args|R args mfset]; simpl in *;
        cbv [encode_rel]; f_equal; apply nth_find_index; assumption.
    Qed.

    Lemma nth_error_to_nth {A} (xs : list A) (n : nat) (x default : A) :
      nth_error xs n = Some x -> nth n xs default = x.
    Proof.
      revert n. induction xs as [|y ys IH]; intros [|n] H; simpl in *;
        try discriminate; auto.
      injection H as <-. reflexivity.
    Qed.

    Lemma fnat_decodable_to_original
      (t : nattify_tables) (default : rel) (fnat : fact nat T) (R0 : rel) :
      NoDup t.(tbl_rels) ->
      nth_error t.(tbl_rels) (rel_of fnat) = Some R0 ->
      In (rel_of (decode_fact default t fnat)) t.(tbl_rels) /\
      nattify_fact t (decode_fact default t fnat) = fnat.
    Proof.
      intros Hnd Hnth.
      assert (HinR0 : In R0 t.(tbl_rels)) by (eapply nth_error_In; eassumption).
      assert (Hfind : find_index rel_eqb t.(tbl_rels) R0 = rel_of fnat).
      { eapply find_index_nth_error_NoDup; eauto. }
      destruct fnat as [n args|n args mfset]; simpl in *;
        rewrite (nth_error_to_nth _ _ _ default Hnth);
        (split; [assumption|]); cbv [encode_rel]; rewrite Hfind; reflexivity.
    Qed.

    Lemma map_nattify_eq_normal_facts
      (t : nattify_tables) (hyps : list (fact rel T))
      (hr : rel) (args0 : list T) (vals : list (T * T)) :
      NoDup t.(tbl_rels) ->
      In hr t.(tbl_rels) ->
      Forall (fun h => In (rel_of h) t.(tbl_rels)) hyps ->
      map (nattify_fact t) hyps
        = map (fun '(i, x_i) =>
                 normal_fact (encode_rel t hr) (i :: x_i :: args0)) vals ->
      hyps = map (fun '(i, x_i) => normal_fact hr (i :: x_i :: args0)) vals.
    Proof.
      intros Hnd Hhr Hin. revert vals.
      induction hyps as [|h hyps' IH]; intros [|[i x_i] vals'] Heq;
        simpl in *; try discriminate; auto.
      injection Heq as Hh Hrest.
      inversion Hin; subst.
      assert (h = normal_fact hr (i :: x_i :: args0)).
      { destruct h as [Rh argsh|Rh argsh Sh]; [|discriminate].
        simpl in Hh, H1. injection Hh as Hr <-.
        f_equal. eapply find_index_inj; eauto. }
      subst h. f_equal. apply IH; auto.
    Qed.

    Lemma non_meta_rule_impl_nattify
      (t : nattify_tables) (r : rule rel var fn aggregator)
      (R : rel) (args : list T) (hyps : list (fact rel T)) :
      NoDup t.(tbl_rels) ->
      NoDup t.(tbl_vars) ->
      incl (rels_of_rule r) t.(tbl_rels) ->
      incl (vars_of_rule r) t.(tbl_vars) ->
      In R t.(tbl_rels) ->
      Forall (fun h => In (rel_of h) t.(tbl_rels)) hyps ->
      (non_meta_rule_impl r R args hyps <->
       non_meta_rule_impl
         (rule_relvarmap (encode_rel t) (encode_var t) r)
         (encode_rel t R) args
         (map (nattify_fact t) hyps)).
    Proof.
      intros Hnd_r Hnd_v Hincl_r Hincl_v Hin_R Hin_hyps.
      split.
      - (* fwd *)
        intros H. invert H.
        + (* normal_rule_impl *)
          set (ctxn := translate_ctx t ctx).
          pose proof (translate_ctx_corresp t ctx Hnd_v) as Hcorresp.
          simpl. eapply normal_rule_impl with (ctx := ctxn).
          * apply Exists_exists in H0. fwd. apply Exists_exists.
            exists (clause_relvarmap (encode_rel t) (encode_var t) x). split.
            { apply in_map_iff. eauto. }
            { assert (Hcrel : In x.(clause_rel) t.(tbl_rels)).
              { apply Hincl_r. simpl. apply in_flat_map. exists x.
                split; [apply in_app_iff; left; assumption|]. left. reflexivity. }
              assert (Hcvars : incl (vars_of_clause' x) t.(tbl_vars)).
              { intros v Hv. apply Hincl_v. simpl. apply in_flat_map. exists x.
                split; [apply in_app_iff; left; assumption|]. exact Hv. }
              eapply (proj1 (interp_clause_nattify t ctx ctxn x (normal_fact R args)
                              Hcorresp Hnd_r Hcrel Hcvars Hin_R)).
              exact H0p1. }
          * rewrite <- Forall2_map_l. rewrite <- Forall2_map_r.
            eapply Forall2_impl_strong; [|eassumption].
            intros c h Hch Hcin Hhin.
            assert (Hcrel : In c.(clause_rel) t.(tbl_rels)).
            { apply Hincl_r. simpl. apply in_flat_map. exists c.
              split; [apply in_app_iff; right; assumption|]. left. reflexivity. }
            assert (Hcvars : incl (vars_of_clause' c) t.(tbl_vars)).
            { intros v Hv. apply Hincl_v. simpl. apply in_flat_map. exists c.
              split; [apply in_app_iff; right; assumption|]. exact Hv. }
            assert (Hhrel : In (rel_of h) t.(tbl_rels)).
            { rewrite Forall_forall in Hin_hyps. apply Hin_hyps. assumption. }
            apply (proj1 (interp_clause_nattify t ctx ctxn c h
                            Hcorresp Hnd_r Hcrel Hcvars Hhrel)).
            exact Hch.
        + (* agg_rule_impl *)
          simpl.
          assert (Heq : map (nattify_fact t)
                          (map (fun '(i, x_i) =>
                                  normal_fact hyp_rel (i :: x_i :: args0)) vals)
                      = map (fun '(i, x_i) =>
                               normal_fact (encode_rel t hyp_rel) (i :: x_i :: args0))
                            vals).
          { rewrite map_map. apply map_ext. intros [i x_i]. reflexivity. }
          rewrite Heq. apply agg_rule_impl. assumption.
      - (* bwd *)
        intros H.
        destruct r as [concls hyps_c|concls hyps_c|cr ag hr].
        + (* normal_rule *)
          simpl in H. inversion H as [concls' hyps_c' ctxn R' args' hyps' HEx HFa|];
            subst; clear H.
          set (ctx0 := untranslate_ctx t ctxn).
          pose proof (untranslate_ctx_corresp t ctxn Hnd_v) as Hcorresp.
          eapply normal_rule_impl with (ctx := ctx0).
          * apply Exists_exists in HEx. fwd. apply in_map_iff in HExp0. fwd.
            apply Exists_exists. exists x0. split; [assumption|].
            assert (Hcrel : In x0.(clause_rel) t.(tbl_rels)).
            { apply Hincl_r. simpl. apply in_flat_map. exists x0.
              split; [apply in_app_iff; left; assumption|]. left. reflexivity. }
            assert (Hcvars : incl (vars_of_clause' x0) t.(tbl_vars)).
            { intros v Hv. apply Hincl_v. simpl. apply in_flat_map. exists x0.
              split; [apply in_app_iff; left; assumption|]. exact Hv. }
            apply (proj2 (interp_clause_nattify t ctx0 ctxn x0 (normal_fact R args)
                            Hcorresp Hnd_r Hcrel Hcvars Hin_R)).
            exact HExp1.
          * rewrite <- Forall2_map_l in HFa. rewrite <- Forall2_map_r in HFa.
            eapply Forall2_impl_strong; [|eassumption].
            intros c h Hch Hcin Hhin.
            assert (Hcrel : In c.(clause_rel) t.(tbl_rels)).
            { apply Hincl_r. simpl. apply in_flat_map. exists c.
              split; [apply in_app_iff; right; assumption|]. left. reflexivity. }
            assert (Hcvars : incl (vars_of_clause' c) t.(tbl_vars)).
            { intros v Hv. apply Hincl_v. simpl. apply in_flat_map. exists c.
              split; [apply in_app_iff; right; assumption|]. exact Hv. }
            assert (Hhrel : In (rel_of h) t.(tbl_rels)).
            { rewrite Forall_forall in Hin_hyps. apply Hin_hyps. assumption. }
            apply (proj2 (interp_clause_nattify t ctx0 ctxn c h
                            Hcorresp Hnd_r Hcrel Hcvars Hhrel)).
            exact Hch.
        + (* meta_rule: non_meta_rule_impl is false on meta_rule *)
          simpl in H. inversion H.
        + (* agg_rule *)
          simpl in H.
          inversion H as [|S0 vals0 cr_n ag_n hr_n args0 Hisls Hreq Hreqq Hargsq Hhypsq];
            subst.
          (* Hreq: cr_n = encode_rel t cr (from rule match)
             Actually inversion substitutes things. Let me check what survives. *)
          assert (Hcr_in : In cr t.(tbl_rels)).
          { apply Hincl_r. simpl. left. reflexivity. }
          assert (Hhr_in : In hr t.(tbl_rels)).
          { apply Hincl_r. simpl. right. left. reflexivity. }
          assert (HR_eq : R = cr).
          { eapply find_index_inj; eauto. }
          subst R.
          (* Now Hhypsq says map nattify hyps = meta_fact (encode_rel t hr) ... S0 :: map ... vals0 *)
          destruct hyps as [|h0 hyps_rest]; [simpl in Hhypsq; discriminate|].
          simpl in Hhypsq. injection Hhypsq as Hh0 Hrest.
          inversion Hin_hyps as [|? ? Hh0_in Hrest_in]; subst.
          assert (Hh0_eq : h0 = meta_fact hr (None :: None :: map Some args0) S0).
          { destruct h0 as [Rh0 argsh0|Rh0 mfargsh0 mfseth0];
              [discriminate|].
            simpl in Hh0, Hh0_in.
            injection Hh0 as Hr_eq <- <-.
            assert (Rh0 = hr).
            { eapply find_index_inj; eauto. }
            subst Rh0. reflexivity. }
          subst h0.
          assert (Hrest_eq : hyps_rest =
                              map (fun '(i, x_i) => normal_fact hr (i :: x_i :: args0))
                                  vals0).
          { eapply map_nattify_eq_normal_facts; eauto. }
          subst hyps_rest.
          apply agg_rule_impl. assumption.
    Qed.

    Lemma extensionally_equal_nattify
      (t : nattify_tables) (f1 f2 : fact rel T) :
      NoDup t.(tbl_rels) ->
      In (rel_of f1) t.(tbl_rels) ->
      In (rel_of f2) t.(tbl_rels) ->
      (extensionally_equal f1 f2 <->
       extensionally_equal (nattify_fact t f1) (nattify_fact t f2)).
    Proof.
      intros Hnd H1 H2.
      destruct f1 as [R1 args1|R1 args1 S1], f2 as [R2 args2|R2 args2 S2];
        simpl in *; try reflexivity.
      - split.
        + intros (Heq & Hargs). subst. split; reflexivity.
        + intros (Heq & Hargs). subst args2.
          split; [|reflexivity]. eapply find_index_inj; eauto.
      - split.
        + intros (Heq & Hmargs & Hsets). subst.
          split; [reflexivity|]. split; [reflexivity|assumption].
        + intros (Heq & Hmargs & Hsets). subst args2.
          split; [eapply find_index_inj; eauto|].
          split; [reflexivity|assumption].
    Qed.

    Lemma fact_matches_nattify
      (t : nattify_tables) (nf mf : fact rel T) :
      NoDup t.(tbl_rels) ->
      In (rel_of nf) t.(tbl_rels) ->
      In (rel_of mf) t.(tbl_rels) ->
      (fact_matches nf mf <->
       fact_matches (nattify_fact t nf) (nattify_fact t mf)).
    Proof.
      intros Hnd Hnfr Hmfr.
      cbv [fact_matches]. split.
      - intros (R & nf_args & mf_args & mf_set & Hnf & Hmf & Hmatch & Hset).
        subst nf mf. simpl.
        exists (encode_rel t R), nf_args, mf_args, mf_set.
        split; [reflexivity|]. split; [reflexivity|]. split; assumption.
      - intros (R' & nf_args & mf_args & mf_set & Hnf & Hmf & Hmatch & Hset).
        destruct nf as [Rn argsn|Rn argsn Sn]; [|discriminate].
        destruct mf as [Rm argsm|Rm argsm Sm]; [discriminate|].
        simpl in *.
        injection Hnf as Hnr Hnargs.
        injection Hmf as Hmr Hmargs Hmset.
        subst nf_args mf_args mf_set.
        exists Rn, argsn, argsm, Sm.
        assert (Rn = Rm).
        { eapply find_index_inj; eauto.
          change (encode_rel t Rn = encode_rel t Rm). congruence. }
        subst Rm. split; [reflexivity|]. split; [reflexivity|]. split; assumption.
    Qed.

    Lemma fact_supported_nattify
      (t : nattify_tables) (mhyps : list (fact rel T)) (f : fact rel T) :
      NoDup t.(tbl_rels) ->
      In (rel_of f) t.(tbl_rels) ->
      Forall (fun h => In (rel_of h) t.(tbl_rels)) mhyps ->
      (fact_supported mhyps f <->
       fact_supported (map (nattify_fact t) mhyps) (nattify_fact t f)).
    Proof.
      intros Hnd Hf Hin_hyps.
      cbv [fact_supported].
      split.
      - intros HEx. apply Exists_exists in HEx. fwd.
        apply Exists_exists. exists (nattify_fact t x).
        split; [apply in_map; assumption|].
        rewrite Forall_forall in Hin_hyps. specialize (Hin_hyps _ HExp0).
        destruct HExp1 as [HEq|HMatch].
        + left. apply (proj1 (extensionally_equal_nattify t f x Hnd Hf Hin_hyps)).
          assumption.
        + right. apply (proj1 (fact_matches_nattify t f x Hnd Hf Hin_hyps)).
          assumption.
      - intros HEx. apply Exists_exists in HEx. fwd.
        apply in_map_iff in HExp0. fwd.
        apply Exists_exists. exists x0. split; [assumption|].
        rewrite Forall_forall in Hin_hyps. specialize (Hin_hyps _ HExp0p1).
        destruct HExp1 as [HEq|HMatch].
        + left. apply (proj2 (extensionally_equal_nattify t f x0 Hnd Hf Hin_hyps)).
          assumption.
        + right. apply (proj2 (fact_matches_nattify t f x0 Hnd Hf Hin_hyps)).
          assumption.
    Qed.

    Lemma hyp_rels_incl_rels_of_rule (r : rule rel var fn aggregator) :
      incl (hyp_rels r) (rels_of_rule r).
    Proof.
      destruct r as [concls hyps|concls hyps|cr ag hr]; simpl; intros x Hx.
      - apply in_map_iff in Hx. fwd. apply in_flat_map. exists x0.
        split; [apply in_app_iff; right; assumption|left; reflexivity].
      - apply in_map_iff in Hx. fwd. apply in_flat_map. exists x0.
        split; [apply in_app_iff; right; assumption|left; reflexivity].
      - destruct Hx as [<-|[]]. right. left. reflexivity.
    Qed.

    Lemma rels_of_rule_in_tbl
      (p : list (rule rel var fn aggregator)) (r : rule rel var fn aggregator) :
      In r p ->
      incl (rels_of_rule r) (tables_of_prog p).(tbl_rels).
    Proof.
      intros Hr x Hx. cbv [tables_of_prog tbl_rels].
      apply dedup_In; [exact rel_eqb_spec|].
      cbv [rels_of_prog]. apply in_flat_map. eauto.
    Qed.

    Lemma vars_of_rule_in_tbl
      (p : list (rule rel var fn aggregator)) (r : rule rel var fn aggregator) :
      In r p ->
      incl (vars_of_rule r) (tables_of_prog p).(tbl_vars).
    Proof.
      intros Hr x Hx. cbv [tables_of_prog tbl_vars].
      apply dedup_In; [exact var_eqb_spec|].
      cbv [vars_of_prog]. apply in_flat_map. eauto.
    Qed.

    Lemma hyp_rels_nattify_rule (t : nattify_tables) (r : rule rel var fn aggregator) :
      hyp_rels (nattify_rule t r) = map (encode_rel t) (hyp_rels r).
    Proof.
      destruct r as [concls hyps|concls hyps|cr ag hr];
        cbv [nattify_rule rule_relvarmap hyp_rels]; rewrite ?map_map; auto.
    Qed.

    Lemma one_step_derives_nattify
      (p : list (rule rel var fn aggregator))
      (t := tables_of_prog p)
      (p' := fst (nattify_prog p))
      (mhyps : list (fact rel T)) (R : rel) (args : list T) :
      In R t.(tbl_rels) ->
      Forall (fun h => In (rel_of h) t.(tbl_rels)) mhyps ->
      (one_step_derives p mhyps R args <->
       one_step_derives p' (map (nattify_fact t) mhyps) (encode_rel t R) args).
    Proof.
      intros HinR Hmhyps_in.
      assert (Hnd_r : NoDup t.(tbl_rels)).
      { unfold t. cbv [tables_of_prog tbl_rels].
        apply (dedup_NoDup rel_eqb). }
      assert (Hnd_v : NoDup t.(tbl_vars)).
      { unfold t. cbv [tables_of_prog tbl_vars].
        apply (dedup_NoDup var_eqb). }
      cbv [one_step_derives one_step_derives0].
      split.
      - (* fwd *)
        intros (hyps & HEx & Hsup).
        apply Exists_exists in HEx. destruct HEx as [r [Hrin Hrimpl]].
        assert (Hrels_in : incl (rels_of_rule r) t.(tbl_rels)).
        { apply rels_of_rule_in_tbl. assumption. }
        assert (Hvars_in : incl (vars_of_rule r) t.(tbl_vars)).
        { apply vars_of_rule_in_tbl. assumption. }
        assert (Hhyps_in : Forall (fun h => In (rel_of h) t.(tbl_rels)) hyps).
        { apply non_meta_rule_impl_hyp_relname_in in Hrimpl.
          rewrite Forall_forall in Hrimpl |- *. intros h Hh.
          apply Hrimpl in Hh. apply Hrels_in.
          apply hyp_rels_incl_rels_of_rule. assumption. }
        exists (map (nattify_fact t) hyps). split.
        + apply Exists_exists. exists (nattify_rule t r). split.
          * subst p'. cbv [nattify_prog]. simpl. apply in_map_iff.
            eexists; split; [reflexivity|]. assumption.
          * apply (proj1 (non_meta_rule_impl_nattify t r R args hyps
                            Hnd_r Hnd_v Hrels_in Hvars_in HinR Hhyps_in)).
            exact Hrimpl.
        + rewrite Forall_forall in Hsup, Hhyps_in.
          rewrite Forall_forall. intros h Hh.
          apply in_map_iff in Hh. destruct Hh as [h0 [Heq Hin]].
          subst h.
          apply (proj1 (fact_supported_nattify t mhyps h0 Hnd_r
                          (Hhyps_in _ Hin) Hmhyps_in)).
          apply Hsup. assumption.
      - (* bwd *)
        intros (hyps_nat & HEx & Hsup).
        apply Exists_exists in HEx. destruct HEx as [r' [Hr'in Hr'impl]].
        subst p'. cbv [nattify_prog] in Hr'in. simpl in Hr'in.
        apply in_map_iff in Hr'in. destruct Hr'in as [r [<- Hrin]].
        assert (Hrels_in : incl (rels_of_rule r) t.(tbl_rels))
          by (apply rels_of_rule_in_tbl; assumption).
        assert (Hvars_in : incl (vars_of_rule r) t.(tbl_vars))
          by (apply vars_of_rule_in_tbl; assumption).
        pose proof (non_meta_rule_impl_hyp_relname_in _ _ _ _ Hr'impl) as Hhyps_nat_rels.
        rewrite hyp_rels_nattify_rule in Hhyps_nat_rels.
        assert (Hhyp_in : incl (hyp_rels r) (rels_of_rule r))
          by apply hyp_rels_incl_rels_of_rule.
        set (orig_hyps := map (decode_fact R t) hyps_nat).
        assert (Hdecodable : Forall (fun hn => exists R0, nth_error t.(tbl_rels) (rel_of hn) = Some R0 /\ In R0 t.(tbl_rels)) hyps_nat).
        { rewrite Forall_forall. intros hn Hhn.
          rewrite Forall_forall in Hhyps_nat_rels.
          specialize (Hhyps_nat_rels _ Hhn).
          apply in_map_iff in Hhyps_nat_rels.
          destruct Hhyps_nat_rels as [R0 [HReq HRin]].
          exists R0. split.
          - cbv [encode_rel] in HReq. rewrite <- HReq.
            apply (find_index_In rel_eqb). apply Hrels_in. apply Hhyp_in. assumption.
          - apply Hrels_in. apply Hhyp_in. assumption. }
        assert (Hhyps_in_tbl : Forall (fun h => In (rel_of h) t.(tbl_rels)) orig_hyps).
        { subst orig_hyps. rewrite Forall_forall. intros h Hh.
          apply in_map_iff in Hh. destruct Hh as [hn [<- Hhn_in]].
          rewrite Forall_forall in Hdecodable.
          destruct (Hdecodable _ Hhn_in) as [R0 [Hnth HR0in]].
          apply (fnat_decodable_to_original t R hn R0 Hnd_r Hnth). }
        assert (Hhyps_eq : hyps_nat = map (nattify_fact t) orig_hyps).
        { subst orig_hyps. rewrite map_map.
          assert (Haux : forall ys,
            Forall (fun hn => exists R0, nth_error t.(tbl_rels) (rel_of hn) = Some R0
                                          /\ In R0 t.(tbl_rels)) ys ->
            ys = map (fun x => nattify_fact t (decode_fact R t x)) ys).
          { induction ys as [|hn rest IH]; intros Hdec; simpl; [reflexivity|].
            inversion Hdec; subst.
            destruct H1 as [R0 [Hnth HR0in]].
            f_equal.
            - symmetry. apply (fnat_decodable_to_original t R hn R0 Hnd_r Hnth).
            - apply IH. assumption. }
          apply Haux. assumption. }
        exists orig_hyps. split.
        + apply Exists_exists. exists r. split; [assumption|].
          apply (proj2 (non_meta_rule_impl_nattify t r R args orig_hyps
                          Hnd_r Hnd_v Hrels_in Hvars_in HinR Hhyps_in_tbl)).
          rewrite <- Hhyps_eq. exact Hr'impl.
        + rewrite Forall_forall in Hsup, Hhyps_in_tbl.
          rewrite Forall_forall. intros h Hh.
          subst orig_hyps. apply in_map_iff in Hh.
          destruct Hh as [hn [<- Hhn_in]].
          assert (Hh_in : In (rel_of (decode_fact R t hn)) t.(tbl_rels)).
          { apply Hhyps_in_tbl. apply in_map. assumption. }
          apply (proj2 (fact_supported_nattify t mhyps (decode_fact R t hn)
                          Hnd_r Hh_in Hmhyps_in)).
          rewrite Forall_forall in Hdecodable.
          destruct (Hdecodable _ Hhn_in) as [R0 [Hnth HR0in]].
          replace (nattify_fact t (decode_fact R t hn)) with hn.
          { apply Hsup. assumption. }
          { symmetry. apply (fnat_decodable_to_original t R hn R0 Hnd_r Hnth). }
    Qed.

    Lemma rule_impl_nattify
      (p : list (rule rel var fn aggregator))
      (t := tables_of_prog p)
      (p' := fst (nattify_prog p))
      (r : rule rel var fn aggregator) (f : fact rel T) (hyps : list (fact rel T)) :
      In r p ->
      In (rel_of f) t.(tbl_rels) ->
      Forall (fun h => In (rel_of h) t.(tbl_rels)) hyps ->
      (rule_impl (one_step_derives p) r f hyps <->
       rule_impl (one_step_derives p')
                 (nattify_rule t r) (nattify_fact t f) (map (nattify_fact t) hyps)).
    Proof.
      intros Hrin Hf_in Hhyps_in.
      assert (Hnd_r : NoDup t.(tbl_rels)).
      { unfold t. cbv [tables_of_prog tbl_rels]. apply (dedup_NoDup rel_eqb). }
      assert (Hnd_v : NoDup t.(tbl_vars)).
      { unfold t. cbv [tables_of_prog tbl_vars]. apply (dedup_NoDup var_eqb). }
      assert (Hrels_in : incl (rels_of_rule r) t.(tbl_rels))
        by (apply rels_of_rule_in_tbl; assumption).
      assert (Hvars_in : incl (vars_of_rule r) t.(tbl_vars))
        by (apply vars_of_rule_in_tbl; assumption).
      split.
      - (* fwd *)
        intros H. invert H.
        + (* simple_rule_impl: f = normal_fact R args *)
          constructor.
          apply (proj1 (non_meta_rule_impl_nattify t r R args hyps
                          Hnd_r Hnd_v Hrels_in Hvars_in Hf_in Hhyps_in)).
          assumption.
        + (* meta_rule_impl *)
          rename ctx into ctx0.
          pose proof (translate_ctx_corresp t ctx0 Hnd_v) as Hcorresp.
          simpl in *.
          eapply meta_rule_impl with (ctx := translate_ctx t ctx0).
          * apply Exists_exists in H0. fwd. apply Exists_exists.
            exists (meta_clause_relvarmap (encode_rel t) (encode_var t) x). split.
            { apply in_map. assumption. }
            { assert (Hcrel : In x.(meta_clause_rel) t.(tbl_rels)).
              { apply Hrels_in. cbv [rels_of_rule].
                apply in_flat_map. exists x.
                split; [apply in_app_iff; left; assumption|]. left. reflexivity. }
              assert (Hcvars : incl (vars_of_meta_clause' x) t.(tbl_vars)).
              { intros v Hv. apply Hvars_in. cbv [vars_of_rule].
                apply in_flat_map. exists x.
                split; [apply in_app_iff; left; assumption|]. exact Hv. }
              apply (proj1 (interp_meta_clause_nattify t ctx0 (translate_ctx t ctx0)
                              x (meta_fact R args (fun args' => S args'))
                              Hcorresp Hnd_r Hcrel Hcvars Hf_in)).
              exact H0p1. }
          * rewrite <- Forall2_map_l. rewrite <- Forall2_map_r.
            eapply Forall2_impl_strong; [|eassumption].
            intros c h Hch Hcin Hhin.
            assert (Hcrel : In c.(meta_clause_rel) t.(tbl_rels)).
            { apply Hrels_in. cbv [rels_of_rule]. apply in_flat_map. exists c.
              split; [apply in_app_iff; right; assumption|]. left. reflexivity. }
            assert (Hcvars : incl (vars_of_meta_clause' c) t.(tbl_vars)).
            { intros v Hv. apply Hvars_in. cbv [vars_of_rule].
              apply in_flat_map. exists c.
              split; [apply in_app_iff; right; assumption|]. exact Hv. }
            assert (Hhrel : In (rel_of h) t.(tbl_rels)).
            { rewrite Forall_forall in Hhyps_in. apply Hhyps_in. assumption. }
            apply (proj1 (interp_meta_clause_nattify t ctx0 (translate_ctx t ctx0)
                            c h Hcorresp Hnd_r Hcrel Hcvars Hhrel)).
            exact Hch.
          * intros args'' Hmatches.
            rewrite (H2 _ Hmatches).
            apply (one_step_derives_nattify p hyps R args'' Hf_in Hhyps_in).
      - (* bwd *)
        intros H.
        destruct r as [concls hyps_c|concls hyps_c|cr ag hr];
          destruct f as [Rf argsf|Rf argsf Sf]; simpl in H.
        + (* normal_rule + normal_fact *)
          inversion H; clear H; subst.
          match goal with H : non_meta_rule_impl _ _ _ _ |- _ =>
            constructor;
            apply (proj2 (non_meta_rule_impl_nattify t (normal_rule concls hyps_c)
                          Rf argsf hyps Hnd_r Hnd_v Hrels_in Hvars_in Hf_in Hhyps_in));
            exact H
          end.
        + (* normal_rule + meta_fact: impossible *)
          inversion H.
        + (* meta_rule + normal_fact: impossible *)
          inversion H; clear H; subst.
          match goal with H : non_meta_rule_impl _ _ _ _ |- _ => inversion H end.
        + (* meta_rule + meta_fact *)
          inversion H as [|? ? ctxn ? ? ? ? HEx HFa Hxor]; clear H; subst.
          pose proof (untranslate_ctx_corresp t ctxn Hnd_v) as Hcorresp.
          eapply meta_rule_impl with (ctx := untranslate_ctx t ctxn).
          * apply Exists_exists. apply Exists_exists in HEx. fwd.
            apply in_map_iff in HExp0. fwd.
            exists x0. split; [assumption|].
            assert (Hcrel : In x0.(meta_clause_rel) t.(tbl_rels)).
            { apply Hrels_in. cbv [rels_of_rule]. apply in_flat_map.
              exists x0. split; [apply in_app_iff; left; assumption|].
              left. reflexivity. }
            assert (Hcvars : incl (vars_of_meta_clause' x0) t.(tbl_vars)).
            { intros v Hv. apply Hvars_in. cbv [vars_of_rule].
              apply in_flat_map. exists x0.
              split; [apply in_app_iff; left; assumption|]. exact Hv. }
            apply (proj2 (interp_meta_clause_nattify
                            t (untranslate_ctx t ctxn) ctxn x0
                            (meta_fact Rf argsf Sf)
                            Hcorresp Hnd_r Hcrel Hcvars Hf_in)).
            exact HExp1.
          * rewrite <- Forall2_map_l in HFa. rewrite <- Forall2_map_r in HFa.
            eapply Forall2_impl_strong; [|eassumption].
            intros c h Hch Hcin Hhin.
            assert (Hcrel : In c.(meta_clause_rel) t.(tbl_rels)).
            { apply Hrels_in. cbv [rels_of_rule]. apply in_flat_map.
              exists c. split; [apply in_app_iff; right; assumption|].
              left. reflexivity. }
            assert (Hcvars : incl (vars_of_meta_clause' c) t.(tbl_vars)).
            { intros v Hv. apply Hvars_in. cbv [vars_of_rule].
              apply in_flat_map. exists c.
              split; [apply in_app_iff; right; assumption|]. exact Hv. }
            assert (Hhrel : In (rel_of h) t.(tbl_rels)).
            { rewrite Forall_forall in Hhyps_in. apply Hhyps_in. assumption. }
            apply (proj2 (interp_meta_clause_nattify
                            t (untranslate_ctx t ctxn) ctxn c h
                            Hcorresp Hnd_r Hcrel Hcvars Hhrel)).
            exact Hch.
          * intros args'' Hmatches.
            rewrite (Hxor _ Hmatches).
            symmetry.
            apply (one_step_derives_nattify p hyps Rf args'' Hf_in Hhyps_in).
        + (* agg_rule + normal_fact *)
          inversion H; clear H; subst.
          match goal with H : non_meta_rule_impl _ _ _ _ |- _ =>
            constructor;
            apply (proj2 (non_meta_rule_impl_nattify t (agg_rule cr ag hr)
                          Rf argsf hyps Hnd_r Hnd_v Hrels_in Hvars_in Hf_in Hhyps_in));
            exact H
          end.
        + (* agg_rule + meta_fact: impossible *)
          inversion H.
    Qed.

    (* --- Main correctness theorem --- *)

    Lemma concl_rels_in_rels_of_rule (r : rule rel var fn aggregator) :
      incl (concl_rels r) (rels_of_rule r).
    Proof.
      destruct r as [concls hyps|concls hyps|cr ag hr]; simpl; intros x Hx.
      - apply in_flat_map. apply in_map_iff in Hx. fwd.
        eexists. split; [apply in_app_iff; left; eassumption|].
        cbv [rels_of_clause]. left. reflexivity.
      - apply in_flat_map. apply in_map_iff in Hx. fwd.
        eexists. split; [apply in_app_iff; left; eassumption|].
        cbv [rels_of_meta_clause]. left. reflexivity.
      - simpl in Hx. destruct Hx as [<-|[]]. left. reflexivity.
    Qed.

    Lemma prog_impl_rel_in_table
      (p : list (rule rel var fn aggregator))
      (Q : fact rel T -> Prop) (f : fact rel T) :
      let t := tables_of_prog p in
      (forall f0, Q f0 -> In (rel_of f0) t.(tbl_rels)) ->
      prog_impl p Q f ->
      In (rel_of f) t.(tbl_rels).
    Proof.
      intros t HQ Hprog. revert f Hprog.
      apply (prog_impl_ind p Q (fun f => In (rel_of f) t.(tbl_rels))).
      - intros f0. apply HQ.
      - intros f0 hyps Hex _ _.
        apply Exists_exists in Hex. destruct Hex as [r [Hrin Hrimpl]].
        apply rule_impl_concl_relname_in in Hrimpl.
        apply concl_rels_in_rels_of_rule in Hrimpl.
        subst t. cbv [tables_of_prog tbl_rels].
        apply dedup_In; [exact rel_eqb_spec|].
        cbv [rels_of_prog]. apply in_flat_map. eauto.
    Qed.

    Theorem nattify_prog_correct
      (p : list (rule rel var fn aggregator))
      (Q : fact rel T -> Prop)
      (f : fact rel T) :
      let t  := tables_of_prog p in
      let p' := fst (nattify_prog p) in
      In (rel_of f) t.(tbl_rels) ->
      (forall f0, Q f0 -> In (rel_of f0) t.(tbl_rels)) ->
      (prog_impl p Q f <->
       prog_impl p'
         (fun fnat => exists f0, fnat = nattify_fact t f0 /\ Q f0)
         (nattify_fact t f)).
    Proof.
      intros t p' Hf_in HQ_supp.
      split.
      - (* forward *)
        intros Hprog. clear Hf_in. revert f Hprog.
        apply (prog_impl_ind p Q
                 (fun f => prog_impl p'
                   (fun fnat => exists f0, fnat = nattify_fact t f0 /\ Q f0)
                   (nattify_fact t f))).
        + intros f0 HQ. apply prog_impl_leaf.
          eexists. split; [reflexivity|]. assumption.
        + intros f0 hyps Hex HFprog HForall_R.
          eapply prog_impl_step.
          * apply Exists_exists in Hex. destruct Hex as [r [Hrin Hrimpl]].
            assert (Hin_f : In (rel_of f0) t.(tbl_rels)).
            { apply rule_impl_concl_relname_in in Hrimpl.
              apply concl_rels_in_rels_of_rule in Hrimpl.
              subst t. cbv [tables_of_prog tbl_rels].
              apply dedup_In; [exact rel_eqb_spec|].
              cbv [rels_of_prog]. apply in_flat_map. eauto. }
            assert (Hin_hyps : Forall (fun h => In (rel_of h) t.(tbl_rels)) hyps).
            { rewrite Forall_forall in HFprog |- *. intros h Hh.
              eapply prog_impl_rel_in_table; eauto. }
            apply Exists_exists. exists (nattify_rule t r). split.
            { subst p'. cbv [nattify_prog]. simpl.
              apply in_map_iff. eexists. split; [reflexivity|]. assumption. }
            { apply (proj1 (rule_impl_nattify p r f0 hyps Hrin Hin_f Hin_hyps)).
              exact Hrimpl. }
          * apply Forall_map. assumption.
      - (* backward *)
        intros Hprog.
        assert (Hnd_r : NoDup t.(tbl_rels)).
        { unfold t. cbv [tables_of_prog tbl_rels]. apply (dedup_NoDup rel_eqb). }
        assert (Hgen :
          forall fnat,
            prog_impl p'
              (fun fnat0 => exists f1, fnat0 = nattify_fact t f1 /\ Q f1) fnat ->
            forall f0,
              fnat = nattify_fact t f0 ->
              In (rel_of f0) t.(tbl_rels) ->
              prog_impl p Q f0).
        { intros fnat Hp. revert fnat Hp.
          apply (prog_impl_ind p'
                   (fun fnat => exists f1, fnat = nattify_fact t f1 /\ Q f1)
                   (fun fnat =>
                      forall f0, fnat = nattify_fact t f0 ->
                              In (rel_of f0) t.(tbl_rels) ->
                              prog_impl p Q f0)).
          - (* base *)
            intros f1 HQnat f0 Heqf Hf0_in.
            destruct HQnat as [f2 [Hf2eq HQ2]].
            assert (Hf2_in : In (rel_of f2) t.(tbl_rels)) by (apply HQ_supp; assumption).
            assert (f0 = f2).
            { apply (nattify_fact_inj t f0 f2 Hnd_r Hf0_in Hf2_in). congruence. }
            subst f2. apply prog_impl_leaf. assumption.
          - (* step *)
            intros f1 hyps_nat HEx HFprog HFR f0 Heqf Hf0_in.
            apply Exists_exists in HEx. destruct HEx as [r' [Hr'in Hr'impl]].
            subst p'. cbv [nattify_prog] in Hr'in. simpl in Hr'in.
            apply in_map_iff in Hr'in. destruct Hr'in as [r [<- Hrin]].
            apply rule_impl_hyp_relname_in in Hr'impl as Hhyps_nat_rels.
            rewrite hyp_rels_nattify_rule in Hhyps_nat_rels.
            pose proof (hyp_rels_incl_rels_of_rule r) as Hhyp_in.
            pose proof (rels_of_rule_in_tbl p r Hrin) as Hrels_in.
            assert (Hdecodable :
              Forall (fun hn => exists R0,
                  nth_error t.(tbl_rels) (rel_of hn) = Some R0 /\
                  In R0 t.(tbl_rels)) hyps_nat).
            { rewrite Forall_forall. intros hn Hh.
              rewrite Forall_forall in Hhyps_nat_rels.
              specialize (Hhyps_nat_rels _ Hh).
              apply in_map_iff in Hhyps_nat_rels.
              destruct Hhyps_nat_rels as [R0 [HReq HRin]].
              exists R0. split.
              - cbv [encode_rel] in HReq. rewrite <- HReq.
                apply (find_index_In rel_eqb).
                apply Hrels_in. apply Hhyp_in. assumption.
              - apply Hrels_in. apply Hhyp_in. assumption. }
            set (orig_hyps := map (decode_fact (rel_of f0) t) hyps_nat).
            assert (Hhyps_in_tbl :
                      Forall (fun h => In (rel_of h) t.(tbl_rels)) orig_hyps).
            { subst orig_hyps. rewrite Forall_forall. intros h Hh.
              apply in_map_iff in Hh. destruct Hh as [hn [<- Hhn_in]].
              rewrite Forall_forall in Hdecodable.
              destruct (Hdecodable _ Hhn_in) as [R0 [Hnth HR0in]].
              apply (fnat_decodable_to_original t (rel_of f0) hn R0 Hnd_r Hnth). }
            assert (Hhyps_eq : hyps_nat = map (nattify_fact t) orig_hyps).
            { subst orig_hyps. rewrite map_map.
              assert (Haux : forall ys,
                Forall (fun hn => exists R0,
                          nth_error t.(tbl_rels) (rel_of hn) = Some R0 /\
                          In R0 t.(tbl_rels)) ys ->
                ys = map (fun x => nattify_fact t (decode_fact (rel_of f0) t x)) ys).
              { induction ys as [|hn rest IH]; intros Hdec; simpl; [reflexivity|].
                inversion Hdec; subst.
                destruct H1 as [R0 [Hnth HR0in]].
                f_equal.
                - symmetry.
                  apply (fnat_decodable_to_original t (rel_of f0) hn R0 Hnd_r Hnth).
                - apply IH. assumption. }
              apply Haux. assumption. }
            eapply prog_impl_step.
            + apply Exists_exists. exists r. split; [assumption|].
              apply (proj2 (rule_impl_nattify p r f0 orig_hyps Hrin Hf0_in Hhyps_in_tbl)).
              subst f1.
              change (tables_of_prog p) with t.
              rewrite <- Hhyps_eq. exact Hr'impl.
            + apply Forall_forall. intros h Hh.
              subst orig_hyps. apply in_map_iff in Hh.
              destruct Hh as [hn [<- Hhn_in]].
              rewrite Forall_forall in HFR.
              specialize (HFR _ Hhn_in).
              apply HFR.
              * rewrite Forall_forall in Hdecodable.
                destruct (Hdecodable _ Hhn_in) as [R0 [Hnth HR0in]].
                symmetry.
                apply (fnat_decodable_to_original t (rel_of f0) hn R0 Hnd_r Hnth).
              * rewrite Forall_forall in Hhyps_in_tbl.
                apply Hhyps_in_tbl. apply in_map. assumption. }
        eapply Hgen; [exact Hprog|reflexivity|exact Hf_in].
    Qed.

  End Correctness.

End Nattify.
