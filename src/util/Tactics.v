From Stdlib Require Import Lists.List.
From Stdlib Require Import Eqdep.

Ltac specialize' H :=
  let hyp := fresh "hyp" in
  eassert _ as hyp;
  [clear H|specialize (H hyp); clear hyp].

Ltac epose_dep H :=
  repeat lazymatch type of H with
  | ?A -> ?B => fail
  | forall _, _ => epose proof (H _) as H
  end.

Ltac apply_somewhere H :=
  match goal with
  | H' : _ |- _ => apply H in H'
  end.

Ltac invert' H := inversion H; clear H; subst.

Ltac invertN n :=
  match goal with
    | [ |- forall x : ?E, _ ] =>
      match type of E with
        | Prop =>
          let H := fresh in intro H;
            match n with
              | 1 => invert' H
              | S ?n' => invertN n'
            end
        | _ => intro; invertN n
      end
  end.

Ltac invert e := invertN e || invert' e.

Ltac invert0 H := invert H; fail.
Ltac invert1 H := invert H; [].

Ltac dep_invert H :=
  invert H;
  repeat match goal with
    | H: existT _ _ _ = existT _ _ _ |- _ => apply Eqdep.EqdepTheory.inj_pair2 in H
    end;
  subst.

Hint Unfold iff : core.
Hint Extern 6 => match goal with
                | H: forall x, _ <-> _ |- _ => apply H
                | H: _ <-> _ |- _ => apply H
                end : core.
Hint Extern 7 (_ <-> _) => split : core.

From coqutil Require Import Tactics.

Ltac destr_sth x :=
  match goal with
  | H: context[x ?a ?b] |- _ => destr (x a b)
  | |- context[x ?a ?b] => destr (x a b)
  end.
