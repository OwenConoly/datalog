From Stdlib Require Import Lists.List.

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
