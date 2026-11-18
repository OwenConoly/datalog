From Stdlib Require Import Eqdep_dec.
From coqutil Require Import Eqb.

Definition fun_put {A B} {eqbA : Eqb A} (f : A -> B) (a : A) (b : B) : A -> B :=
  fun x => if eqb x a then b else f x.

Definition dfun_put {A} {B : A -> Type} {eqbA : Eqb A} {eqbA_ok : Eqb_ok eqbA}
  (f : forall a, B a) (a : A) (b : B a) : forall x, B x :=
  fun x =>
    match eqb x a as e return (if e then x = a else x <> a) -> B x with
    | true => fun H => eq_rect_r B b H
    | false => fun _ => f x
    end (eqb_spec x a).

Lemma dfun_put_same {A} {B : A -> Type} {eqbA : Eqb A} {eqbA_ok : Eqb_ok eqbA}
  (f : forall a, B a) a b :
  dfun_put f a b a = b.
Proof.
  cbv [dfun_put]. generalize (eqb_spec a a). destruct (eqb a a); intros H; [ | congruence ].
  unshelve erewrite (eq_proofs_unicity _ H eq_refl).
  - intros x y. generalize (eqb_spec x y). destruct (eqb x y); auto.
  - reflexivity.
Qed.

Lemma dfun_put_diff {A} {B : A -> Type} {eqbA : Eqb A} {eqbA_ok : Eqb_ok eqbA}
  (f : forall a, B a) a b x :
  x <> a ->
  dfun_put f a b x = f x.
Proof.
  intros Hx. cbv [dfun_put]. generalize (eqb_spec x a).
  destruct (eqb x a); intros H; [ congruence | reflexivity ].
Qed.
