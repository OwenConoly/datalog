From Stdlib Require Import Bool.
From coqutil Require Import Eqb Decidable.

#[global] Instance Eqb_ok_BoolSpec {A} {f : Eqb A} {Hok : Eqb_ok f} (x y :
A)
  : BoolSpec (x = y) (x <> y) (f x y) := eqb_boolspec A x y.


Section eqb_prod.
  Context {A B : Type}.
  Context {eqbA : Eqb A} {eqbA_ok : Eqb_ok eqbA}.
  Context {eqbB : Eqb B} {eqbB_ok : Eqb_ok eqbB}.

  #[global] Instance eqb_prod : Eqb (A * B) :=
    fun x y => (eqbA (fst x) (fst y) && eqbB (snd x) (snd y))%bool.

  #[global] Instance eqb_prod_ok : Eqb_ok eqb_prod.
  Proof.
    intros [a1 b1] [a2 b2]. cbv [eqb eqb_prod]. simpl.
    pose proof (eqb_spec a1 a2) as HA. pose proof (eqb_spec b1 b2) as HB.
    cbv [eqb] in *.
    destruct (eqbA a1 a2), (eqbB b1 b2); subst; simpl; try congruence.
  Qed.
End eqb_prod.

Lemma eqb_sym {A} {f : Eqb A} {Hok : Eqb_ok f} (a b : A) : eqb a b = eqb b a.
Proof.
  pose proof (eqb_spec a b) as Hab. pose proof (eqb_spec b a) as Hba.
  destruct (eqb a b), (eqb b a); congruence.
Qed.
