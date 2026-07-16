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

Section eqb_option.
  Context {A : Type}.
  Context {eqbA : Eqb A} {eqbA_ok : Eqb_ok eqbA}.

  #[global] Instance eqb_option : Eqb (option A) :=
    fun x y => match x, y with
               | Some a, Some b => eqb a b
               | None, None => true
               | _, _ => false
               end.

  #[global] Instance eqb_option_ok : Eqb_ok eqb_option.
  Proof.
    intros [a|] [b|]; cbv [eqb eqb_option]; simpl; try congruence.
    pose proof (eqb_spec a b) as H. cbv [eqb] in *.
    destruct (eqbA a b); simpl in H |- *; congruence.
  Qed.
End eqb_option.

Lemma eqb_sym {A} {f : Eqb A} {Hok : Eqb_ok f} (a b : A) : eqb a b = eqb b a.
Proof.
  pose proof (eqb_spec a b) as Hab. pose proof (eqb_spec b a) as Hba.
  destruct (eqb a b), (eqb b a); congruence.
Qed.

Lemma eqb_map_inj {A B} {fa : Eqb A} {fa_ok : Eqb_ok fa} {fb : Eqb B} {fb_ok : Eqb_ok fb}
  (g : A -> B) (Hinj : forall a b, g a = g b -> a = b) (a b : A) :
  eqb (g a) (g b) = eqb a b.
Proof.
  pose proof (eqb_spec (g a) (g b)) as Hg. pose proof (eqb_spec a b) as H.
  destruct (eqb (g a) (g b)), (eqb a b); simpl in Hg, H; try reflexivity.
  - apply Hinj in Hg. contradiction.
  - subst b. contradiction.
Qed.
