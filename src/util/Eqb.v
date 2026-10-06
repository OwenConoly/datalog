From Stdlib Require Import Bool.
From coqutil Require Import Eqb Decidable Tactics Tactics.fwd.

#[global] Instance Eqb_ok_BoolSpec {A} {f : Eqb A} {Hok : Eqb_ok f} (x y :
A)
  : BoolSpec (x = y) (x <> y) (f x y) := eqb_boolspec A x y.

#[global] Hint Mode Eqb + : typeclass_instances.
#[global] Hint Mode Eqb_ok + - : typeclass_instances.

Ltac eqb_ok :=
  intros a b; destruct a, b; cbv [eqb] in *; simpl in *;
  repeat destruct_one_match; repeat intro; fwd; simpl in *; fwd; try (congruence || tauto).

Scheme Boolean Equality for prod.
Section eqb_prod.
  Context {A B : Type}.
  Context {eqbA : Eqb A} {eqbA_ok : Eqb_ok eqbA}.
  Context {eqbB : Eqb B} {eqbB_ok : Eqb_ok eqbB}.

  #[export] Instance eqb_prod : Eqb (A * B) := prod_beq _ _ eqb eqb.
  #[export] Instance eqb_prod_ok : Eqb_ok eqb_prod.
  Proof. eqb_ok. Qed.
End eqb_prod.

Scheme Boolean Equality for option.
Section eqb_option.
  Context {A : Type}.
  Context {eqbA : Eqb A} {eqbA_ok : Eqb_ok eqbA}.

  #[export] Instance eqb_option : Eqb (option A) := option_beq A eqb.
  #[global] Instance eqb_option_ok : Eqb_ok eqb_option.
  Proof. eqb_ok. Qed.
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

#[export] Register Scheme Nat.eqb as beq for nat.
#[export] Register Scheme Bool.eqb as beq for bool.
