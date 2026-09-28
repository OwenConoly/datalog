From Stdlib Require Import Relations.Relation_Operators Relations.Operators_Properties.

Notation "R ^*" := (clos_refl_trans_1n _ R) (format "R ^*").
#[export] Hint Constructors clos_refl_trans_1n : core.

Lemma crt1n_trans_compose {A R} (x y z : A) :
  clos_refl_trans_1n A R x y ->
  clos_refl_trans_1n A R y z ->
  clos_refl_trans_1n A R x z.
Proof.
  intros H1 H2.
  eapply Operators_Properties.clos_rt1n_rt in H1.
  eapply Operators_Properties.clos_rt1n_rt in H2.
  eapply Operators_Properties.clos_rt_rt1n.
  eapply Relation_Operators.rt_trans; eassumption.
Qed.
