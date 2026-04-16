Section fp.
Context {T : Type} (F : (T -> Prop) -> (T -> Prop)).
Context (F_mono : forall S1 S2, (forall x, S1 x -> S2 x) -> forall x, F S1 x -> F S2 x).
Context (F_inc : forall S x, S x -> F S x).

Definition fp (S : T -> Prop) : Prop :=
  forall x, F S x -> S x.

Definition lfp : T -> Prop :=
  fun x => forall S, fp S -> S x.

(*the least fixed point is a fixed point*)
Lemma fp_lfp : fp lfp.
Proof.
  cbv [fp lfp]. intros.
  apply H0. eapply F_mono; [|exact H]. simpl. intros. apply H1. auto.
Qed.
End fp.

Definition equiv {T : Type} (P Q : T -> Prop) := forall x, P x <-> Q x.

Section fps.
  Context {T U : Type} (F : (T -> Prop) -> (T -> Prop)) (G : (U -> Prop) -> (U -> Prop)).
  Context (f : (T -> Prop) -> (U -> Prop)) (g : (U -> Prop) -> (T -> Prop)).
  (* Context (f_mono : forall S1 S2, (forall x, S1 x -> S2 x) -> forall x, f S1 x -> f S2 x). *)
  (*note: g_mono can be weakened*)
  Context (g_mono_ish : forall S1 S2, (forall x, S1 x -> S2 x) -> forall x, g S1 x -> g S2 x).
  Context (f_fp : fp G (f (lfp F))) (g_fp : fp F (g (lfp G))).
  
  (*Helps to find lfp of G given lfp of F: the lfp of G is a preimage (via g) of the lfp of F*)
  Lemma lfp_preimage' :
    equiv (lfp F) (g (f (lfp F))) ->
    equiv (g (lfp G)) (lfp F).
  Proof.
    cbv [equiv]. intros H x. split; intros Hx.
    - apply H. eapply g_mono_ish; [|eassumption]. intros ? Hlfp. apply Hlfp. apply f_fp.
    - apply Hx. apply g_fp.
  Qed.

  Lemma lfp_preimage :
    (forall S, equiv S (g (f S))) ->
    equiv (g (lfp G)) (lfp F).
  Proof.
    cbv [equiv]. intros H x. split; intros Hx.
    - apply H. eapply g_mono_ish; [|eassumption]. intros ? Hlfp. apply Hlfp. apply f_fp.
    - apply Hx. apply g_fp.
  Qed.
End fps.    
