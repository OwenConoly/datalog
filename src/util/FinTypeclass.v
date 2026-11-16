From Stdlib Require Import List Finite.
From coqutil Require Import Eqb Tactics.
From Datalog Require Import Function.

Module Fin.
  Class Fin A := {
      all : list A;
      all_NoDup : NoDup all;
      all_Full : Full all;
    }.
  Arguments all A {_}.

  Section __.
    Context {A} {A_fin : Fin A}.

    Lemma all_Listing : Listing (all A).
    Proof. split; [ apply all_NoDup | apply all_Full ]. Qed.

    Lemma Forall_all (P : A -> Prop) : Forall P (all A) <-> forall x, P x.
    Proof.
      rewrite Forall_forall. split.
      - intros H x. apply H, all_Full.
      - auto.
    Qed.

    Context {A_eqb : Eqb A} {A_eqb_ok : Eqb_ok A_eqb}.

    Lemma choice {B} (P : A -> B -> Prop) :
      (forall x, exists y, P x y) ->
      exists f, forall x, P x (f x).
    Proof.
      intros H. destruct (all A) as [|a l] eqn:Hall.
      - assert (Hempty : A -> False).
        { intros x. pose proof (all_Full x) as Hx. rewrite Hall in Hx. destruct Hx. }
        exists (fun x => False_rect B (Hempty x)). intros x. destruct (Hempty x).
      - destruct (H a) as [y0 _].
        enough (Hl : forall l, exists f, forall x, In x l -> P x (f x)).
        { destruct (Hl (all A)) as [f Hf]. exists f. intros x. apply Hf, all_Full. }
        intros l'. induction l' as [|a' l' [f Hf]].
        + exists (fun _ => y0). intros _ [].
        + destruct (H a') as [ya Hya]. exists (fun_put f a' ya). intros x Hx. cbv [fun_put].
          destr (eqb x a'); [ assumption | ].
          apply Hf. destruct Hx; [ congruence | assumption ].
    Qed.
  End __.
End Fin.
