(*worth comparing to https://compcert.org/doc/html/compcert.common.Smallstep.html*)
From Stdlib Require Import List Permutation RelationClasses.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
From coqutil Require Import Tactics.fwd.
From Datalog Require Import Tactics.
Import ListNotations.

Section star.
  Context {state event : Type} (trace := list event)
          (step : state -> event -> state -> Prop).
  Inductive star (s : state) : trace -> state -> Prop :=
  | star_refl :
    star s [] s
  | star_step t0 s' e s'' :
    star s t0 s' ->
    step s' e s'' ->
    star s (e :: t0) s''.

  Lemma star_one s e s' : step s e s' -> star s [e] s'.
  Proof. intros. eapply star_step; [apply star_refl | eassumption]. Qed.

  Lemma star_app s1 t1 s2 t2 s3 :
    star s1 t1 s2 -> star s2 t2 s3 -> star s1 (t2 ++ t1) s3.
  Proof.
    intros H1 H2. induction H2 as [ | t0 s' e s'' Hstar IH Hstep]; cbn.
    - exact H1.
    - eapply star_step; [exact IH | exact Hstep].
  Qed.
End star.

Section io.
  Context {label message : Type}.

  Variant IO_event : Type :=
    | I_event : message -> IO_event
    | O_event : label -> list message -> IO_event.

  Definition inputs_of (t : list IO_event) :=
    flat_map (fun e => match e with I_event m => [m] | _ => [] end) t.

  Definition outputs_of (t : list IO_event) :=
    flat_map (fun e => match e with O_event _ outs => outs | _ => [] end) t.

  Lemma inputs_of_map_I_event (l : list message) :
    inputs_of (map I_event l) = l.
  Proof.
    unfold inputs_of.
    induction l as [|m l IH]; [reflexivity|].
    cbn. rewrite IH. reflexivity.
  Qed.
End io.

Arguments IO_event : clear implicits.

Section step.
  Context {state label message : Type}.
  Context (step : state -> IO_event label message -> state -> Prop).
  Context (equiv : message -> message -> Prop).
  Context (equiv_equiv : Equivalence equiv).
  Context (consistent : list message (*a set*) -> list message (*a multiset*) -> Prop).

  Definition submultiset (l1 l2 : list message) : Prop :=
    exists rest, Permutation l2 (l1 ++ rest).

  Context (allowed : list message -> Prop).
  Context (allowed_submultiset :
            forall l1 l2, submultiset l1 l2 -> allowed l2 -> allowed l1).
  (* "allowed" should satisfy the allowed_submultiset definition.
     if we have some consistent sets which are not allowed, then they are not good
     for anything, so we can just set consistent := consistent /\ allowed.
     so, wlog, allowed is closed under submultiset, and it is a superset of consistent.
     this yields the following:
   *)
  (* Definition allowed ms := exists ms', consistent ms' /\ submultiset ms' ms. *)
  (*but oops that doesn't typecheck; that's not how consistent works.
    hmm.*)

  Definition consistent_monotone :=
    forall c l1 l2,
      allowed l1 ->
      allowed l2 ->
      submultiset l1 l2 ->
      consistent c l1 ->
      consistent c l2.

  Context (Hcm : consistent_monotone).

  Lemma submultiset_refl l : submultiset l l.
  Proof. exists []. rewrite app_nil_r. apply Permutation_refl. Qed.

  Lemma outputs_of_perm (t1 t2 : list (IO_event label message)) :
    Permutation t1 t2 -> Permutation (outputs_of t1) (outputs_of t2).
  Proof.
    unfold outputs_of. induction 1; cbn [flat_map].
    - apply Permutation_refl.
    - apply Permutation_app_head; assumption.
    - rewrite 2!app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
    - eapply perm_trans; eassumption.
  Qed.

  Lemma outputs_of_app (t1 t2 : list (IO_event label message)) :
    outputs_of (t1 ++ t2) = outputs_of t1 ++ outputs_of t2.
  Proof. apply flat_map_app. Qed.

  Lemma outputs_of_in_perm o (t1 t2 : list (IO_event label message)) :
    Permutation t1 t2 -> In o (outputs_of t1) -> In o (outputs_of t2).
  Proof.
    intros Hperm Hin. eapply Permutation_in; [apply outputs_of_perm; exact Hperm | exact Hin].
  Qed.

  Lemma inputs_of_perm (t1 t2 : list (IO_event label message)) :
    Permutation t1 t2 -> Permutation (inputs_of t1) (inputs_of t2).
  Proof.
    unfold inputs_of. induction 1; cbn [flat_map].
    - apply Permutation_refl.
    - apply Permutation_app_head; assumption.
    - rewrite 2!app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
    - eapply perm_trans; eassumption.
  Qed.

  Lemma inputs_of_app (t1 t2 : list (IO_event label message)) :
    inputs_of (t1 ++ t2) = inputs_of t1 ++ inputs_of t2.
  Proof. apply flat_map_app. Qed.

  Lemma outputs_of_in_app o (l1 l2 : list (IO_event label message)) :
    In o (outputs_of (l1 ++ l2)) <-> In o (outputs_of l1) \/ In o (outputs_of l2).
  Proof. rewrite outputs_of_app. apply in_app_iff. Qed.

  Lemma outputs_of_in_swap o l1 e (l2 : list (IO_event label message)) :
    In o (outputs_of (l1 ++ e :: l2)) <-> In o (outputs_of (e :: l1 ++ l2)).
  Proof.
    split.
    - apply outputs_of_in_perm. apply Permutation_sym. apply Permutation_middle.
    - apply outputs_of_in_perm. apply Permutation_middle.
  Qed.

  Definition input_total :=
    forall s m, exists s', step s (I_event m) s'.

  Lemma star_recv :
    input_total ->
    forall (inputs : list message) (s : state),
      exists tr s', star step s tr s' /\ inputs_of tr = inputs.
  Proof.
    intros Htotal.
    induction inputs as [|m inputs IH]; intros s.
    - exists [], s. split; [constructor|reflexivity].
    - destruct (IH s) as (tr & s_mid & Hstar & Hinp).
      destruct (Htotal s_mid m) as (s' & Hstep).
      exists (I_event m :: tr), s'. split.
      + eapply star_step; [exact Hstar | exact Hstep].
      + cbn. f_equal. exact Hinp.
  Qed.

  Lemma star_recv_map :
    input_total ->
    forall (inputs : list message) (s : state),
      exists s', star step s (map I_event inputs) s'.
  Proof.
    intros Htotal.
    induction inputs as [|m inputs IH]; intros s.
    - exists s. constructor.
    - destruct (IH s) as (s_mid & Hstar).
      destruct (Htotal s_mid m) as (s' & Hstep).
      exists s'. cbn. eapply star_step; [exact Hstar | exact Hstep].
  Qed.

  (*some fairness condition: we can eventually take the step that we want.*)
  Definition will_step '(s, t) (P : state * list (IO_event label message) -> Prop) : Prop :=
    exists lbl,
    forall s' t',
      star step s t' s' ->
      allowed (inputs_of (t' ++ t)) ->
      P (s', t' ++ t) \/
        exists s'' outs,
          step s' (O_event lbl outs) s'' /\
            P (s'', O_event lbl outs :: t' ++ t).

  (*this is not used anywhere, but without it will_step is a bit weird, since it allows
    the good step to depend on the prior arbitrary sequence of steps.
    maybe we will want it later?*)
  Definition label_precise :=
    forall s lbl outs1 s1' outs2 s2',
      step s (O_event lbl outs1) s1' ->
      step s (O_event lbl outs2) s2' ->
      outs1 = outs2 /\ s1' = s2'.

  Lemma eventually_will_step_to_star :
    forall (P : state * list (IO_event label message) -> Prop) s t,
      allowed (inputs_of t) ->
      eventually will_step P (s, t) ->
      exists s' tr,
        star step s tr s' /\
        inputs_of tr = [] /\
        P (s', tr ++ t).
  Proof.
    intros P s0 t0 Hallow Hwill.
    remember (s0, t0) as st eqn:Est.
    revert s0 t0 Hallow Est.
    induction Hwill as [[s' t'] HP | [s' t'] midset Hcan Hmid IH];
      intros s0 t0 Hallow [= -> ->].
    - exists s0, []. split; [constructor|]. split; [reflexivity|exact HP].
    - destruct Hcan as [lbl Hcan].
      assert (Hallow0 : allowed (inputs_of ([] ++ t0))) by (cbn; exact Hallow).
      destruct (Hcan s0 [] (star_refl _ _) Hallow0)
        as [Hmid0 | (s'' & outs & Hstep & Hmidset)].
      + apply (IH (s0, [] ++ t0) Hmid0 s0 t0 Hallow eq_refl).
      + assert (Hallow' : allowed (inputs_of (O_event lbl outs :: t0))).
        { exact Hallow. }
        destruct (IH _ Hmidset s'' (O_event lbl outs :: t0) Hallow' eq_refl)
          as (s_final & tr & Hstar & Hinp & HP).
        exists s_final, (tr ++ [O_event lbl outs]). split.
        * eapply star_app; [apply star_one; exact Hstep | exact Hstar].
        * split.
          -- rewrite inputs_of_app, Hinp. reflexivity.
          -- rewrite <- app_assoc. exact HP.
  Qed.

  Definition might_output start t output :=
    exists t' s',
      star step start t' s' /\
        inputs_of t' = [] /\
        In output (outputs_of (t' ++ t)).

  Definition might_output_equiv start t o :=
    exists o', equiv o' o /\ might_output start t o'.

  Definition produces (init : state) (inputs : list message) (output : message) : Prop :=
    exists t ns,
      star step init t ns /\
      inputs_of t = inputs /\
      In output (outputs_of t).

  Definition will_output start t (output : message) : Prop :=
    eventually will_step
      (fun '(_, t') => In output (outputs_of t'))
      (start, t).

  Definition will_output_equiv start t (output : message) : Prop :=
    eventually will_step
      (fun '(_, t') => exists o', equiv o' output /\ In o' (outputs_of t'))
      (start, t).

  Lemma will_implies_might :
    forall s t o,
      allowed (inputs_of t) ->
      will_output s t o ->
      might_output s t o.
  Proof.
    intros s0 t0 o Hall Hwill.
    cbv [will_output] in Hwill.
    remember (s0, t0) as st eqn:Est.
    revert s0 t0 Hall Est.
    induction Hwill as [[s' t'] HP | [s' t'] midset Hcan Hmid IH];
      intros s0 t0 Hall [= -> ->].
    - exists [], s0. split; [constructor|].
      split; [reflexivity|exact HP].
    - cbv [will_step] in Hcan. destruct Hcan as [lbl Hcan].
      specialize (Hcan s0 [] (star_refl _ _)).
      cbn in Hcan. specialize (Hcan Hall).
      destruct Hcan as [Hmid0 | (s'' & outs & Hstep & Hmidset)].
      + apply (IH (s0, t0) Hmid0 s0 t0 Hall eq_refl).
      + assert (Hall' : allowed (inputs_of (O_event lbl outs :: t0))).
        { exact Hall. }
        destruct (IH _ Hmidset s'' (O_event lbl outs :: t0) Hall' eq_refl)
          as (t'' & s''' & Hstar'' & Hinp'' & Hout'').
        exists (t'' ++ [O_event lbl outs]), s'''. split.
        * eapply star_app; [apply star_one; exact Hstep | exact Hstar''].
        * split.
          -- rewrite inputs_of_app, Hinp''. reflexivity.
          -- rewrite <- app_assoc. exact Hout''.
  Qed.

  Lemma will_output_step :
    forall s e s' t o,
      step s e s' ->
      will_output s t o ->
      will_output s' (e :: t) o.
  Proof.
    intros s e s' t o Hstep Hwill.
    cbv [will_output] in *.
    remember (s, t) as st eqn:Est.
    revert s e s' t Hstep Est.
    induction Hwill as [[s0 t0] HP | [s0 t0] midset Hcan Hmid IH];
      intros s_orig e_orig s_new t_orig Hstep [= -> ->].
    - apply eventually_done. cbn in HP |- *.
      apply in_or_app. right. exact HP.
    - destruct Hcan as [lbl Hcan].
      apply eventually_step_cps. exists lbl.
      intros s_d t_d Hstar_d Hallow_d.
      (* Fold the single step [e_orig] into the demon run [t_d]: with newest-first
         traces the combined run is [t_d ++ [e_orig]] and lands exactly where the
         demon does, so no permutation is needed. *)
      assert (Hstar_combined : star step s_orig (t_d ++ [e_orig]) s_d).
      { eapply star_app; [apply star_one; exact Hstep | exact Hstar_d]. }
      assert (Hallow_o : allowed (inputs_of ((t_d ++ [e_orig]) ++ t_orig))).
      { rewrite <- app_assoc. exact Hallow_d. }
      specialize (Hcan s_d (t_d ++ [e_orig]) Hstar_combined Hallow_o).
      destruct Hcan as [Hmid_left | (s'' & outs & Hstep_a & Hmidset)].
      + left. pose proof (Hmid _ Hmid_left) as Hev.
        rewrite <- app_assoc in Hev. exact Hev.
      + right. exists s'', outs. split; [exact Hstep_a|].
        pose proof (Hmid _ Hmidset) as Hev.
        rewrite <- app_assoc in Hev. exact Hev.
  Qed.

  Definition incl_mod (l1 l2 : list message) : Prop :=
    forall a,
      incl a l1 ->
      consistent a l1 ->
      exists b,
        incl b l2 /\ Forall2 equiv a b /\ consistent b l2.

  Lemma incl_mod_refl l : incl_mod l l.
  Proof.
    destruct equiv_equiv as [Href _ _].
    intros a Ha Hc. exists a. split; [exact Ha | split; [| exact Hc]].
    clear Ha Hc. induction a as [|x xs IH].
    - constructor.
    - constructor; [apply Href | exact IH].
  Qed.

  (* [will_output_equiv]-analogues of [will_implies_might]/[will_output_step]:
     the target output is only pinned down up to [equiv]. *)
  Lemma will_equiv_implies_might_equiv s t o :
    allowed (inputs_of t) ->
    will_output_equiv s t o ->
    might_output_equiv s t o.
  Proof.
    intros Hall Hwill. unfold will_output_equiv in Hwill.
    destruct (eventually_will_step_to_star _ s t Hall Hwill)
      as (s' & tr & Hstar & Hinp & (o' & Hequiv & Hin)).
    exists o'. split; [exact Hequiv|].
    exists tr, s'. split; [exact Hstar | split; [exact Hinp | exact Hin]].
  Qed.

  Lemma will_output_equiv_step s e s' t o :
    step s e s' ->
    will_output_equiv s t o ->
    will_output_equiv s' (e :: t) o.
  Proof.
    intros Hstep Hwill.
    cbv [will_output_equiv] in *.
    remember (s, t) as st eqn:Est.
    revert s e s' t Hstep Est.
    induction Hwill as [[s0 t0] HP | [s0 t0] midset Hcan Hmid IH];
      intros s_orig e_orig s_new t_orig Hstep [= -> ->].
    - apply eventually_done. destruct HP as (o' & Heq & Hin).
      exists o'. split; [exact Heq|]. cbn. apply in_or_app. right. exact Hin.
    - destruct Hcan as [lbl Hcan].
      apply eventually_step_cps. exists lbl.
      intros s_d t_d Hstar_d Hallow_d.
      assert (Hstar_combined : star step s_orig (t_d ++ [e_orig]) s_d).
      { eapply star_app; [apply star_one; exact Hstep | exact Hstar_d]. }
      assert (Hallow_o : allowed (inputs_of ((t_d ++ [e_orig]) ++ t_orig))).
      { rewrite <- app_assoc. exact Hallow_d. }
      specialize (Hcan s_d (t_d ++ [e_orig]) Hstar_combined Hallow_o).
      destruct Hcan as [Hmid_left | (s'' & outs & Hstep_a & Hmidset)].
      + left. pose proof (Hmid _ Hmid_left) as Hev.
        rewrite <- app_assoc in Hev. exact Hev.
      + right. exists s'', outs. split; [exact Hstep_a|].
        pose proof (Hmid _ Hmidset) as Hev.
        rewrite <- app_assoc in Hev. exact Hev.
  Qed.

  Lemma will_output_equiv_star s t' s' t o :
    star step s t' s' ->
    will_output_equiv s t o ->
    will_output_equiv s' (t' ++ t) o.
  Proof.
    intros Hstar Hwill. induction Hstar as [ | t0 sa e sb Hstar' IH Hstep].
    - exact Hwill.
    - exact (will_output_equiv_step sa e sb (t0 ++ t) o Hstep IH).
  Qed.

  Context (outputs_wf : list message -> Prop).
  Context (initial : state).

  Definition outputs_well_formed :=
    forall t s, star step initial t s -> outputs_wf (outputs_of t).

  Definition might_implies_will_equiv_at s t :=
    forall o,
      might_output s t o ->
      will_output_equiv s t o.

  Definition might_implies_will_equiv :=
    forall t s o,
      star step initial t s ->
      allowed (inputs_of t) ->
      might_output s t o ->
      will_output_equiv s t o.

  Definition might_implies_will_equiv' :=
    forall t s o,
      star step initial t s ->
      allowed (inputs_of t) ->
      In o (outputs_of t) ->
      forall s' t',
        incl_mod (inputs_of t) (inputs_of t') ->
        star step initial t' s' ->
        allowed (inputs_of t') ->
        will_output_equiv s' t' o.

  Lemma might_output_step_preserved :
    might_implies_will_equiv ->
    forall ns tau e ns' o,
      allowed (inputs_of (e :: tau)) ->
      star step initial tau ns ->
      step ns e ns' ->
      might_output_equiv ns tau o ->
      might_output_equiv ns' (e :: tau) o.
  Proof.
    intros Hciw ns tau e ns' o Halt Hstar Hstep Hcan.
    destruct Hcan as (o' & Hequiv & Hmo).
    assert (Halt_tau : allowed (inputs_of tau)).
    { eapply allowed_submultiset; [|exact Halt].
      exists (inputs_of [e]). change (e :: tau) with ([e] ++ tau).
      rewrite inputs_of_app. apply Permutation_app_comm. }
    pose proof (Hciw tau ns o' Hstar Halt_tau Hmo) as Hwill.
    pose proof (will_output_equiv_step ns e ns' tau o' Hstep Hwill) as Hwill'.
    pose proof (will_equiv_implies_might_equiv ns' (e :: tau) o' Halt Hwill') as Hmoe.
    destruct Hmoe as (o'' & Hequiv2 & Hmo'').
    exists o''. split; [| exact Hmo''].
    destruct equiv_equiv as [_ _ Htrans]. eapply Htrans; [exact Hequiv2 | exact Hequiv].
  Qed.

  Definition monotone :=
    forall t1 t2 s1 s2 o,
      star step initial t1 s1 ->
      star step s1 t2 s2 ->
      allowed (inputs_of t1) ->
      allowed (inputs_of (t2 ++ t1)) ->
      might_output s1 t1 o ->
      might_output_equiv s2 (t2 ++ t1) o.

  Definition monotone_mod_equiv :=
    forall t1 t2 s1 s2 o,
      star step initial t1 s1 ->
      star step initial t2 s2 ->
      allowed (inputs_of t1) ->
      allowed (inputs_of t2) ->
      incl_mod (inputs_of t1) (inputs_of t2) ->
      might_output s1 t1 o ->
      might_output_equiv s2 t2 o.

  Definition monotone_multiset :=
    forall t1 t2 s1 s2 o,
      star step initial t1 s1 ->
      star step initial t2 s2 ->
      allowed (inputs_of t1) ->
      allowed (inputs_of t2) ->
      submultiset (inputs_of t1) (inputs_of t2) ->
      might_output s1 t1 o ->
      might_output_equiv s2 t2 o.

  Lemma monotone_multiset_of_mod_equiv : monotone_mod_equiv -> monotone_multiset.
  Proof.
    intros Hmono t1 t2 s1 s2 o Hs1 Hs2 Hal1 Hal2 Hsub Hmight.
    apply (Hmono t1 t2 s1 s2 o Hs1 Hs2 Hal1 Hal2).
    - intros a Hincl Hcons. exists a. split; [|split].
      + destruct Hsub as (rest & Hperm). intros x Hx.
        eapply Permutation_in; [symmetry; exact Hperm|].
        apply in_or_app. left. apply Hincl. exact Hx.
      + clear Hincl Hcons. induction a as [|x xs IHa]; constructor; [reflexivity | exact IHa].
      + exact (Hcm a (inputs_of t1) (inputs_of t2) Hal1 Hal2 Hsub Hcons).
    - exact Hmight.
  Qed.

  Lemma ciw'_iff_ciw_and_monotone' :
    might_implies_will_equiv' <-> might_implies_will_equiv /\ monotone_mod_equiv.
  Proof.
    split.
    - (* -> *)
      intros Hciw'. split.
      + (* might_implies_will_equiv *)
        intros t s o Hstar Hall Hcan.
        destruct Hcan as (T_a & s_f & Hstar_a & Hinp_a & Hout).
        pose proof (star_app _ _ _ _ _ _ Hstar Hstar_a) as Hstar_T.
        assert (HallT : allowed (inputs_of (T_a ++ t))).
        { rewrite inputs_of_app, Hinp_a. exact Hall. }
        apply (Hciw' (T_a ++ t) s_f o Hstar_T HallT Hout s t).
        * rewrite inputs_of_app, Hinp_a. apply incl_mod_refl.
        * exact Hstar.
        * exact Hall.
      + (* monotone_mod_equiv *)
        intros t1 t2 s1 s2 o Hstar1 Hstar2 Hall1 Hall2 Hincl Hcan1.
        destruct Hcan1 as (T_a & s_f & Hstar_a & Hinp_a & Hout).
        pose proof (star_app _ _ _ _ _ _ Hstar1 Hstar_a) as Hstar_T.
        assert (HallT : allowed (inputs_of (T_a ++ t1))).
        { rewrite inputs_of_app, Hinp_a. exact Hall1. }
        assert (HinclT : incl_mod (inputs_of (T_a ++ t1)) (inputs_of t2)).
        { rewrite inputs_of_app, Hinp_a. exact Hincl. }
        pose proof (Hciw' (T_a ++ t1) s_f o Hstar_T HallT Hout s2 t2 HinclT Hstar2 Hall2)
          as Hwill.
        exact (will_equiv_implies_might_equiv s2 t2 o Hall2 Hwill).
    - (* <- *)
      intros [Hciw Hmono] t s o Hstar Hall Hout s' t' Hincl Hstar' Hall'.
      assert (Hmst : might_output s t o).
      { exists [], s. split; [constructor|]. split; [reflexivity|]. cbn. exact Hout. }
      pose proof (Hmono t t' s s' o Hstar Hstar' Hall Hall' Hincl Hmst) as Hmoe.
      destruct Hmoe as (o'' & Hequiv & Hmo).
      pose proof (Hciw t' s' o'' Hstar' Hall' Hmo) as Hwill.
      unfold will_output_equiv in *.
      eapply eventually_weaken; [exact Hwill|].
      intros [sf tf] (w & Heqw & Hinw). exists w. split; [| exact Hinw].
      destruct equiv_equiv as [_ _ Htrans]. eapply Htrans; [exact Heqw | exact Hequiv].
  Qed.

  Lemma ciw_monotone :
    might_implies_will_equiv ->
    monotone.
  Proof.
    intros Hciw t1 t2 s1 s2 o Hstar1 Hstar2 Hall1 Hallt Hcan.
    pose proof (Hciw t1 s1 o Hstar1 Hall1 Hcan) as Hwill.
    apply (will_equiv_implies_might_equiv s2 (t2 ++ t1) o Hallt).
    exact (will_output_equiv_star s1 t2 s2 t1 o Hstar2 Hwill).
  Qed.

  Definition ev_stable (P : state * list (IO_event label message) -> Prop) : Prop :=
    forall s s' e t,
      P (s, t) ->
      step s e s' ->
      P (s', e :: t).

  Lemma ev_stable_star P s t s' t' :
    ev_stable P ->
    star step s t' s' ->
    P (s, t) ->
    P (s', t' ++ t).
  Proof.
    intros Hst Hstar Hinit. induction Hstar; auto.
    simpl. eapply Hst; eauto.
  Qed.

  Lemma ev_stable_ex_out (R : message -> Prop) :
    ev_stable (fun '(_, t') => exists o', R o' /\ In o' (outputs_of t')).
  Proof.
    intros s s' e t (o' & HR & Hin) Hstep. exists o'. split; [exact HR|].
    change (e :: t) with ([e] ++ t). rewrite outputs_of_app.
    apply in_or_app. right. exact Hin.
  Qed.

  Lemma eventually_carry_stable_gen P Q st :
    ev_stable P ->
    P st ->
    eventually will_step Q st ->
    eventually will_step (fun x => P x /\ Q x) st.
  Proof.
    intros Hstable.
    intros HP Hev. revert HP.
    induction Hev as [[s0 t0] HQ | [s0 t0] midset Hstep Hnext IH]; intros HP.
    - apply eventually_done. split; [exact HP | exact HQ].
    - destruct Hstep as [lbl Hstep].
      apply eventually_step_cps. exists lbl.
      intros s' td Hstar_d Hallow_d.
      assert (HP' : P (s', td ++ t0)).
      { eapply ev_stable_star; [exact Hstable | exact Hstar_d | exact HP]. }
      specialize (Hstep s' td Hstar_d Hallow_d).
      destruct Hstep as [Hleft | (s'' & outs & Hst & Hright)].
      + left. apply (IH (s', td ++ t0) Hleft). exact HP'.
      + right. exists s'', outs. split; [exact Hst|].
        apply (IH (s'', O_event lbl outs :: td ++ t0) Hright).
        eapply Hstable; [exact HP' | exact Hst].
  Qed.

  Lemma eventually_will_step_advance Q s t s' t' :
    ev_stable Q ->
    star step s t' s' ->
    allowed (inputs_of (t' ++ t)) ->
    eventually will_step Q (s, t) ->
    eventually will_step Q (s', t' ++ t).
  Proof.
    intros Hstable Hstar Hallow Hev.
    destruct Hev as [HQ | midset Hstep Hnext].
    - apply eventually_done.
      eapply ev_stable_star; [exact Hstable | exact Hstar | exact HQ].
    - destruct Hstep as [lblQ HQstep].
      apply eventually_step_cps. exists lblQ.
      intros s'' sigma Hstar_sigma Hallow_sigma.
      assert (Hcomb : star step s (sigma ++ t') s'').
      { eapply star_app; [exact Hstar | exact Hstar_sigma]. }
      assert (Hallow_comb : allowed (inputs_of ((sigma ++ t') ++ t))).
      { rewrite <- app_assoc. exact Hallow_sigma. }
      specialize (HQstep s'' (sigma ++ t') Hcomb Hallow_comb).
      destruct HQstep as [Hleft | (s3 & outs & Hst & Hright)].
      + left. pose proof (Hnext _ Hleft) as Hev.
        rewrite <- app_assoc in Hev. exact Hev.
      + right. exists s3, outs. split; [exact Hst|].
        pose proof (Hnext _ Hright) as Hev.
        rewrite <- app_assoc in Hev. exact Hev.
  Qed.

  Lemma eventually_will_step_and P Q st :
    ev_stable P ->
    ev_stable Q ->
    eventually will_step P st ->
    eventually will_step Q st ->
    eventually will_step (fun x => P x /\ Q x) st.
  Proof.
    intros HsP HsQ HevP HevQ. revert HevQ.
    induction HevP as [[s0 t0] HP | [s0 t0] midset HstepP HnextP IHP]; intros HevQ.
    - apply eventually_carry_stable_gen; [exact HsP | exact HP | exact HevQ].
    - destruct HstepP as [lblP HstepP].
      apply eventually_step_cps. exists lblP.
      intros s' td Hstar_d Hallow_d.
      specialize (HstepP s' td Hstar_d Hallow_d).
      destruct HstepP as [Hleft | (s'' & outs & Hst & Hright)].
      + left. apply (IHP (s', td ++ t0) Hleft).
        eapply eventually_will_step_advance; eauto.
      + right. exists s'', outs. split; [exact Hst|].
        apply (IHP (s'', O_event lblP outs :: td ++ t0) Hright).
        eapply eventually_will_step_advance with (t' := _ :: _); eauto.
        econstructor; eauto.
  Qed.

  Lemma ev_stable_Forall Ps :
    Forall ev_stable Ps ->
    ev_stable (fun x => Forall (fun P => P x) Ps).
  Proof.
    intros H. cbv [ev_stable]. intros ? ? ? ? H' ?.
    eapply Forall_impl.
    2: { apply Forall_and; [exact H|exact H']. }
    simpl. intros. fwd. eauto.
  Qed.

  Hint Constructors eventually : core.
  Lemma eventually_will_step_Forall Ps st :
    Forall ev_stable Ps ->
    Forall (fun P => eventually will_step P st) Ps ->
    eventually will_step (fun x => Forall (fun P => P x) Ps) st.
  Proof.
    intros H1 H2. induction H1; invert H2.
    - auto.
    - eapply eventually_weaken.
      + eapply eventually_will_step_and; [| |eassumption|apply IHForall]; auto.
        apply ev_stable_Forall; auto.
      + simpl. intros. fwd. auto.
  Qed.

  Lemma will_output_all outs ns t :
    might_implies_will_equiv ->
    star step initial t ns ->
    allowed (inputs_of t) ->
    Forall (might_output_equiv ns t) outs ->
    eventually will_step
      (fun '(_, t') => Forall (fun o => exists o', equiv o o' /\ In o' (outputs_of t')) outs) (ns, t).
  Proof.
    intros Hmiw Hstar Hallow HF.
    eapply eventually_weaken.
    - eapply (eventually_will_step_Forall
                (map (fun o => (fun '(_, t') => exists o', equiv o o' /\ In o' (outputs_of t'))) outs)
                (ns, t)).
      + rewrite Forall_map, Forall_forall. intros o _.
        apply (ev_stable_ex_out (fun o' => equiv o o')).
      + rewrite Forall_map. eapply Forall_impl; [| exact HF]. intros o Hmoe.
        destruct Hmoe as (o' & Hequiv & Hmo).
        pose proof (Hmiw t ns o' Hstar Hallow Hmo) as HW.
        unfold will_output_equiv in HW.
        eapply eventually_weaken; [exact HW|].
        intros [sf tf] (w & Heqw & Hinw). exists w. split; [| exact Hinw].
        destruct equiv_equiv as [_ Hsym Htrans].
        eapply Htrans; [apply Hsym; exact Hequiv | apply Hsym; exact Heqw].
    - intros [s' t'] H. rewrite Forall_map in H. exact H.
  Qed.

  Context (D : list message -> message -> Prop).

  Definition complete :=
    forall t s,
      star step initial t s ->
      allowed (inputs_of t) ->
      forall output,
        D (inputs_of t) output ->
        will_output_equiv s t output.

  Definition sound :=
    forall t s,
      star step initial t s ->
      allowed (inputs_of t) ->
      forall output,
        In output (outputs_of t) ->
        D (inputs_of t) output.

  Definition described_by := sound /\ complete.

  Definition complete_weak :=
    forall t s,
      star step initial t s ->
      allowed (inputs_of t) ->
      forall output,
        D (inputs_of t) output ->
        might_output s t output.

  Definition described_by_weak := sound /\ complete_weak.

  Lemma complete_weak_implies_strong :
    complete_weak ->
    might_implies_will_equiv ->
    complete.
  Proof.
    intros Hweak Hcan t s Hstar Hall o HD.
    apply Hcan; auto.
  Qed.
End step.

Section steps_corresp.
  Context {label message : Type}.
  Context (allowed : list message -> Prop).
  Context (equiv : message -> message -> Prop).
  Context (equiv_equiv : Equivalence equiv).
  Context (consistent : list message -> list message -> Prop).
  Local Notation IO_event := (IO_event label message).

  Section steps.
    Context {state1 : Type}.
    Context (step1 : state1 -> IO_event -> state1 -> Prop).
    Context (initial1 : state1).

    Context {state2 : Type}.
    Context (step2 : state2 -> IO_event -> state2 -> Prop).
    Context (initial2 : state2).

    Definition steps_corresp_sound :=
      forall t2 ns2 output,
        star step2 initial2 t2 ns2 ->
        allowed (inputs_of t2) ->
        In output (outputs_of t2) ->
        produces step1 initial1 (inputs_of t2) output.

    Definition steps_corresp_sound' :=
      forall ns2 inps o,
        star step2 initial2 (map I_event inps) ns2 ->
        allowed inps ->
        will_output_equiv step2 equiv allowed ns2 (map I_event inps) o ->
        produces step1 initial1 inps o.

    Definition steps_corresp_complete :=
      forall t2 ns2 output,
        star step2 initial2 t2 ns2 ->
        allowed (inputs_of t2) ->
        produces step1 initial1 (inputs_of t2) output ->
        might_output step2 ns2 t2 output.

    (* Primed completeness: restrict system 2's observed trace to be input-only
       (the dual restriction to steps_corresp_sound').  This is the form the
       cross-graph completeness lemma proves directly; the bridge below recovers
       the (up-to-equiv) unprimed version from monotone_mod_equiv/input_total of
       system 2. *)
    Definition steps_corresp_complete' :=
      forall ns2 inps o,
        star step2 initial2 (map I_event inps) ns2 ->
        allowed inps ->
        produces step1 initial1 inps o ->
        might_output step2 ns2 (map I_event inps) o.

    Lemma complete_sound D :
      input_total step1 ->
      complete_weak step1 allowed initial1 D ->
      steps_corresp_complete ->
      complete_weak step2 allowed initial2 D.
    Proof.
      intros Hit1 Hcw1 Hcorresp t2 ns2 Hstar2 Hall2 o HD.
      destruct (star_recv step1 Hit1 (inputs_of t2) initial1)
        as (t1 & ns1 & Hstar1 & Hinp1).
      assert (Hall1 : allowed (inputs_of t1)).
      {  rewrite Hinp1. exact Hall2. }
      assert (HD1 : D (inputs_of t1) o) by (rewrite Hinp1; exact HD).
      apply (Hcw1 _ _ Hstar1 Hall1) in HD1.
      destruct HD1 as (t' & ns' & Hstar' & Hinpt' & Hout).
      pose proof (star_app _ _ _ _ _ _ Hstar1 Hstar') as Hstar_full.
      apply (Hcorresp t2 ns2 o Hstar2 Hall2).
      unfold produces. exists (t' ++ t1), ns'.
      split; [exact Hstar_full|]. split.
      - rewrite inputs_of_app, Hinpt'. exact Hinp1.
      - exact Hout.
    Qed.

    Lemma sound_sound D :
      sound step1 allowed initial1 D ->
      steps_corresp_sound ->
      sound step2 allowed initial2 D.
     Proof.
      intros Hs1 Hcorresp t2 s2 Hstar2 Hall2 o Hout2.
      pose proof (Hcorresp _ _ _ Hstar2 Hall2 Hout2) as Hpr. unfold produces in Hpr.
      destruct Hpr as (t1 & s1 & Hstar1 & Hinp & Hout1).
      assert (Hall1 : allowed (inputs_of t1)).
      {  rewrite Hinp. exact Hall2. }
      pose proof (Hs1 _ _ Hstar1 Hall1 _ Hout1) as HD.
      rewrite Hinp in HD. exact HD.
    Qed.

    Lemma steps_corresp_sound'_implies_sound :
      input_total step2 ->
      might_implies_will_equiv' step2 equiv consistent allowed initial2 ->
      steps_corresp_sound' ->
      steps_corresp_sound.
    Proof.
      intros Hit2 Hciw2 Hscs' t2 ns2 o Hstar2 Hall2 Hout2.
      destruct (star_recv_map step2 Hit2 (inputs_of t2) initial2) as (ns2' & Hstar2').
      assert (Hall' : allowed (inputs_of (map I_event (inputs_of t2) : list IO_event))).
      {  rewrite inputs_of_map_I_event. exact Hall2. }
      assert (Hincl : incl_mod equiv consistent (inputs_of t2)
                           (inputs_of (map I_event (inputs_of t2) : list IO_event))).
      { rewrite inputs_of_map_I_event. apply (incl_mod_refl equiv equiv_equiv consistent). }
      pose proof (Hciw2 t2 ns2 o Hstar2 Hall2 Hout2
                       ns2' (map I_event (inputs_of t2)) Hincl Hstar2' Hall') as Hwill.
      exact (Hscs' ns2' (inputs_of t2) o Hstar2' Hall2 Hwill).
    Qed.

    (* Dual bridge: recover (up-to-equiv) unprimed completeness from the primed
       version, using input_total (to realize the input-only run) and
       monotone_mod_equiv (to transfer the capability to the actually-observed run
       on the same inputs).  Since only an up-to-equiv monotonicity survives, the
       conclusion is the equiv-relaxed form of steps_corresp_complete. *)
    Lemma steps_corresp_complete'_implies_complete :
      input_total step2 ->
      monotone_mod_equiv step2 equiv consistent allowed initial2 ->
      steps_corresp_complete' ->
      forall t2 ns2 output,
        star step2 initial2 t2 ns2 ->
        allowed (inputs_of t2) ->
        produces step1 initial1 (inputs_of t2) output ->
        might_output_equiv step2 equiv ns2 t2 output.
    Proof.
      intros Hit2 Hmono2 Hcc' t2 ns2 o Hstar2 Hall2 Hprod.
      destruct (star_recv_map step2 Hit2 (inputs_of t2) initial2) as (ns2' & Hstar2').
      pose proof (Hcc' ns2' (inputs_of t2) o Hstar2' Hall2 Hprod) as Hcan'.
      apply (Hmono2 (map I_event (inputs_of t2)) t2 ns2' ns2 o Hstar2' Hstar2).
      -  rewrite inputs_of_map_I_event. exact Hall2.
      - exact Hall2.
      - rewrite inputs_of_map_I_event. apply (incl_mod_refl equiv equiv_equiv consistent).
      - exact Hcan'.
    Qed.

    Definition steps_bicorresp :=
      forall t1 t2 ns1 ns2,
        star step1 initial1 t1 ns1 ->
        star step2 initial2 t2 ns2 ->
        allowed (inputs_of t1) ->
        allowed (inputs_of t2) ->
        inputs_of t1 = inputs_of t2 ->
        forall output,
          might_output_equiv step1 equiv ns1 t1 output <->
          might_output_equiv step2 equiv ns2 t2 output.

    Lemma sound_complete_bicorresp :
      monotone_mod_equiv step1 equiv consistent allowed initial1 ->
      steps_corresp_complete ->
      steps_corresp_sound ->
      steps_bicorresp.
    Proof.
      intros Hmono Hcomp Hsound t1 t2 ns1 ns2 Hstar1 Hstar2 Hall1 Hall2 Heq o.
      split.
      - (* -> : witness [o'] carries through steps_corresp_complete unchanged. *)
        intros (o' & Hequiv & Hmo1). exists o'. split; [exact Hequiv|].
        destruct Hmo1 as (t' & ns' & Hstar' & Hinpt' & Hout).
        pose proof (star_app _ _ _ _ _ _ Hstar1 Hstar') as Hstar1'.
        apply (Hcomp t2 ns2 o' Hstar2 Hall2).
        unfold produces. exists (t' ++ t1), ns'.
        split; [exact Hstar1'|]. split.
        + rewrite inputs_of_app, Hinpt'. exact Heq.
        + exact Hout.
      - (* <- : steps_corresp_sound recovers an input-only run of system 1, then
             monotone_mod_equiv transfers the capability (up to [equiv]) to [t1]. *)
        intros (o' & Hequiv & Hmo2).
        destruct Hmo2 as (t' & ns' & Hstar' & Hinpt' & Hout).
        pose proof (star_app _ _ _ _ _ _ Hstar2 Hstar') as Hstar2'.
        assert (Hall2' : allowed (inputs_of (t' ++ t2))).
        { rewrite inputs_of_app, Hinpt'. exact Hall2. }
        pose proof (Hsound _ _ _ Hstar2' Hall2' Hout) as Hpr. unfold produces in Hpr.
        destruct Hpr as (t1' & ns1' & Hstar1' & Heqinp & Hout1).
        assert (Hcan1' : might_output step1 ns1' t1' o').
        { exists [], ns1'. split; [constructor|].
          split; [reflexivity|exact Hout1]. }
        assert (Hmoe : might_output_equiv step1 equiv ns1 t1 o').
        { apply (Hmono t1' t1 ns1' ns1 o' Hstar1' Hstar1).
          - rewrite Heqinp. exact Hall2'.
          - exact Hall1.
          - rewrite Heqinp, inputs_of_app, Hinpt', <- Heq.
            apply (incl_mod_refl equiv equiv_equiv consistent).
          - exact Hcan1'. }
        destruct Hmoe as (o'' & Hequiv2 & Hmo1'').
        exists o''. split; [| exact Hmo1''].
        destruct equiv_equiv as [_ _ Htrans]. eapply Htrans; [exact Hequiv2 | exact Hequiv].
    Qed.

    Fail Fail Definition steps_equiv :=
      exists D,
        (*monotone D /\*)
        described_by step1 equiv allowed initial1 D /\
          described_by step2 equiv allowed initial2 D.
  End steps.

  Section steps.
    Context {state1 : Type}.
    Context (step1 : state1 -> IO_event -> state1 -> Prop).
    Context (initial1 : state1).

    Context {state2 : Type}.
    Context (step2 : state2 -> IO_event -> state2 -> Prop).
    Context (initial2 : state2).

    Lemma sound_impl_complete :
      steps_corresp_sound step1 initial1 step2 initial2 ->
      steps_corresp_complete step2 initial2 step1 initial1.
    Proof. Abort.

    Lemma complete_impl_sound :
      steps_corresp_complete step2 initial2 step1 initial1 ->
      steps_corresp_sound step1 initial1 step2 initial2.
    Proof. Abort.
  End steps.
End steps_corresp.
