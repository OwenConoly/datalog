(*worth comparing to https://compcert.org/doc/html/compcert.common.Smallstep.html*)
From Stdlib Require Import List Permutation RelationClasses.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
From coqutil Require Import Tactics.fwd.
From Datalog Require Import Tactics List.
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

  Lemma star_nil s s' : star s [] s' -> s' = s.
  Proof. intros H. inversion H. reflexivity. Qed.

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

Definition translate_event {L M M'} (t : M' -> M) (ev : IO_event L M') : IO_event L M :=
  match ev with
  | I_event m' => I_event (t m')
  | O_event l ms' => O_event l (map t ms')
  end.

Definition translate_step {NS L M M'} (t : M' -> M)
  (step : NS -> IO_event L M -> NS -> Prop)
  : NS -> IO_event L M' -> NS -> Prop :=
  fun ns ev ns' => step ns (translate_event t ev) ns'.

Section step.
  Context {state label message : Type}.
  Context (step : state -> IO_event label message -> state -> Prop).
  Context (equiv : message -> message -> Prop).
  Context {equiv_equiv : Equivalence equiv}.
  Context {stmt} (claim : stmt -> list message -> Prop).
  Context (consistent : stmt -> list message (*a multiset*) -> Prop).
  Context (allowed : list message (*multiset*) -> Prop).
  Context (claim_output : stmt -> list message -> Prop).
  Context (consistent_output : stmt -> list message -> Prop).

  Context (allowed_submultiset : multiset_monotone_dec allowed).
  Context (consistent_mono : forall s, multiset_monotone_inc (consistent s)).
  Context (claim_mono : forall s, incl_mod_mono_inc equiv (claim s)).
  Context (claim_output_mono : forall s, incl_mod_mono_inc equiv (claim_output s)).

  Definition consistent_le (claim consistent : stmt -> list message -> Prop) l1 l2 :=
    forall s,
      claim s l1 ->
      consistent s l1 ->
      consistent s l2.

  Definition consistently_incl (claim consistent : stmt -> list message -> Prop) l1 l2 :=
    incl_mod equiv l1 l2 /\ consistent_le claim consistent l1 l2.

  Lemma consistently_incl_refl l : consistently_incl claim consistent l l.
  Proof.
    split; [ exact (incl_mod_refl equiv l) | intros s _ Hc; exact Hc ].
  Qed.

  Lemma consistently_incl_grow_r l1 l2 l2' :
    consistently_incl claim consistent l1 l2 -> submultiset l2 l2' ->
    consistently_incl claim consistent l1 l2'.
  Proof.
    intros (Hincl & Hle) Hsub. split.
    - eapply (incl_mod_trans equiv);
        [ exact Hincl | exact (incl_mod_of_submultiset equiv _ _ Hsub) ].
    - intros s Hcl Hco. exact (consistent_mono s l2 l2' (Hle s Hcl Hco) Hsub).
  Qed.

  Lemma consistently_incl_shrink_l l1 l1' l2 :
    submultiset l1' l1 -> consistently_incl claim consistent l1 l2 ->
    consistently_incl claim consistent l1' l2.
  Proof.
    intros Hsub (Hincl & Hle). split.
    - eapply (incl_mod_trans equiv);
        [ exact (incl_mod_of_submultiset equiv _ _ Hsub) | exact Hincl ].
    - intros s Hcl Hco. apply (Hle s).
      + eapply claim_mono; [ exact Hcl | exact (incl_mod_of_submultiset equiv _ _ Hsub) ].
      + exact (consistent_mono s l1' l1 Hco Hsub).
  Qed.

  CoInductive noncontradictory_wf (claim consistent : stmt -> list message -> Prop)
    (wf : list message -> Prop) (l1 l2 : list message) : Prop :=
  | nc_intro l1' :
    submultiset l1 l1' ->
    wf l1' ->
    consistently_incl claim consistent l2 l1' ->
    noncontradictory_wf _ _ _ l2 l1' ->
    noncontradictory_wf _ _ _ l1 l2.

  Definition noncontradictory_inputs := noncontradictory_wf claim consistent allowed.
  Context (outputs_wf : list message -> Prop).
  Context (outputs_wf_consistent :
             forall s l, outputs_wf l -> claim_output s l -> consistent_output s l).
  Definition noncontradictory_outputs := noncontradictory_wf claim_output consistent_output outputs_wf.

  Lemma noncontradictory_wf_refl (wf : list message -> Prop) l :
    wf l -> noncontradictory_wf claim consistent wf l l.
  Proof.
    cofix CIH. intros Hwf. econstructor.
    - apply submultiset_refl.
    - exact Hwf.
    - exact (consistently_incl_refl l).
    - apply CIH. exact Hwf.
  Qed.

  Lemma noncontradictory_refl l : allowed l -> noncontradictory_inputs l l.
  Proof. exact (noncontradictory_wf_refl allowed l). Qed.

  Lemma noncontradictory_wf_of_submultiset (wf : list message -> Prop) l1 l2 :
    submultiset l1 l2 -> wf l2 -> noncontradictory_wf claim consistent wf l1 l2.
  Proof.
    intros Hsub Hwf. econstructor.
    - exact Hsub.
    - exact Hwf.
    - exact (consistently_incl_refl l2).
    - apply noncontradictory_wf_refl. exact Hwf.
  Qed.

  Lemma noncontradictory_wf_shrink_l (wf : list message -> Prop) l1 l1' l2 :
    submultiset l1' l1 -> noncontradictory_wf claim consistent wf l1 l2 ->
    noncontradictory_wf claim consistent wf l1' l2.
  Proof.
    intros Hsub [m Hsubm Hwf Hci Htail]. econstructor.
    - eapply submultiset_trans; [ exact Hsub | exact Hsubm ].
    - exact Hwf.
    - exact Hci.
    - exact Htail.
  Qed.

  Lemma noncontradictory_wf_shrink_r (wf : list message -> Prop) l1 l2 l2' :
    submultiset l2' l2 -> noncontradictory_wf claim consistent wf l1 l2 ->
    noncontradictory_wf claim consistent wf l1 l2'.
  Proof.
    intros Hsub [m Hsubm Hwf Hci Htail]. econstructor.
    - exact Hsubm.
    - exact Hwf.
    - eapply consistently_incl_shrink_l; [ exact Hsub | exact Hci ].
    - eapply noncontradictory_wf_shrink_l; [ exact Hsub | exact Htail ].
  Qed.

  Lemma outputs_of_perm (t1 t2 : list (IO_event label message)) :
    Permutation t1 t2 -> Permutation (outputs_of t1) (outputs_of t2).
  Proof. apply Permutation_flat_map. Qed.

  Lemma outputs_of_app (t1 t2 : list (IO_event label message)) :
    outputs_of (t1 ++ t2) = outputs_of t1 ++ outputs_of t2.
  Proof. apply flat_map_app. Qed.

  Lemma outputs_of_map_I_event (l : list message) :
    outputs_of (map (@I_event label message) l) = [].
  Proof. induction l as [|m l IH]; [reflexivity | cbn; exact IH]. Qed.

  Lemma inputs_of_perm (t1 t2 : list (IO_event label message)) :
    Permutation t1 t2 -> Permutation (inputs_of t1) (inputs_of t2).
  Proof. apply Permutation_flat_map. Qed.

  Lemma inputs_of_app (t1 t2 : list (IO_event label message)) :
    inputs_of (t1 ++ t2) = inputs_of t1 ++ inputs_of t2.
  Proof. apply flat_map_app. Qed.

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

  Lemma will_step_impl (P Q : state * list (IO_event label message) -> Prop) st :
    will_step st P ->
    (forall x, P x -> Q x) ->
    will_step st Q.
  Proof.
    destruct st as [s t]. intros [lbl H] HPQ. exists lbl.
    intros s' t' Hstar Hallow.
    destruct (H s' t' Hstar Hallow) as [HP | (s'' & outs & Hstep & HP)].
    - left. apply HPQ, HP.
    - right. exists s'', outs. split; [exact Hstep | apply HPQ, HP].
  Qed.

  Definition reachable (s : state) (t : list (IO_event label message))
                       (s' : state) (t' : list (IO_event label message)) : Prop :=
    exists tr, star step s tr s' /\ t' = tr ++ t /\
               (allowed (inputs_of t) -> allowed (inputs_of t')).

  Lemma reachable_refl s t : reachable s t s t.
  Proof. exists []. split; [apply star_refl | split; [reflexivity | exact (fun H => H)]]. Qed.

  Lemma reachable_trans s1 t1 s2 t2 s3 t3 :
    reachable s1 t1 s2 t2 -> reachable s2 t2 s3 t3 -> reachable s1 t1 s3 t3.
  Proof.
    cbv [reachable]. intros. fwd. eexists (_ ++ _).
    split; eauto using star_app. rewrite <- app_assoc. eauto.
  Qed.

  Lemma will_step_reach (s0 : state) (t0 : list (IO_event label message))
      (P : state * list (IO_event label message) -> Prop) :
    will_step (s0, t0) (fun '(s, t) => reachable s0 t0 s t -> P (s, t)) ->
    will_step (s0, t0) P.
  Proof.
    intros [lbl H]. exists lbl. intros s' t' Hstar Hallow.
    destruct (H s' t' Hstar Hallow) as [HP | (s'' & outs & Hstep & HP)].
    - left. apply HP. exists t'. split; [exact Hstar | split; [reflexivity | intros _; exact Hallow]].
    - right. exists s'', outs. split; [exact Hstep|]. apply HP.
      exists (O_event lbl outs :: t').
      split; [ eapply star_step; [exact Hstar | exact Hstep]
             | split; [reflexivity | intros _; exact Hallow] ].
  Qed.

  (* [eventually]-analogue of [will_step_reach]: at every reached state the target
     may assume it is [reachable] from [(s0, t0)]. *)
  Lemma eventually_will_step_reach (s0 : state) (t0 : list (IO_event label message))
      (P : state * list (IO_event label message) -> Prop) :
    eventually will_step (fun '(s, t) => reachable s0 t0 s t -> P (s, t)) (s0, t0) ->
    eventually will_step P (s0, t0).
  Proof.
    intros Hev.
    cut (forall st, reachable s0 t0 (fst st) (snd st) ->
           eventually will_step (fun '(s, t) => reachable s0 t0 s t -> P (s, t)) st ->
           eventually will_step P st).
    { intros H. apply (H (s0, t0)); [ apply reachable_refl | exact Hev ]. }
    clear Hev. intros st Hr Hev. revert Hr.
    induction Hev as [ [s' t'] HQ | [s' t'] ms Hcan Hmid IH ]; intros Hr; cbn [fst snd] in Hr.
    - apply eventually_done. apply HQ, Hr.
    - eapply eventually_step with (midset := fun mid => ms mid /\ reachable s0 t0 (fst mid) (snd mid)).
      + apply will_step_reach. eapply will_step_impl; [ exact Hcan | ].
        intros [s'' t''] Hm Hr2. cbn [fst snd]. split; [ exact Hm | eapply reachable_trans; eassumption ].
      + intros [s'' t''] [Hm Hr2]. apply IH; [ exact Hm | exact Hr2 ].
  Qed.

  Lemma eventually_will_step_annotate (P : state * list (IO_event label message) -> Prop) s0 t0 :
    eventually will_step P (s0, t0) ->
    eventually will_step (fun '(s, t) => reachable s0 t0 s t /\ P (s, t)) (s0, t0).
  Proof.
    intros Hev. apply eventually_will_step_reach.
    eapply eventually_weaken; [ exact Hev | ].
    intros [s t] HP Hr. split; [ exact Hr | exact HP ].
  Qed.

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
        noncontradictory_inputs (inputs_of t) (inputs_of t') ->
        consistently_incl claim consistent (inputs_of t) (inputs_of t') ->
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
    intros Hmiw ns tau e ns' o Halt Hstar Hstep Hcan.
    destruct Hcan as (o' & Hequiv & Hmo).
    assert (Halt_tau : allowed (inputs_of tau)).
    { eapply allowed_submultiset; [exact Halt|].
      exists (inputs_of [e]). change (e :: tau) with ([e] ++ tau).
      rewrite inputs_of_app. apply Permutation_app_comm. }
    pose proof (Hmiw tau ns o' Hstar Halt_tau Hmo) as Hwill.
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
      noncontradictory_inputs (inputs_of t1) (inputs_of t2) ->
      consistently_incl claim consistent (inputs_of t1) (inputs_of t2) ->
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
    apply (Hmono t1 t2 s1 s2 o Hs1 Hs2 Hal1 Hal2); [ | | exact Hmight ].
    - apply noncontradictory_wf_of_submultiset; [ exact Hsub | exact Hal2 ].
    - split.
      + exact (incl_mod_of_submultiset equiv _ _ Hsub).
      + intros s _ Hcons. exact (consistent_mono s (inputs_of t1) (inputs_of t2) Hcons Hsub).
  Qed.

  Lemma miw'_iff_miw_and_monotone' :
    might_implies_will_equiv' <-> might_implies_will_equiv /\ monotone_mod_equiv.
  Proof.
    split.
    - (* -> *)
      intros Hmiw'. split.
      + (* might_implies_will_equiv *)
        intros t s o Hstar Hall Hcan.
        destruct Hcan as (T_a & s_f & Hstar_a & Hinp_a & Hout).
        pose proof (star_app _ _ _ _ _ _ Hstar Hstar_a) as Hstar_T.
        assert (HallT : allowed (inputs_of (T_a ++ t))).
        { rewrite inputs_of_app, Hinp_a. exact Hall. }
        apply (Hmiw' (T_a ++ t) s_f o Hstar_T HallT Hout s t).
        * rewrite inputs_of_app, Hinp_a. cbn [app].
          apply noncontradictory_refl. exact Hall.
        * rewrite inputs_of_app, Hinp_a. apply consistently_incl_refl.
        * exact Hstar.
        * exact Hall.
      + (* monotone_mod_equiv *)
        intros t1 t2 s1 s2 o Hstar1 Hstar2 Hall1 Hall2 Hnc Hincl Hcan1.
        destruct Hcan1 as (T_a & s_f & Hstar_a & Hinp_a & Hout).
        pose proof (star_app _ _ _ _ _ _ Hstar1 Hstar_a) as Hstar_T.
        assert (HallT : allowed (inputs_of (T_a ++ t1))).
        { rewrite inputs_of_app, Hinp_a. exact Hall1. }
        assert (HncT : noncontradictory_inputs (inputs_of (T_a ++ t1)) (inputs_of t2)).
        { rewrite inputs_of_app, Hinp_a. exact Hnc. }
        assert (HinclT : consistently_incl claim consistent (inputs_of (T_a ++ t1)) (inputs_of t2)).
        { rewrite inputs_of_app, Hinp_a. exact Hincl. }
        pose proof (Hmiw' (T_a ++ t1) s_f o Hstar_T HallT Hout s2 t2 HncT HinclT Hstar2 Hall2)
          as Hwill.
        exact (will_equiv_implies_might_equiv s2 t2 o Hall2 Hwill).
    - (* <- *)
      intros [Hmiw Hmono] t s o Hstar Hall Hout s' t' Hnc Hincl Hstar' Hall'.
      assert (Hmst : might_output s t o).
      { exists [], s. split; [constructor|]. split; [reflexivity|]. cbn. exact Hout. }
      pose proof (Hmono t t' s s' o Hstar Hstar' Hall Hall' Hnc Hincl Hmst) as Hmoe.
      destruct Hmoe as (o'' & Hequiv & Hmo).
      pose proof (Hmiw t' s' o'' Hstar' Hall' Hmo) as Hwill.
      unfold will_output_equiv in *.
      eapply eventually_weaken; [exact Hwill|].
      intros [sf tf] (w & Heqw & Hinw). exists w. split; [| exact Hinw].
      destruct equiv_equiv as [_ _ Htrans]. eapply Htrans; [exact Heqw | exact Hequiv].
  Qed.

  Lemma miw_monotone :
    might_implies_will_equiv ->
    monotone.
  Proof.
    intros Hmiw t1 t2 s1 s2 o Hstar1 Hstar2 Hall1 Hallt Hcan.
    pose proof (Hmiw t1 s1 o Hstar1 Hall1 Hcan) as Hwill.
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

  (* Extract a concrete run realizing an [eventually will_step] goal: run the
     cooperative (empty) demon, so the committed steps become an input-free
     [star].  Generalizes [will_implies_might] to any trace predicate [Q]. *)
  Lemma will_step_extract (Q : list (IO_event label message) -> Prop) :
    forall s0 t0,
      allowed (inputs_of t0) ->
      eventually will_step (fun '(_, t) => Q t) (s0, t0) ->
      exists tf sf, star step s0 tf sf /\ inputs_of tf = [] /\ Q (tf ++ t0).
  Proof.
    intros s0 t0 Hall Hev.
    remember (s0, t0) as st eqn:Est.
    revert s0 t0 Hall Est.
    induction Hev as [[s' t'] HP | [s' t'] midset Hcan Hmid IH];
      intros s0 t0 Hall [= -> ->].
    - exists [], s0. split; [constructor|]. split; [reflexivity| exact HP].
    - cbv [will_step] in Hcan. destruct Hcan as [lbl Hcan].
      specialize (Hcan s0 [] (star_refl _ _)).
      cbn in Hcan. specialize (Hcan Hall).
      destruct Hcan as [Hmid0 | (s'' & outs & Hstep & Hmidset)].
      + apply (IH (s0, t0) Hmid0 s0 t0 Hall eq_refl).
      + assert (Hall' : allowed (inputs_of (O_event lbl outs :: t0))) by exact Hall.
        destruct (IH _ Hmidset s'' (O_event lbl outs :: t0) Hall' eq_refl)
          as (tf & sf & Hstarf & Hinpf & HQf).
        exists (tf ++ [O_event lbl outs]), sf. split.
        * eapply star_app; [apply star_one; exact Hstep | exact Hstarf].
        * split.
          -- rewrite inputs_of_app, Hinpf. reflexivity.
          -- rewrite <- app_assoc. exact HQf.
  Qed.

  Lemma reproduce_outputs :
    might_implies_will_equiv' ->
    forall t s t' s',
      star step initial t s ->
      star step initial t' s' ->
      allowed (inputs_of t) ->
      allowed (inputs_of t') ->
      noncontradictory_inputs (inputs_of t) (inputs_of t') ->
      consistently_incl claim consistent (inputs_of t) (inputs_of t') ->
      exists tf sf,
        star step s' tf sf /\
        inputs_of tf = [] /\
        incl_mod equiv (outputs_of t) (outputs_of (tf ++ t')).
  Proof.
    intros Hmiw' t s t' s' Hstar Hstar' Hallt Hallt' Hnc Hci.
    pose proof (proj1 miw'_iff_miw_and_monotone' Hmiw') as (Hmiw & Hmono).
    assert (HF : Forall (might_output_equiv s' t') (outputs_of t)).
    { apply Forall_forall. intros o Ho.
      assert (Hmo : might_output s t o).
      { exists [], s. split; [apply star_refl | split; [reflexivity | cbn [app]; exact Ho]]. }
      exact (Hmono t t' s s' o Hstar Hstar' Hallt Hallt' Hnc Hci Hmo). }
    pose proof (will_output_all (outputs_of t) s' t' Hmiw Hstar' Hallt' HF) as Hev.
    destruct (will_step_extract _ s' t' Hallt' Hev) as (tf & sf & Hstarf & Hinpf & HQ).
    exists tf, sf. split; [ exact Hstarf | ]. split; [ exact Hinpf | ].
    intros o Ho. rewrite Forall_forall in HQ. destruct (HQ o Ho) as (o' & Hequiv & Hin).
    exists o'. split; [ exact Hin | exact Hequiv ].
  Qed.

  Lemma noncontradictory_drive :
    input_total ->
    forall (t t' : list (IO_event label message)) s,
      noncontradictory_inputs (inputs_of t) (inputs_of t') ->
      exists tr sf,
        star step s tr sf /\
        outputs_of tr = [] /\
        allowed (inputs_of (tr ++ t)) /\
        consistently_incl claim consistent (inputs_of t') (inputs_of (tr ++ t)) /\
        noncontradictory_inputs (inputs_of t') (inputs_of (tr ++ t)).
  Proof.
    intros Hit t t' s Hnc.
    destruct Hnc as [l' [rest Hperm] HallL Hci Htail].
    destruct (star_recv_map Hit rest s) as (sf & Hstartr).
    assert (Hinp : Permutation (inputs_of (map I_event rest ++ t)) l').
    { rewrite inputs_of_app, inputs_of_map_I_event.
      eapply Permutation_trans; [ apply Permutation_app_comm | apply Permutation_sym; exact Hperm ]. }
    assert (Hsub_TL : submultiset (inputs_of (map I_event rest ++ t)) l')
      by (exists []; rewrite app_nil_r; apply Permutation_sym; exact Hinp).
    exists (map I_event rest), sf.
    split; [ exact Hstartr | ].
    split; [ apply outputs_of_map_I_event | ].
    split; [ eapply allowed_submultiset; [ exact HallL | exact Hsub_TL ] | ].
    split.
    - eapply consistently_incl_grow_r; [ exact Hci | ].
      exists []. rewrite app_nil_r. exact Hinp.
    - eapply noncontradictory_wf_shrink_r; [ exact Hsub_TL | exact Htail ].
  Qed.

  Lemma noncontradictory_outputs_of_inputs t s t' s' :
    might_implies_will_equiv' ->
    input_total ->
    outputs_well_formed ->
    star step initial t s ->
    star step initial t' s' ->
    allowed (inputs_of t') ->
    noncontradictory_inputs (inputs_of t) (inputs_of t') ->
    noncontradictory_outputs (outputs_of t) (outputs_of t').
  Proof.
    intros Hmiw' Hit Howf.
    revert t s t' s'.
    cofix CIH. intros t s t' s' Hstar Hstar' Hallt' Hnc.
    destruct (noncontradictory_drive Hit t t' s Hnc)
      as (tr & sT & Hstarr & Houttr & HallT & HciT & HncT).
    assert (HstarT : star step initial (tr ++ t) sT)
      by (eapply star_app; [ exact Hstar | exact Hstarr ]).
    destruct (reproduce_outputs Hmiw' t' s' (tr ++ t) sT
                Hstar' HstarT Hallt' HallT HncT HciT)
      as (tf & sTf & Hstarf & Hinpf & Hcov).
    assert (HstarTf : star step initial (tf ++ tr ++ t) sTf)
      by (eapply star_app; [ exact HstarT | exact Hstarf ]).
    assert (Hsub_out : submultiset (outputs_of t) (outputs_of (tf ++ tr ++ t))).
    { rewrite !outputs_of_app, Houttr. cbn [app].
      exists (outputs_of tf). apply Permutation_app_comm. }
    assert (Hwf_out : outputs_wf (outputs_of (tf ++ tr ++ t)))
      by (eapply Howf; exact HstarTf).
    assert (Hci_out : consistently_incl claim_output consistent_output (outputs_of t') (outputs_of (tf ++ tr ++ t))).
    { split; [ exact Hcov | ].
      intros s0 Hcl _.
      apply outputs_wf_consistent; [ exact Hwf_out | eapply claim_output_mono; [ exact Hcl | exact Hcov ] ]. }
    assert (Halltf : allowed (inputs_of (tf ++ tr ++ t))).
    { rewrite inputs_of_app, Hinpf. cbn [app]. exact HallT. }
    assert (Hnctf : noncontradictory_inputs (inputs_of t') (inputs_of (tf ++ tr ++ t))).
    { rewrite inputs_of_app, Hinpf. cbn [app]. exact HncT. }
    econstructor.
    - exact Hsub_out.
    - exact Hwf_out.
    - exact Hci_out.
    - exact (CIH t' s' (tf ++ tr ++ t) sTf Hstar' HstarTf Halltf Hnctf).
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
  Context {equiv_equiv : Equivalence equiv}.
  Context {stmt} (claim : stmt -> list message -> Prop).
  Context (consistent : stmt -> list message -> Prop).
  Local Notation IO_event := (IO_event label message).

  Section steps.
    Context {state1 : Type}.
    Context (step1 : state1 -> IO_event -> state1 -> Prop).
    Context (initial1 : state1).

    Context {state2 : Type}.
    Context (step2 : state2 -> IO_event -> state2 -> Prop).
    Context (initial2 : state2).

    Definition steps_corresp_sound :=
      forall inps output,
        allowed inps ->
        produces step1 initial1 inps output ->
        produces step2 initial2 inps output.

    (*TODO i think Datatypes.List.map2 needs a better name*)
    Context (R : state1 -> list IO_event -> state2 -> list IO_event -> Prop).
    Context (R_outputs_corresp :
              forall s1 t1 s2 t2,
                R s1 t1 s2 t2 ->
                incl (outputs_of t1) (outputs_of t2)).

    Definition weak_sim_output :=
      forall s1 t1 s1' s2 t2 lbl o,
        R s1 t1 s2 t2 ->
        step1 s1 (O_event lbl o) s1' ->
        exists s2' os,
          R s1' (O_event lbl o :: t1) s2' (Datatypes.List.map2 O_event os ++ t2) /\
            star step2 s2 (Datatypes.List.map2 O_event os) s2'.

    Definition weak_sim_input :=
      forall s1 t1 s1' s2 t2 inp,
        R s1 t1 s2 t2 ->
        step1 s1 (I_event inp) s1' ->
        forall s2',
          step2 s2 (I_event inp) s2' ->
          R s1' (I_event inp :: t1) s2' (I_event inp :: t2).

    Definition weak_sim := weak_sim_input /\ weak_sim_output.

    Lemma inputs_of_map2_O_event (os : list (label * list message)) :
      inputs_of (Datatypes.List.map2 (@O_event label message) os) = [].
    Proof.
      unfold Datatypes.List.map2.
      induction os as [|a os IH]; [reflexivity | cbn; exact IH].
    Qed.

    Lemma weak_sim_lift :
      R initial1 [] initial2 [] ->
      input_total step2 ->
      weak_sim ->
      forall t1 ns1,
        star step1 initial1 t1 ns1 ->
        exists t2 ns2,
          star step2 initial2 t2 ns2 /\
          inputs_of t2 = inputs_of t1 /\
          R ns1 t1 ns2 t2.
    Proof.
      intros Hbase Hit2 [Hinput Houtput] t1 ns1 Hstar1.
      induction Hstar1 as [ | t0 s' e s'' Hstar0 IH Hstep].
      - exists [], initial2. split; [constructor|]. split; [reflexivity | exact Hbase].
      - destruct IH as (t2 & ns2 & Hstar2 & Hinpeq & HR).
        destruct e as [inp | lbl o].
        + destruct (Hit2 ns2 inp) as (s2' & Hstep2).
          exists (I_event inp :: t2), s2'.
          split; [eapply star_step; [exact Hstar2 | exact Hstep2]|].
          split.
          * change (inputs_of (I_event inp :: t2)) with (inp :: inputs_of t2).
            change (inputs_of (I_event inp :: t0)) with (inp :: inputs_of t0).
            rewrite Hinpeq. reflexivity.
          * exact (Hinput s' t0 s'' ns2 t2 inp HR Hstep s2' Hstep2).
        + destruct (Houtput s' t0 s'' ns2 t2 lbl o HR Hstep) as (s2' & os & HR' & Hstar2').
          exists (Datatypes.List.map2 O_event os ++ t2), s2'.
          split; [eapply star_app; [exact Hstar2 | exact Hstar2']|].
          split.
          * rewrite inputs_of_app, inputs_of_map2_O_event. exact Hinpeq.
          * exact HR'.
    Qed.

    Lemma weak_sim_correct :
      R initial1 [] initial2 [] ->
      input_total step2 ->
      weak_sim ->
      steps_corresp_sound.
    Proof.
      intros Hbase Hit2 Hws inps output _ Hprod1.
      destruct Hprod1 as (t1 & ns1 & Hstar1 & Hinp1 & Hout1).
      destruct (weak_sim_lift Hbase Hit2 Hws t1 ns1 Hstar1)
        as (t2 & ns2 & Hstar2 & Hinpeq & HR).
      exists t2, ns2. split; [exact Hstar2|]. split.
      - rewrite Hinpeq. exact Hinp1.
      - exact (R_outputs_corresp _ _ _ _ HR output Hout1).
    Qed.

    Definition steps_corresp_sound' :=
      forall ns1 inps o,
        star step1 initial1 (map I_event inps) ns1 ->
        allowed inps ->
        will_output_equiv step1 equiv allowed ns1 (map I_event inps) o ->
        produces step2 initial2 inps o.

    Lemma sound_sound D :
      sound step2 allowed initial2 D ->
      steps_corresp_sound ->
      sound step1 allowed initial1 D.
    Proof.
      intros Hs2 Hcorresp t1 s1 Hstar1 Hall1 o Hout1.
      assert (Hprod1 : produces step1 initial1 (inputs_of t1) o).
      { exists t1, s1. split; [exact Hstar1|]. split; [reflexivity|exact Hout1]. }
      destruct (Hcorresp _ _ Hall1 Hprod1) as (t2 & s2 & Hstar2 & Hinp & Hout2).
      assert (Hall2 : allowed (inputs_of t2)) by (rewrite Hinp; exact Hall1).
      pose proof (Hs2 _ _ Hstar2 Hall2 _ Hout2) as HD.
      rewrite Hinp in HD. exact HD.
    Qed.

    Lemma steps_corresp_sound'_implies_sound :
      input_total step1 ->
      might_implies_will_equiv' step1 equiv claim consistent allowed initial1 ->
      steps_corresp_sound' ->
      steps_corresp_sound.
    Proof.
      intros Hit1 Hmiw1 Hscs' inps o Hallowed Hprod1.
      destruct Hprod1 as (t1 & ns1 & Hstar1 & Hinp1 & Hout1).
      assert (Hall1 : allowed (inputs_of t1)) by (rewrite Hinp1; exact Hallowed).
      destruct (star_recv_map step1 Hit1 (inputs_of t1) initial1) as (ns1' & Hstar1').
      assert (Hall' : allowed (inputs_of (map I_event (inputs_of t1) : list IO_event))).
      {  rewrite inputs_of_map_I_event. exact Hall1. }
      assert (Hincl : consistently_incl equiv claim consistent (inputs_of t1)
                           (inputs_of (map I_event (inputs_of t1) : list IO_event))).
      { rewrite inputs_of_map_I_event. apply (consistently_incl_refl equiv claim consistent). }
      assert (Hnc : noncontradictory_inputs equiv claim consistent allowed (inputs_of t1)
                         (inputs_of (map I_event (inputs_of t1) : list IO_event))).
      { rewrite inputs_of_map_I_event. exact (noncontradictory_refl equiv claim consistent allowed (inputs_of t1) Hall1). }
      pose proof (Hmiw1 t1 ns1 o Hstar1 Hall1 Hout1
                       ns1' (map I_event (inputs_of t1)) Hnc Hincl Hstar1' Hall') as Hwill.
      rewrite <- Hinp1.
      exact (Hscs' ns1' (inputs_of t1) o Hstar1' Hall1 Hwill).
    Qed.

    Fail Fail Definition steps_equiv :=
      exists D,
        (*monotone D /\*)
        described_by step1 equiv allowed initial1 D /\
          described_by step2 equiv allowed initial2 D.
  End steps.
End steps_corresp.
