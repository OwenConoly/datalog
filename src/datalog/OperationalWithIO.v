From Stdlib Require Import List PeanoNat Lia Classical_Prop.
From Datalog Require Import Datalog Node Operational Smallstep List Tactics.
From coqutil Require Import Map.Interface Datatypes.List.
Import ListNotations.

Section __.
  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.
  Context (is_input : rel -> bool).
  Context (p : prog).
  Context (Hmeta_rules : meta_rules_valid (rules_of p)).
  Context (Hp_input : Forall (good_non_meta_rule is_input) p.(non_meta_rules)).
  Context (Hp_meta_input : Forall (good_meta_rule_inputs is_input) p.(meta_rules)).
  Context (Hfin : meta_facts_finite p).
  Context (Hlen : 0 < length p.(non_meta_rules)).

  Local Notation IO_event := (Smallstep.IO_event unit dfact).

  Inductive step : state -> IO_event -> state -> Prop :=
  | step_comp s1 s2 :
    comp_step is_input p s1 s2 ->
    step s1 (O_event tt []) s2
  | step_input s f :
    step s (I_event f) (map (add_waiting_fact f) s)
  | step_output s R args :
    knows_dfact s (normal_dfact R args) ->
    step s (O_event tt [normal_dfact R args]) s.

  Definition empty_rule_state : Operational.node_state :=
    {| known_facts := []; waiting_facts := []; sent_facts := [] |}.

  Definition initial : state := repeat empty_rule_state (length p.(non_meta_rules)).

  Local Notation R_senders := (Operational.R_senders is_input p).
  Local Notation rules_of := (Operational.rules_of p).
  Local Notation knows_datalog_fact := (Node.knows_datalog_fact R_senders).
  Local Notation good_input_facts := (Operational.good_input_facts is_input).
  Local Notation state_correct := (Operational.state_correct is_input p).
  Local Notation state_complete := (Operational.state_complete is_input p).
  Local Notation sane_state := (Operational.sane_state is_input p).
  Local Notation meta_facts_correct := (Operational.meta_facts_correct is_input p).
  Local Notation meta_facts_ok := (Operational.meta_facts_ok is_input p).
  Local Notation has_derived_datalog_fact := (Operational.has_derived_datalog_fact is_input p).

  Definition load (l : list dfact) (s : state) : state :=
    fold_right (fun f s' => map (add_waiting_fact f) s') s l.

  Lemma load_star (l : list dfact) (s : state) :
    star step s (map I_event l) (load l s).
  Proof.
    induction l as [|f l IH]; [apply star_refl|].
    cbn [map load fold_right]. eapply star_step; [exact IH | apply step_input].
  Qed.

  Lemma comp_lift (s s' : state) :
    (comp_step is_input p)^* s s' ->
    exists t, star step s t s' /\ inputs_of t = [] /\ outputs_of t = [].
  Proof.
    intros H. induction H as [ | s0 s1 s2 Hstep Hrest IH].
    - exists []. split; [apply star_refl | split; reflexivity].
    - destruct IH as (t & Hstar & Hin & Hout).
      exists (t ++ [O_event tt []]). split.
      + eapply star_app; [apply star_one; apply step_comp; exact Hstep | exact Hstar].
      + rewrite inputs_of_app, outputs_of_app, Hin, Hout. split; reflexivity.
  Qed.

  Lemma Forall3_map_mid {A B B' C} (g : B -> B') (Q : A -> B' -> C -> Prop)
    (l : list A) (m : list B) (k : list C) :
    Forall3 (fun a b c => Q a (g b) c) l m k -> Forall3 Q l (map g m) k.
  Proof. intros H. induction H; cbn; constructor; assumption. Qed.

  Lemma Forall3_repeat_seq {A} (Q : A -> node_state -> nat -> Prop)
    (l : list A) (x : node_state) (start : nat) :
    (forall a n, Q a x n) -> Forall3 Q l (repeat x (length l)) (seq start (length l)).
  Proof.
    intros HQ. revert start. induction l as [|a l IH]; intros start; cbn; constructor.
    - apply HQ.
    - apply IH.
  Qed.

  Lemma mfc_initial : meta_facts_correct initial.
  Proof.
    unfold meta_facts_correct, initial. rewrite repeat_length.
    apply Forall3_repeat_seq. intros a n R mf_args num Hin. destruct Hin.
  Qed.

  Lemma mfok_initial : meta_facts_ok initial.
  Proof.
    unfold meta_facts_ok, initial. rewrite repeat_length.
    apply Forall3_repeat_seq. intros a n mf_rel mf_args num Hin. destruct Hin.
  Qed.

  Lemma add_wf_mfc (f : dfact) (s : state) :
    meta_facts_correct s -> meta_facts_correct (map (add_waiting_fact f) s).
  Proof.
    unfold meta_facts_correct. rewrite length_map. intros H.
    apply Forall3_map_mid. exact H.
  Qed.

  Lemma add_wf_mfok (f : dfact) (s : state) :
    meta_facts_ok s -> meta_facts_ok (map (add_waiting_fact f) s).
  Proof.
    unfold meta_facts_ok. rewrite length_map. intros H.
    apply Forall3_map_mid. exact H.
  Qed.

  Definition INV (t : list IO_event) (s : state) : Prop :=
    sane_state (inputs_of t) s /\ meta_facts_correct s /\ meta_facts_ok s /\
    state_correct (inputs_of t) s.

  Lemma Existsn_tl {A} (P : A -> Prop) (x : A) (n : nat) (l : list A) :
    Existsn P n (x :: l) -> exists m, m <= n /\ Existsn P m l.
  Proof.
    intros H. inversion H; subst.
    - exists n. split; [lia | assumption].
    - exists n0. split; [lia | assumption].
  Qed.

  Lemma good_input_facts_tl (f : dfact) (l : list dfact) :
    good_input_facts (f :: l) -> good_input_facts l.
  Proof.
    intros [Hall Hmeta]. split.
    - inversion Hall; assumption.
    - intros R a num Hin.
      destruct (Hmeta R a num (or_intror Hin)) as (Huniq & num' & Hle & Hex).
      split.
      + intros num0 Hin0. apply Huniq. right. exact Hin0.
      + apply Existsn_tl in Hex. destruct Hex as (m & Hm & Hexm).
        exists m. split; [lia | exact Hexm].
  Qed.

  Lemma knows_dfact_initial (g : dfact) : ~ knows_dfact initial g.
  Proof.
    unfold knows_dfact, initial. intros H. apply Exists_exists in H.
    destruct H as (rs & Hin & Hrhd). apply repeat_spec in Hin. subst rs.
    destruct Hrhd as [[] | []].
  Qed.

  Lemma Forall2_repeat_l {A B} (P : A -> B -> Prop) (x : A) (y : B) (n : nat) :
    P x y -> Forall2 P (repeat x n) (repeat y n).
  Proof. intros H. induction n; cbn; constructor; auto. Qed.

  Lemma Forall_repeat_l {A} (P : A -> Prop) (x : A) (n : nat) :
    P x -> Forall P (repeat x n).
  Proof. intros H. induction n; cbn; constructor; auto. Qed.

  Lemma list_sum_repeat_0 (n : nat) : list_sum (repeat 0 n) = 0.
  Proof. induction n; cbn; auto. Qed.

  Lemma INV_nil : INV [] initial.
  Proof.
    unfold INV. cbn [inputs_of flat_map].
    split; [| split; [apply mfc_initial | split; [apply mfok_initial |]]].
    - constructor.
      + unfold initial. rewrite repeat_length. reflexivity.
      + intros R a num H. exfalso. eapply knows_dfact_initial; exact H.
      + intros R a n num H. exfalso. eapply knows_dfact_initial; exact H.
      + intros f H. exfalso. eapply knows_dfact_initial; exact H.
      + intros R a. exists (repeat 0 (length initial)), 0. split; [| split].
        * unfold initial. rewrite !repeat_length. apply Forall2_repeat_l. cbn. constructor.
        * constructor.
        * apply Forall_repeat_l. exists 0, 0. cbn.
          split; [constructor | split; [constructor |]].
          rewrite list_sum_repeat_0. reflexivity.
      + intros R Hin. split.
        * intros a. apply Forall_repeat_l. cbn. constructor.
        * intros a n num H. eapply knows_dfact_initial; exact H.
      + intros f H. destruct H.
    - intros f (Hderiv & _). exfalso. destruct f as [R args | R a set].
      + eapply knows_dfact_initial; exact Hderiv.
      + cbn in Hderiv. destruct (is_input R).
        * apply Exists_exists in Hderiv. destruct Hderiv as (rs & Hin & num & Hrh & _).
          eapply knows_dfact_initial. apply Exists_exists. exists rs. split; [exact Hin | exact Hrh].
        * specialize (Hderiv 0 Hlen). destruct Hderiv as (num & Hk).
          eapply knows_dfact_initial; exact Hk.
  Qed.

  Lemma knows_add_self (f : dfact) (s : state) :
    s <> [] -> knows_dfact (map (add_waiting_fact f) s) f.
  Proof.
    destruct s as [|rs0 rest]; [congruence|]. intros _.
    cbn [map]. apply Exists_cons_hd.
    unfold rule_has_dfact, add_waiting_fact. cbn. right. left. reflexivity.
  Qed.

  Lemma knows_add_iff (f : dfact) (s : state) (g : dfact) :
    s <> [] ->
    (knows_dfact (map (add_waiting_fact f) s) g <-> g = f \/ knows_dfact s g).
  Proof.
    intros Hne. split.
    - apply knows_dfact_add_waiting.
    - intros [-> | Hk].
      + apply knows_add_self; exact Hne.
      + apply knows_dfact_add_waiting_mono; exact Hk.
  Qed.

  Lemma s_nonempty (l : list dfact) (s : state) : sane_state l s -> s <> [].
  Proof.
    intros Hsane Heq. destruct Hsane as [Hl _ _ _ _ _ _].
    rewrite Heq in Hl. cbn in Hl. lia.
  Qed.

  Lemma add_input_sane (l : list dfact) (f : dfact) (s : state) :
    good_input_facts (f :: l) -> sane_state l s ->
    sane_state (f :: l) (map (add_waiting_fact f) s).
  Proof.
    intros Hgood Hsane.
    pose proof (s_nonempty _ _ Hsane) as Hne.
    destruct Hgood as [Hall _].
    pose proof (Forall_inv Hall) as Hf_in.
    destruct Hsane as [Hlen' Him Ilm Irh Icnt Iir Iik].
    constructor.
    - rewrite length_map. exact Hlen'.
    - intros R a num H. apply (knows_add_iff f s _ Hne) in H. destruct H as [Heq | Hk].
      + rewrite <- Heq. apply in_eq.
      + apply in_cons. apply Him. exact Hk.
    - intros R a n num H. apply (knows_add_iff f s _ Hne) in H. destruct H as [Heq | Hk].
      + exfalso. rewrite <- Heq in Hf_in. cbn in Hf_in. discriminate.
      + specialize (Ilm R a n num Hk). unfold nth_sat in *. rewrite nth_error_map.
        destruct (nth_error s n); exact Ilm.
    - intros g H. apply (knows_add_iff f s _ Hne) in H. apply Forall_map.
      destruct H as [Heq | Hk].
      + apply Forall_forall. intros rs _.
        unfold rule_has_dfact, add_waiting_fact. cbn. right. rewrite Heq. apply in_eq.
      + eapply Forall_impl; [| exact (Irh g Hk)]. intros rs Hrh.
        unfold rule_has_dfact, add_waiting_fact in *. cbn in *.
        destruct Hrh as [Hk'|Hw]; [left; exact Hk' | right; apply in_cons; exact Hw].
    - intros R a. destruct (Icnt R a) as (ms & ni & HF2 & Hexl & HFa).
      destruct (classic (dfact_matches R a f)) as [Hm | Hm].
      + exists ms, (S ni). split; [| split].
        * rewrite <- Forall2_map_l. exact HF2.
        * apply Existsn_yes; [exact Hm | exact Hexl].
        * apply Forall_map. eapply Forall_impl; [| exact HFa].
          intros rs (nk & nw & Hnk & Hnw & Hsum). exists nk, (S nw).
          cbn [add_waiting_fact known_facts waiting_facts].
          split; [exact Hnk|]. split; [apply Existsn_yes; [exact Hm | exact Hnw] | lia].
      + exists ms, ni. split; [| split].
        * rewrite <- Forall2_map_l. exact HF2.
        * apply Existsn_no; [exact Hm | exact Hexl].
        * apply Forall_map. eapply Forall_impl; [| exact HFa].
          intros rs (nk & nw & Hnk & Hnw & Hsum). exists nk, nw.
          cbn [add_waiting_fact known_facts waiting_facts].
          split; [exact Hnk|]. split; [apply Existsn_no; [exact Hm | exact Hnw] | exact Hsum].
    - intros R Hinp. destruct (Iir R Hinp) as [Hsent Hnk]. split.
      + intros a. apply Forall_map. exact (Hsent a).
      + intros a n num Hbad. apply (knows_add_iff f s _ Hne) in Hbad.
        destruct Hbad as [Heq | Hk].
        * rewrite <- Heq in Hf_in. cbn in Hf_in. discriminate.
        * exact (Hnk a n num Hk).
    - intros g Hin. destruct Hin as [Heq | Hin].
      + subst g. apply knows_add_self. exact Hne.
      + apply knows_dfact_add_waiting_mono. apply Iik. exact Hin.
  Qed.

  Lemma non_meta_rule_impl_not_input (r : non_meta_rule) R nfa hyps :
    good_non_meta_rule is_input r -> non_meta_rule_impl (rule_of r) R nfa hyps ->
    is_input R = false.
  Proof.
    intros Hgood Himpl. destruct r as [cs hs | concl agg hyp]; simpl in Himpl, Hgood.
    - invert Himpl.
      match goal with H : Exists _ _ |- _ =>
        apply Exists_exists in H; destruct H as (c & Hin_c & Hint) end.
      cbv [interp_clause] in Hint. destruct Hint as (nfargs & _ & Heq). injection Heq as -> ->.
      rewrite Forall_forall in Hgood. apply Hgood; exact Hin_c.
    - invert Himpl. exact Hgood.
  Qed.

  Lemma prog_impl_input_normal_leaf (inputs : list dfact) R nfa :
    is_input R = true ->
    prog_impl rules_of (knows_datalog_fact inputs) (normal_fact R nfa) ->
    In (normal_dfact R nfa) inputs.
  Proof.
    intros HER Himpl. invert Himpl.
    - exact H.
    - exfalso. apply Exists_exists in H. destruct H as (r & Hin_r & Hri).
      cbv [rules_of] in Hin_r. apply in_app_or in Hin_r. destruct Hin_r as [Hin_meta | Hin_nm].
      + apply in_map_iff in Hin_meta. destruct Hin_meta as ((c, h) & Heq & _). subst r.
        invert Hri. match goal with H : non_meta_rule_impl _ _ _ _ |- _ => invert H end.
      + apply in_map_iff in Hin_nm. destruct Hin_nm as (nmr & Heq_r & Hin_nmr). subst r.
        invert Hri.
        match goal with H : non_meta_rule_impl _ _ _ _ |- _ =>
          assert (is_input R = false) by
            (eapply non_meta_rule_impl_not_input;
             [ rewrite Forall_forall in Hp_input; apply Hp_input; exact Hin_nmr | exact H ]) end.
        congruence.
  Qed.

  Lemma knows_datalog_fact_add_input (f : dfact) (l : list dfact) (h : fact) :
    good_input_facts (f :: l) -> knows_datalog_fact l h -> knows_datalog_fact (f :: l) h.
  Proof.
    intros Hgood Hk. pose proof Hgood as [Hall Hmeta].
    pose proof (Forall_inv Hall) as Hf_in.
    destruct h as [R args | R a mf_set].
    - cbn [Node.knows_datalog_fact] in *. apply in_cons. exact Hk.
    - cbn [Node.knows_datalog_fact] in *. destruct Hk as (num & Hexp & Hexn & Hiff).
      assert (Hnm : ~ dfact_matches R a f).
      { intros (nfa & Hfeq & Hmatch). subst f. cbn in Hf_in.
        rewrite expect_num_R_facts_eq, Hf_in in Hexp.
        destruct (Hmeta R a num) as (_ & num' & Hle & Hexn'); [right; exact Hexp |].
        assert (HexnS : Existsn (dfact_matches R a) (S num) (normal_dfact R nfa :: l)).
        { apply Existsn_yes; [exists nfa; split; [reflexivity | exact Hmatch] | exact Hexn]. }
        pose proof (Existsn_unique _ _ _ _ Hexn' HexnS). lia. }
      exists num. split; [| split].
      + rewrite expect_num_R_facts_eq in Hexp |- *. destruct (is_input R).
        * apply in_cons. exact Hexp.
        * destruct Hexp as (ems & Hf2 & Hsum). exists ems. split; [| exact Hsum].
          eapply Forall2_impl; [exact Hf2 |]. intros n0 em0 Hin0. apply in_cons. exact Hin0.
      + apply Existsn_no; [exact Hnm | exact Hexn].
      + intros nfa Hm. split.
        * intro Hset. apply in_cons. exact (proj1 (Hiff nfa Hm) Hset).
        * intros [Hfeq | Hin2].
          -- exfalso. apply Hnm. exists nfa. split; [exact Hfeq | exact Hm].
          -- exact (proj2 (Hiff nfa Hm) Hin2).
  Qed.

  Lemma add_input_sc (l : list dfact) (f : dfact) (s : state) :
    good_input_facts (f :: l) -> sane_state l s -> state_correct l s ->
    state_correct (f :: l) (map (add_waiting_fact f) s).
  Proof.
    intros Hgood Hsane Hsc g (Hd & Hmc).
    pose proof (s_nonempty _ _ Hsane) as Hne.
    pose proof Hgood as [Hall _]. pose proof (Forall_inv Hall) as Hf_in.
    (* weaken a base(l) derivation to base(f::l) *)
    assert (Hweak : forall g', prog_impl rules_of (knows_datalog_fact l) g' ->
                               prog_impl rules_of (knows_datalog_fact (f :: l)) g').
    { intros g' Hp. eapply prog_impl_weaken_hyp; [exact Hp |].
      intros y Hy. apply (knows_datalog_fact_add_input f l y Hgood Hy). }
    destruct g as [R args | R a mf_set].
    - (* normal g *)
      cbv [has_derived_datalog_fact] in Hd. apply (knows_add_iff f s _ Hne) in Hd.
      destruct Hd as [Heq | Hk].
      + apply prog_impl_leaf. cbn [Node.knows_datalog_fact]. rewrite <- Heq. apply in_eq.
      + apply Hweak. apply Hsc. split; [exact Hk | exact I].
    - (* meta g *)
      destruct (is_input R) eqn:HER.
      + (* input R: the state's aggregation is complete; build a knows_datalog_fact leaf *)
        apply prog_impl_leaf.
        assert (Hkn_in : forall nfa, knows_dfact s (normal_dfact R nfa) -> In (normal_dfact R nfa) l).
        { intros nfa Hkn. apply (prog_impl_input_normal_leaf l R nfa HER).
          apply Hsc. split; [exact Hkn | exact I]. }
        pose proof (add_input_sane l f s Hgood Hsane) as Hsane'.
        pose proof Hsane as Hs0. destruct Hs0 as [_ Him0 _ _ _ _ Iik0].
        pose proof Hsane' as Hs1. destruct Hs1 as [_ _ _ _ Icnt1 Iir1 _].
        cbv [has_derived_datalog_fact] in Hd. rewrite HER in Hd.
        apply Exists_exists in Hd. destruct Hd as (rs' & Hin' & num & Hrh' & Hexn').
        apply in_map_iff in Hin'. destruct Hin' as (rs & Heq_rs & Hin_rs). subst rs'.
        cbn [add_waiting_fact known_facts waiting_facts] in Hrh', Hexn'.
        assert (Hdm : In (meta_dfact R a None num) (f :: l)).
        { destruct Hrh' as [Hk | Hw].
          - right. apply Him0. apply Exists_exists. exists rs. split; [exact Hin_rs | left; exact Hk].
          - destruct Hw as [Heq | Hw].
            + left. exact Heq.
            + right. apply Him0. apply Exists_exists. exists rs. split; [exact Hin_rs | right; exact Hw]. }
        cbn [Node.knows_datalog_fact]. exists num. split; [| split].
        * rewrite expect_num_R_facts_eq, HER. exact Hdm.
        * destruct (Icnt1 R a) as (msgs' & num_inp' & Hf2' & Hexn_inp' & Hforall').
          destruct (Iir1 R HER) as (Hsent0' & _). specialize (Hsent0' a).
          assert (Hsum0 : list_sum msgs' = 0).
          { enough (Forall (eq 0) msgs') as HF by
              (clear -HF; induction HF; simpl; [reflexivity | subst; assumption]).
            clear -Hf2' Hsent0'. revert Hsent0'.
            induction Hf2' as [| x y xs ys H Hf2'' IH]; intros Hsent0'.
            - constructor.
            - inversion Hsent0' as [| ? ? Hqx Hqxs]; subst. constructor.
              + symmetry. eapply Existsn_unique; [exact H | exact Hqx].
              + apply IH. exact Hqxs. }
          rewrite Forall_forall in Hforall'.
          specialize (Hforall' (add_waiting_fact f rs) (in_map _ _ _ Hin_rs)).
          destruct Hforall' as (nk & nw & Hnk & Hnw & Hsum).
          cbn [add_waiting_fact known_facts waiting_facts] in Hnk, Hnw.
          rewrite Hsum0, Nat.add_0_r in Hsum.
          pose proof (Existsn_app _ _ _ _ _ Hnk Hnw) as Happ.
          pose proof (Existsn_unique _ _ _ _ Hexn' Happ) as Hnn.
          assert (Hnum : num = num_inp') by (rewrite Hnn; exact Hsum).
          rewrite Hnum. exact Hexn_inp'.
        * intros nfa Hm. cbv [mf_consistent_state] in Hmc. specialize (Hmc nfa Hm).
          rewrite Hmc, (knows_add_iff f s (normal_dfact R nfa) Hne). cbn [In]. split.
          -- intros [Heq | Hk]; [left; symmetry; exact Heq | right; apply Hkn_in; exact Hk].
          -- intros [Heq | Hin]; [left; symmetry; exact Heq | right; apply Iik0; exact Hin].
      + (* non-input R: fired/input f is irrelevant, reduce to base(l) via Hsc *)
        apply Hweak. apply Hsc. split.
        * cbv [has_derived_datalog_fact] in Hd |- *. rewrite HER in Hd |- *.
          intros k Hk. specialize (Hd k Hk). destruct Hd as (num & Hkn). exists num.
          apply (knows_add_iff f s _ Hne) in Hkn. destruct Hkn as [Heq | Hk_s]; [| exact Hk_s].
          exfalso. rewrite <- Heq in Hf_in. cbn in Hf_in. discriminate.
        * cbv [mf_consistent_state] in Hmc |- *. intros nfa Hm. specialize (Hmc nfa Hm).
          rewrite Hmc. split.
          -- intro H. apply (knows_add_iff f s _ Hne) in H. destruct H as [Heq | Hk_s]; [| exact Hk_s].
             exfalso. rewrite <- Heq in Hf_in. cbn in Hf_in. rewrite HER in Hf_in. discriminate.
          -- apply knows_dfact_add_waiting_mono.
  Qed.

  Lemma step_preserves_INV (t0 : list IO_event) (e : IO_event) (s1 s2 : state) :
    good_input_facts (inputs_of (e :: t0)) ->
    step s1 e s2 -> INV t0 s1 -> INV (e :: t0) s2.
  Proof.
    intros Hg Hstep (Hsane & Hmfc & Hmfok & Hsc).
    destruct Hstep as [a b Hc | a f | a R args Hk]; unfold INV in *;
      cbn [inputs_of flat_map] in Hg |- *.
    - split; [eapply step_preserves_sane; eassumption|].
      split; [eapply step_preserves_mfs_correct; eassumption|].
      split; [eapply step_preserves_meta_facts_ok; eassumption|].
      eapply comp_step_sound; eassumption.
    - split; [apply add_input_sane; assumption|].
      split; [apply add_wf_mfc; exact Hmfc|].
      split; [apply add_wf_mfok; exact Hmfok|].
      apply add_input_sc; assumption.
    - split; [exact Hsane|]. split; [exact Hmfc|]. split; [exact Hmfok|]. exact Hsc.
  Qed.

  Lemma star_INV (t : list IO_event) (s : state) :
    good_input_facts (inputs_of t) -> star step initial t s -> INV t s.
  Proof.
    intros Hg Hstar. revert Hg.
    induction Hstar as [ | t0 s' e s'' Hstar IH Hstep]; intros Hg.
    - apply INV_nil.
    - eapply step_preserves_INV; [exact Hg | exact Hstep |].
      apply IH. destruct e as [f | lbl outs]; cbn [inputs_of flat_map] in Hg.
      + eapply good_input_facts_tl; exact Hg.
      + exact Hg.
  Qed.

  Lemma step_length (s : state) (e : IO_event) (s' : state) :
    length s = length p.(non_meta_rules) -> step s e s' ->
    length s' = length p.(non_meta_rules).
  Proof.
    intros Hln Hstep. destruct Hstep as [a b Hc | a f | a R args Hk].
    - rewrite (comp_step_length _ _ _ _ Hln Hc). exact Hln.
    - rewrite length_map. exact Hln.
    - exact Hln.
  Qed.

  Lemma step_knows_mono (s : state) (e : IO_event) (s' : state) (g : dfact) :
    length s = length p.(non_meta_rules) -> step s e s' ->
    knows_dfact s g -> knows_dfact s' g.
  Proof.
    intros Hln Hstep Hk. destruct Hstep as [a b Hc | a f | a R args Hkk].
    - eapply comp_step_knows_mono_len; eassumption.
    - apply knows_dfact_add_waiting_mono. exact Hk.
    - exact Hk.
  Qed.

  Lemma star_length (s ns : state) (t : list IO_event) :
    length s = length p.(non_meta_rules) -> star step s t ns ->
    length ns = length p.(non_meta_rules).
  Proof.
    intros Hln Hstar. induction Hstar as [ | t0 s' e s'' Hstar IH Hstep].
    - exact Hln.
    - eapply step_length; [exact IH | exact Hstep].
  Qed.

  Lemma output_known (s ns : state) (t : list IO_event) (g : dfact) :
    length s = length p.(non_meta_rules) ->
    star step s t ns -> In g (outputs_of t) -> knows_dfact ns g.
  Proof.
    intros Hln Hstar. revert g.
    induction Hstar as [ | t0 s' e s'' Hstar IH Hstep]; intros g Hin.
    - destruct Hin.
    - cbn [outputs_of flat_map] in Hin. rewrite in_app_iff in Hin.
      destruct Hin as [Hin_e | Hin_t0].
      + destruct Hstep as [a b Hc | a f | a R args Hk]; cbn in Hin_e.
        * destruct Hin_e.
        * destruct Hin_e.
        * destruct Hin_e as [<- | []]. exact Hk.
      + eapply step_knows_mono; [ | exact Hstep | exact (IH g Hin_t0)].
        eapply star_length; [exact Hln | exact Hstar].
  Qed.

  Lemma output_known_final (t : list IO_event) (ns : state) (g : dfact) :
    good_input_facts (inputs_of t) ->
    star step initial t ns -> In g (outputs_of t) -> knows_dfact ns g.
  Proof.
    intros _ Hstar Hin. eapply output_known; [ | exact Hstar | exact Hin].
    unfold initial. rewrite repeat_length. reflexivity.
  Qed.

  Theorem produces_sound (inputs : list dfact) (R : rel) (args : list T) :
    good_input_facts inputs ->
    produces step initial inputs (normal_dfact R args) ->
    prog_impl rules_of (knows_datalog_fact inputs) (normal_fact R args).
  Proof.
    intros Hg (t & ns & Hstar & Hinp & Hout).
    assert (Hgt : good_input_facts (inputs_of t)) by (rewrite Hinp; exact Hg).
    pose proof (star_INV t ns Hgt Hstar) as (Hsane & _ & _ & Hsc).
    rewrite Hinp in Hsc.
    assert (Hk : knows_dfact ns (normal_dfact R args))
      by (eapply output_known_final; eassumption).
    apply Hsc. split; [exact Hk | exact I].
  Qed.

  Theorem produces_complete (inputs : list dfact) (R : rel) (args : list T) :
    good_input_facts inputs ->
    prog_impl rules_of (knows_datalog_fact inputs) (normal_fact R args) ->
    produces step initial inputs (normal_dfact R args).
  Proof.
    intros Hg Hprog.
    pose proof (load_star inputs initial) as Hload.
    assert (Hgio : good_input_facts (inputs_of (map I_event inputs : list IO_event)))
      by (rewrite inputs_of_map_I_event; exact Hg).
    pose proof (star_INV _ _ Hgio Hload) as (Hsane & Hmfc & Hmfok & Hsc).
    rewrite inputs_of_map_I_event in Hsane, Hsc.
    assert (Hcompl : state_complete inputs (load inputs initial))
      by (apply comp_step_complete; assumption).
    destruct (Hcompl (normal_fact R args) Hprog) as (s' & Hcomp & Hderiv).
    destruct (comp_lift _ _ Hcomp) as (tc & Htc & Htcin & Htcout).
    exists (O_event tt [normal_dfact R args] :: tc ++ map I_event inputs), s'.
    split; [| split].
    - eapply star_step.
      + eapply star_app; [exact Hload | exact Htc].
      + apply step_output. exact Hderiv.
    - replace (inputs_of (O_event tt [normal_dfact R args] :: tc ++ map I_event inputs))
        with (inputs_of (tc ++ map I_event inputs)) by reflexivity.
      rewrite inputs_of_app, Htcin, inputs_of_map_I_event. reflexivity.
    - replace (outputs_of (O_event tt [normal_dfact R args] :: tc ++ map I_event inputs))
        with (normal_dfact R args :: outputs_of (tc ++ map I_event inputs)) by reflexivity.
      apply in_eq.
  Qed.

End __.
