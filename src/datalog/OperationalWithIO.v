From Stdlib Require Import List PeanoNat Lia Classical_Prop.
From Datalog Require Import Datalog Graph Node Operational List Tactics.
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

  Definition add_input (f : dfact) (s : state) : state :=
    {| known_facts := f :: s.(known_facts); sents := s.(sents) |}.

  Definition initial : state :=
    {| known_facts := []; sents := repeat [] (length p.(non_meta_rules)) |}.

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
    fold_right add_input s l.

  Definition start (inputs : list dfact) : state :=
    {| known_facts := inputs; sents := repeat [] (length p.(non_meta_rules)) |}.

  Lemma start_eq (inputs : list dfact) : load inputs initial = start inputs.
  Proof.
    unfold start, load, initial. induction inputs as [|f l IH]; cbn [fold_right].
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  Lemma Forall3_repeat_seq {A} (Q : A -> list dfact -> nat -> Prop)
    (l : list A) (x : list dfact) (start : nat) :
    (forall a n, Q a x n) -> Forall3 Q l (repeat x (length l)) (seq start (length l)).
  Proof.
    intros HQ. revert start. induction l as [|a l IH]; intros start; cbn; constructor.
    - apply HQ.
    - apply IH.
  Qed.

  Lemma mfc_initial : meta_facts_correct initial.
  Proof.
    unfold meta_facts_correct, initial. cbn [known_facts sents]. rewrite repeat_length.
    apply Forall3_repeat_seq. intros a n R mf_args num Hin. destruct Hin.
  Qed.

  Lemma mfok_initial : meta_facts_ok initial.
  Proof.
    unfold meta_facts_ok, initial. cbn [known_facts sents]. rewrite repeat_length.
    apply Forall3_repeat_seq. intros a n mf_rel mf_args num Hin. destruct Hin.
  Qed.

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

  Lemma Forall2_repeat_l {A B} (P : A -> B -> Prop) (x : A) (y : B) (n : nat) :
    P x y -> Forall2 P (repeat x n) (repeat y n).
  Proof. intros H. induction n; cbn; constructor; auto. Qed.

  Lemma Forall_repeat_l {A} (P : A -> Prop) (x : A) (n : nat) :
    P x -> Forall P (repeat x n).
  Proof. intros H. induction n; cbn; constructor; auto. Qed.

  Lemma list_sum_repeat_0 (n : nat) : list_sum (repeat 0 n) = 0.
  Proof. induction n; cbn; auto. Qed.

  Lemma INV_nil_sane : sane_state [] initial.
  Proof.
    unfold initial. constructor; cbn [known_facts sents].
    - rewrite repeat_length. reflexivity.
    - intros R a num H. destruct H.
    - intros R a n num H. destruct H.
    - intros R a. exists (repeat 0 (length p.(non_meta_rules))), 0, 0.
      split; [| split; [| split]].
      + apply Forall2_repeat_l. constructor.
      + constructor.
      + constructor.
      + rewrite list_sum_repeat_0. reflexivity.
    - intros R HER. split.
      + intros a. apply Forall_repeat_l. constructor.
      + intros a n num H. destruct H.
    - intros g H. destruct H.
  Qed.

  Lemma has_derived_initial (g : fact) : ~ has_derived_datalog_fact initial g.
  Proof.
    unfold has_derived_datalog_fact, initial. cbn [known_facts].
    destruct g as [R args | R mf_args mf_set].
    - intros H. destruct H.
    - destruct (is_input R).
      + intros (num & H & _). destruct H.
      + intros H. destruct (H 0 Hlen) as (num & Hin). destruct Hin.
  Qed.

  Lemma INV_nil_sc : state_correct [] initial.
  Proof.
    intros g (Hd & _). exfalso. eapply has_derived_initial; exact Hd.
  Qed.

  Lemma add_input_sane (l : list dfact) (f : dfact) (s : state) :
    good_input_facts (f :: l) -> sane_state l s ->
    sane_state (f :: l) (add_input f s).
  Proof.
    intros Hgood Hsane.
    pose proof (Forall_inv (proj1 Hgood)) as Hf_in.
    destruct Hsane as [Hlen' Him Ilm Icnt Iir Iik].
    unfold add_input. constructor; cbn [known_facts sents].
    - exact Hlen'.
    - intros R a num H. destruct (in_inv H) as [Heq | Hin].
      + left. exact Heq.
      + right. exact (Him _ _ _ Hin).
    - intros R a n num H. destruct (in_inv H) as [Heq | Hin].
      + exfalso. subst f. cbn in Hf_in. discriminate.
      + exact (Ilm _ _ _ _ Hin).
    - intros R a. destruct (Icnt R a) as (msgs & ni & nk & Hf2 & Hexn_l & Hexn_k & Hsum).
      destruct (classic (dfact_matches R a f)) as [Hm | Hm].
      + exists msgs, (S ni), (S nk). split; [exact Hf2 | split; [| split]].
        * apply Existsn_yes; [exact Hm | exact Hexn_l].
        * apply Existsn_yes; [exact Hm | exact Hexn_k].
        * lia.
      + exists msgs, ni, nk. split; [exact Hf2 | split; [| split]].
        * apply Existsn_no; [exact Hm | exact Hexn_l].
        * apply Existsn_no; [exact Hm | exact Hexn_k].
        * exact Hsum.
    - intros R HER. destruct (Iir R HER) as (Hz & Hnk). split.
      + exact Hz.
      + intros a n num H. destruct (in_inv H) as [Heq | Hin].
        * exfalso. subst f. cbn in Hf_in. discriminate.
        * exact (Hnk a n num Hin).
    - intros g H. destruct (in_inv H) as [Heq | Hin].
      + left. exact Heq.
      + right. exact (Iik g Hin).
  Qed.

  Lemma add_input_knows_incl (l : list dfact) (f : dfact) (s : state) :
    good_input_facts (f :: l) -> sane_state l s ->
    Node.knows_incl R_senders s.(known_facts) (f :: s.(known_facts)).
  Proof.
    intros Hgood Hsane. apply knows_incl_of_submultiset.
    - apply submultiset_cons.
    - pose proof (add_input_sane l f s Hgood Hsane) as Hsane'.
      exact (sane_allowed_inputs _ _ _ _ Hgood Hsane').
  Qed.

  Lemma add_wf_mfc (l : list dfact) (f : dfact) (s : state) :
    good_input_facts (f :: l) -> sane_state l s ->
    meta_facts_correct s -> meta_facts_correct (add_input f s).
  Proof.
    intros Hgood Hsane Hmfc.
    pose proof (add_input_knows_incl l f s Hgood Hsane) as Hincl.
    unfold meta_facts_correct in *. unfold add_input. cbn [known_facts sents].
    eapply Forall3_impl; [| exact Hmfc].
    intros r sent n Hat R mf_args num Hin.
    destruct (Hat R mf_args num Hin) as (mc & mh & hyps & Hin_mr & Hcan & Hknows & Hno).
    exists mc, mh, hyps. split; [exact Hin_mr | split; [exact Hcan | split; [| exact Hno]]].
    eapply Forall_impl; [| exact Hknows]. intros h Hh. apply Hincl. exact Hh.
  Qed.

  Lemma add_wf_mfok (l : list dfact) (f : dfact) (s : state) :
    good_input_facts (f :: l) -> sane_state l s ->
    meta_facts_correct s -> meta_facts_ok s -> meta_facts_ok (add_input f s).
  Proof.
    intros Hgood Hsane Hmfc Hmfok.
    pose proof (add_input_knows_incl l f s Hgood Hsane) as Hincl.
    unfold Operational.meta_facts_correct in Hmfc.
    unfold Operational.meta_facts_ok in Hmfok |- *.
    unfold add_input. cbn [known_facts sents].
    pose proof (Forall3_conj _ _ _ _ _ Hmfc Hmfok) as Hcomb.
    eapply meta_facts_ok_forall3_grow;
      [ exact Hmeta_rules | apply incl_refl | exact Hincl | exact Hcomb ].
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

  Lemma input_matching_known_iff_l (l : list dfact) (s : state) R mf_args :
    sane_state l s -> is_input R = true ->
    forall n, Existsn (dfact_matches R mf_args) n s.(known_facts) <->
              Existsn (dfact_matches R mf_args) n l.
  Proof.
    intros Hsane HER.
    destruct Hsane as [Hlen' Him Ilm Icnt Iir Iik].
    destruct (Icnt R mf_args) as (msgs & ni & nk & Hf2 & Hexn_l & Hexn_k & Hsum).
    assert (Hmsgs0 : list_sum msgs = 0).
    { destruct (Iir R HER) as (Hz & _). specialize (Hz mf_args).
      apply list_sum_zero.
      clear -Hf2 Hz. revert Hz. induction Hf2 as [| a b la lb Hab Hf2' IH]; intros Hz.
      - constructor.
      - inversion Hz as [| ? ? Hz0 Hzs]; subst.
        constructor; [ eapply Existsn_unique; eassumption | apply IH; exact Hzs ]. }
    rewrite Hmsgs0, Nat.add_0_r in Hsum. subst nk.
    intros n. split; intro Hn.
    - rewrite (Existsn_unique _ _ _ _ Hn Hexn_k). exact Hexn_l.
    - rewrite (Existsn_unique _ _ _ _ Hn Hexn_l). exact Hexn_k.
  Qed.

  Lemma add_input_sc (l : list dfact) (f : dfact) (s : state) :
    good_input_facts (f :: l) -> sane_state l s -> state_correct l s ->
    state_correct (f :: l) (add_input f s).
  Proof.
    intros Hgood Hsane Hsc g (Hd & Hmc).
    pose proof (Forall_inv (proj1 Hgood)) as Hf_in.
    pose proof Hsane as Hsane_c. destruct Hsane_c as [_ Him _ _ _ Iik].
    assert (Hweak : forall g', prog_impl rules_of (knows_datalog_fact l) g' ->
                               prog_impl rules_of (knows_datalog_fact (f :: l)) g').
    { intros g' Hp. eapply prog_impl_weaken_hyp; [exact Hp |].
      intros y Hy. apply (knows_datalog_fact_add_input f l y Hgood Hy). }
    destruct g as [R args | R mf_args mf_set].
    - cbv [has_derived_datalog_fact] in Hd. unfold add_input in Hd. cbn [known_facts] in Hd.
      destruct (in_inv Hd) as [Heq | Hin].
      + apply prog_impl_leaf. cbn [Node.knows_datalog_fact]. left. exact Heq.
      + apply Hweak. apply Hsc. split; [exact Hin | exact I].
    - destruct (is_input R) eqn:HER.
      + apply prog_impl_leaf. cbn [Node.knows_datalog_fact].
        cbv [has_derived_datalog_fact] in Hd. rewrite HER in Hd.
        unfold add_input in Hd. cbn [known_facts] in Hd.
        destruct Hd as (num & Hdm_pool & Hexn_pool).
        assert (Hdm_fl : In (meta_dfact R mf_args input_source num) (f :: l)).
        { destruct (in_inv Hdm_pool) as [Heq | Hin].
          - left. exact Heq.
          - right. exact (Him _ _ _ Hin). }
        assert (Hexn_fl : Existsn (dfact_matches R mf_args) num (f :: l)).
        { destruct (classic (dfact_matches R mf_args f)) as [Hfm | Hfm].
          - inversion Hexn_pool as [| | x n' l' Hp' Hrest]; subst; [exfalso; auto |].
            apply Existsn_yes; [exact Hfm |].
            apply (input_matching_known_iff_l l s R mf_args Hsane HER). exact Hrest.
          - apply Existsn_no; [exact Hfm |].
            apply (input_matching_known_iff_l l s R mf_args Hsane HER).
            exact (proj1 (Existsn_cons_no_iff _ f num s.(known_facts) Hfm) Hexn_pool). }
        exists num. split; [| split].
        * rewrite expect_num_R_facts_eq, HER. exact Hdm_fl.
        * exact Hexn_fl.
        * intros nfa Hm. cbv [mf_consistent_state] in Hmc. specialize (Hmc nfa Hm).
          unfold add_input in Hmc. cbn [known_facts] in Hmc. rewrite Hmc.
          assert (Hknl : In (normal_dfact R nfa) s.(known_facts) -> In (normal_dfact R nfa) l).
          { intros Hkn. apply (prog_impl_input_normal_leaf l R nfa HER).
            apply Hsc. split; [exact Hkn | exact I]. }
          split.
          -- intros [Heq | Hin]; [left; exact Heq | right; apply Hknl; exact Hin].
          -- intros [Heq | Hin]; [left; exact Heq | right; apply Iik; exact Hin].
      + apply Hweak. apply Hsc. split.
        * cbv [has_derived_datalog_fact] in Hd |- *. rewrite HER in Hd |- *.
          unfold add_input in Hd. cbn [known_facts] in Hd.
          intros k Hk. destruct (Hd k Hk) as (num & Hin). exists num.
          destruct (in_inv Hin) as [Heq | Hin_k]; [| exact Hin_k].
          exfalso. subst f. cbn in Hf_in. discriminate.
        * cbv [mf_consistent_state] in Hmc |- *. intros nfa Hm. specialize (Hmc nfa Hm).
          unfold add_input in Hmc. cbn [known_facts] in Hmc. rewrite Hmc.
          assert (Hfne : f <> normal_dfact R nfa).
          { intros Heq. subst f. cbn in Hf_in. rewrite HER in Hf_in. discriminate. }
          split.
          -- intros [Heq | Hin]; [exfalso; apply Hfne; exact Heq | exact Hin].
          -- intros Hin. right. exact Hin.
  Qed.

  Lemma load_INV (inputs : list dfact) :
    good_input_facts inputs ->
    sane_state inputs (load inputs initial) /\
    meta_facts_correct (load inputs initial) /\
    meta_facts_ok (load inputs initial) /\
    state_correct inputs (load inputs initial).
  Proof.
    induction inputs as [|f l IH]; intros Hg.
    - change (load [] initial) with initial.
      split; [apply INV_nil_sane |].
      split; [apply mfc_initial |].
      split; [apply mfok_initial | apply INV_nil_sc].
    - change (load (f :: l) initial) with (add_input f (load l initial)).
      pose proof (good_input_facts_tl f l Hg) as Hgl.
      destruct (IH Hgl) as (Hsane & Hmfc & Hmfok & Hsc).
      split; [apply add_input_sane; assumption |].
      split; [eapply add_wf_mfc; eassumption |].
      split; [eapply add_wf_mfok; eassumption | apply add_input_sc; assumption].
  Qed.

  Theorem prog_impl_iff_comp_step (inputs : list dfact) (f : fact) :
    good_input_facts inputs ->
    (prog_impl rules_of (knows_datalog_fact inputs) f <->
     exists s', (comp_step is_input p)^* (start inputs) s' /\
                has_derived_datalog_fact s' f /\ mf_consistent_state s' f).
  Proof.
    intros Hg. rewrite <- start_eq.
    destruct (load_INV inputs Hg) as (Hsane & Hmfc & Hmfok & Hsc).
    split.
    - intros Hprog.
      assert (Hcompl : state_complete inputs (load inputs initial))
        by (apply comp_step_complete; assumption).
      destruct (Hcompl _ Hprog) as (s' & Hsteps & Hderiv).
      assert (Hsc' : state_correct inputs s')
        by (eapply comp_steps_sound; eassumption).
      exists s'. split; [exact Hsteps | split; [exact Hderiv |]].
      eapply correct_impl_consistent; eassumption.
    - intros (s' & Hsteps & Hderiv & Hcons).
      assert (Hsc' : state_correct inputs s')
        by (eapply comp_steps_sound; eassumption).
      apply Hsc'. split; [exact Hderiv | exact Hcons].
  Qed.

End __.
