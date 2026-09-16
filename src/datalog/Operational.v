From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Classical_Prop.
From Stdlib Require Import Relations.Relation_Operators Relations.Operators_Properties.

From Datalog Require Import Map Tactics List Pftree Datalog Node Default.

From coqutil Require Import Map.Interface Map.Properties Tactics Tactics.fwd Datatypes.List Eqb.

Import ListNotations.
Import node.

Notation "R ^*" := (clos_refl_trans_1n _ R) (format "R ^*").
#[global] Hint Constructors clos_refl_trans_1n : core.

Section __.
  Context `{params : datalog_params}.
  Context {rule_eqb : Eqb rule} {rule_eqb_ok : Eqb_ok rule_eqb}.

  Variant op_source :=
  | from_rule (r : rule)
  | from_input.

  #[local] Instance sender_label : sender_labelT := op_source.

  Context {sent_map : map.map rule (list message)} {sent_map_ok : map.ok sent_map}.

  Record state := { known_facts : list message; sents : sent_map }.

  Context (is_input : rel -> bool).

  Context (p : program).

  Definition sender_rules : list rule := dedup eqb p.(program.rules).

  Lemma In_sender_rules r : In r p.(program.rules) -> In r sender_rules.
  Proof. exact (proj1 (dedup_preserves_In _ r)). Qed.

  Lemma sender_rules_In r : In r sender_rules -> In r p.(program.rules).
  Proof. exact (proj2 (dedup_preserves_In _ r)). Qed.

  Definition R_senders : rel -> list op_source :=
    fun R => if is_input R then [from_input] else map from_rule sender_rules.

  Local Abbreviation expects_num_facts := (node.expects_num_facts R_senders).
  Local Abbreviation knows_fact := (node.knows_fact R_senders).
  Local Abbreviation knows_meta_fact := (node.knows_meta_fact R_senders).
  Local Abbreviation can_deduce_normal_fact := (node.can_deduce_normal_fact R_senders).
  Local Abbreviation allowed_inputs := (node.allowed_inputs R_senders).
  Local Abbreviation knows_incl := (node.knows_incl R_senders).

  (* [expects_num_facts] with the new [R_senders] recovers its old [is_input] form:
     for input relations, a single [None]-declaration; otherwise one [Some k] count
     per node. *)
  Lemma expects_num_facts_eq pat known num :
    expects_num_facts known pat num <->
    (if is_input pat.(fact_pattern.rel)
     then In (message.done_with pat from_input num) known
     else exists expected_msgss,
       Forall2 (fun r expected_msgs =>
                  In (message.done_with pat (from_rule r) expected_msgs) known)
               sender_rules expected_msgss /\
       num = list_sum expected_msgss).
  Proof.
    unfold node.expects_num_facts, R_senders.
    destruct (is_input pat.(fact_pattern.rel)); cbn.
    - split.
      + intros (ems & HF2 & Hsum).
        inversion HF2 as [| a e la lb Ha Hlb]; subst.
        inversion Hlb; subst. cbn. rewrite Nat.add_0_r. exact Ha.
      + intros HIn. exists [num]. split; [| cbn; lia].
        constructor; [exact HIn | constructor].
    - split; intros (ems & HF2 & Hsum); exists ems; split; try assumption.
      + rewrite <- Forall2_map_l in HF2. exact HF2.
      + rewrite <- Forall2_map_l. exact HF2.
  Qed.

  Definition meta_facts_correct_at_rule (mrs : list meta_rule) known r sent :=
    forall pat num,
      In (message.done_with pat (from_rule r) num) sent ->
      exists mr mhyps,
        In mr mrs /\
          Existsn (message.matches pat) num sent /\
          meta_rule.pattern_interp mr pat (map meta_fact.pattern mhyps) /\
          Forall (knows_meta_fact known) mhyps /\
          Forall (fun mh => mh.(meta_fact.pattern) <> pat) mhyps.

  Definition meta_facts_correct (s : state) :=
    forall r, In r p.(program.rules) ->
      meta_facts_correct_at_rule p.(program.meta_rules) s.(known_facts) r
        (get_or_default s.(sents) r).

  (*[node.saturated] specialized to the one rule of one positional node*)
  Definition ok_to_deduce (r : rule) known sent (pat : fact_pattern) :=
    forall nf,
      can_deduce_normal_fact r known nf ->
      fact_pattern.matches pat nf ->
      In (message.normal nf) sent.

  Definition meta_facts_ok_at_rule known r sent :=
    forall pat num,
      In (message.done_with pat (from_rule r) num) sent ->
      ok_to_deduce r known sent pat.

  Definition meta_facts_ok (s : state) :=
    forall r, In r p.(program.rules) ->
      meta_facts_ok_at_rule s.(known_facts) r (get_or_default s.(sents) r).

  Definition add_known_fact f (s : state) :=
    {| known_facts := f :: s.(known_facts); sents := s.(sents) |}.

  (*the node for rule [r] runs [r] plus all the meta rules*)
  Definition node_prog (r : rule) : program :=
    {| program.rules := [r]; program.meta_rules := p.(program.meta_rules) |}.

  (* The effect of node [r] firing fact [f]: given the global [known] pool and
     the node's sent list [sent]. *)
  Definition fire_at_rule (r : rule) known (sent : list message) (f : message) : Prop :=
    node.can_deduce R_senders (node_prog r) (from_rule r)
      {| node.state.known := known; node.state.sent := sent |} f.

  Inductive comp_step : state -> state -> Prop :=
  | fire_rule new_fact s r :
    In r p.(program.rules) ->
    fire_at_rule r s.(known_facts) (get_or_default s.(sents) r) new_fact ->
    comp_step s {| known_facts := new_fact :: s.(known_facts);
                  sents := mupd_with_default (cons new_fact) s.(sents) r |}.

  Definition is_input_fact (f : message) :=
    match f with
    | message.normal nf => is_input nf.(normal_fact.rel)
    | message.done_with pat from_input _ => is_input pat.(fact_pattern.rel)
    | message.done_with _ (from_rule _) _ => false
    end.

  Context (Hmeta_rules : program.meta_rules_valid p).

  Context (Hp_good : Forall (fun R => is_input R = false) (program.concl_rels p)).

  Lemma concl_rel_not_input R :
    In R (program.concl_rels p) -> is_input R = false.
  Proof. rewrite Forall_forall in Hp_good. auto. Qed.

  (* Propagation of meta-fact finiteness: analog of SimpleDataflow.v:2505
     [meta_facts_finite].  We constrain the matching nf_args range only,
     because that is all the meta-fact semantics actually pin down (the
     S predicate is opaque on non-matching args).  This makes the leaf
     case provable from finiteness of the inputs list. *)
  Definition meta_facts_finite :=
    forall Q,
      (forall mf, Q (fact.meta mf) ->
                  exists l, forall args,
                    Forall2 value_pattern.matches
                      mf.(meta_fact.pattern).(fact_pattern.args) args ->
                    mf.(meta_fact.set) args -> In args l) ->
      forall mf, program.interp p Q (fact.meta mf) ->
                 exists l, forall args,
                   Forall2 value_pattern.matches
                     mf.(meta_fact.pattern).(fact_pattern.args) args ->
                   mf.(meta_fact.set) args -> In args l.

  Context (Hmeta_finite : meta_facts_finite).

  Definition good_input_facts input_facts :=
    Forall (fun f => is_input_fact f = true) input_facts /\
      (forall pat num,
          In (message.done_with pat from_input num) input_facts ->
          (forall num0, In (message.done_with pat from_input num0) input_facts -> num0 = num) /\
            exists num',
              num' <= num /\
                Existsn (message.matches pat) num' input_facts).

  Record sane_state {input_facts : list message} {s : state} : Prop := {
    sane_input_meta :
      forall pat num,
        In (message.done_with pat from_input num) s.(known_facts) ->
        In (message.done_with pat from_input num) input_facts;
    sane_local_meta :
      forall pat r num,
          In (message.done_with pat (from_rule r) num) s.(known_facts) ->
          Existsn (message.matches pat) num (get_or_default s.(sents) r) /\
          In (message.done_with pat (from_rule r) num) (get_or_default s.(sents) r);
    sane_count :
      forall pat,
        exists msgs_sents num_inp num_known,
          Forall2 (fun r m => Existsn (message.matches pat) m (get_or_default s.(sents) r))
                  sender_rules msgs_sents /\
            Existsn (message.matches pat) num_inp input_facts /\
            Existsn (message.matches pat) num_known s.(known_facts) /\
            num_known = num_inp + list_sum msgs_sents;
    sane_input_rel :
      forall pat,
          is_input pat.(fact_pattern.rel) = true ->
          Forall (fun sent => Existsn (message.matches pat) O sent) (values s.(sents)) /\
            (forall r num, ~In (message.done_with pat (from_rule r) num) s.(known_facts));
    sane_inputs_known :
      forall f, In f input_facts -> In f s.(known_facts);
  }.

  Arguments sane_state : clear implicits.

  Lemma can_deduce_implies_not_input r kf nf :
    In r p.(program.rules) ->
    can_deduce_normal_fact r kf nf ->
    is_input nf.(normal_fact.rel) = false.
  Proof.
    intros Hr (hyps & Hri & _). apply concl_rel_not_input.
    eauto using program.rule_concl_rel_in, rule.interp_concl_relname_in.
  Qed.

  Lemma pattern_concl_not_input mr pat pats :
    In mr p.(program.meta_rules) ->
    meta_rule.pattern_interp mr pat pats ->
    is_input pat.(fact_pattern.rel) = false.
  Proof.
    intros. apply concl_rel_not_input.
    eauto using program.meta_rule_concl_rel_in,
      meta_rule.pattern_interp_concl_relname_in.
  Qed.

  Lemma no_matching_inputs inputs pat :
    good_input_facts inputs ->
    is_input pat.(fact_pattern.rel) = false ->
    Existsn (message.matches pat) 0 inputs.
  Proof.
    intros (Hall & _) HER. apply Forall_not_Existsn_0.
    rewrite Forall_forall in Hall |- *. intros g Hg Hm.
    specialize (Hall _ Hg). destruct g as [gnf | ? ? ?]; [ | exact Hm ].
    destruct Hm as (Hrel & _). simpl in Hall. congruence.
  Qed.

  Lemma sane_input_sents_0 inputs s pat msgs :
    sane_state inputs s ->
    is_input pat.(fact_pattern.rel) = true ->
    Forall2 (fun r m => Existsn (message.matches pat) m (get_or_default s.(sents) r))
            sender_rules msgs ->
    list_sum msgs = 0.
  Proof.
    intros Hsane HER Hf2.
    destruct (Hsane.(sane_input_rel) _ HER) as (Hz & _).
    assert (Hmz : msgs = repeat 0 (length sender_rules)).
    { eapply Forall2_unique_r;
        [ exact Hf2
        | apply Forall2_repeat_r, Forall_forall; intros r0 _;
          apply get_or_default_values; [ exact Hz | apply Existsn_nil ]
        | intros x y y' _ Hy Hy'; exact (Existsn_unique _ _ _ _ Hy Hy') ]. }
    rewrite Hmz, list_sum_repeat. lia.
  Qed.

  Lemma sane_sent_counts_eq_dones inputs s pat ems msgs :
    sane_state inputs s ->
    Forall2 (fun r m => In (message.done_with pat (from_rule r) m) s.(known_facts))
            sender_rules ems ->
    Forall2 (fun r m => Existsn (message.matches pat) m (get_or_default s.(sents) r))
            sender_rules msgs ->
    msgs = ems.
  Proof.
    intros Hsane Hdones Hf2.
    eapply Forall2_unique_r;
      [ exact Hf2 | | intros x y y' _ Hy Hy'; exact (Existsn_unique _ _ _ _ Hy Hy') ].
    eapply Forall2_impl_strong; [ exact Hdones | ].
    intros rk ek HIn _ _. exact (proj1 (Hsane.(sane_local_meta) _ _ _ HIn)).
  Qed.

  Lemma Forall2_update_at_nat {A} (R S : A -> nat -> Prop) (a : A) (d : nat) (l : list A) (ns : list nat) :
    NoDup l -> In a l ->
    Forall2 R l ns ->
    (forall x, In x l -> x <> a -> forall n, R x n -> S x n) ->
    (forall n, R a n -> S a (n + d)) ->
    exists ns', Forall2 S l ns' /\ list_sum ns' = list_sum ns + d.
  Proof.
    intros Hnd Hin HF. revert Hnd Hin.
    induction HF as [| x n l' ns' HR HF IH]; intros Hnd Hin Hother Hat.
    - inversion Hin.
    - inversion Hnd as [| xx ll Hnotin Hnd']; subst.
      destruct Hin as [Heq | Hin'].
      + subst x. exists ((n + d) :: ns'). split.
        * constructor; [ exact (Hat _ HR) | ].
          eapply Forall2_impl_strong; [ exact HF | ].
          intros y m Hry Hy _. apply (Hother y); [ right; exact Hy | | exact Hry ].
          intro Hya; subst y; exact (Hnotin Hy).
        * rewrite !list_sum_cons. lia.
      + assert (Hxa : x <> a) by (intro Hc; subst x; exact (Hnotin Hin')).
        specialize (IH Hnd' Hin' (fun y Hy => Hother y (or_intror Hy)) Hat).
        destruct IH as (ns'' & HF'' & Hsum).
        exists (n :: ns''). split.
        * constructor; [ apply (Hother x); [ left; reflexivity | exact Hxa | exact HR ] | exact HF'' ].
        * rewrite !list_sum_cons. lia.
  Qed.

  Lemma sane_count_forall2_fire (P : message -> Prop) (m : sent_map) (r : rule)
      (f : message) (msgs : list nat) (d : nat) :
    In r p.(program.rules) ->
    (forall c, Existsn P c (get_or_default m r) -> Existsn P (c + d) (f :: get_or_default m r)) ->
    Forall2 (fun r0 c => Existsn P c (get_or_default m r0)) sender_rules msgs ->
    exists msgs',
      Forall2 (fun r0 c => Existsn P c (get_or_default (mupd_with_default (cons f) m r) r0)) sender_rules msgs'
      /\ list_sum msgs' = list_sum msgs + d.
  Proof.
    intros Hin_r Hinc Hf2.
    eapply (Forall2_update_at_nat
              (fun r0 c => Existsn P c (get_or_default m r0))
              (fun r0 c => Existsn P c (get_or_default (mupd_with_default (cons f) m r) r0))
              r d sender_rules msgs).
    - unfold sender_rules. apply NoDup_dedup.
    - exact (In_sender_rules r Hin_r).
    - exact Hf2.
    - intros x _ Hxr n HRx. rewrite get_or_default_mupd.
      destr (eqb r x); [ exfalso; apply Hxr; congruence | exact HRx ].
    - intros n HRr. rewrite get_or_default_mupd. destr (eqb r r); [ | congruence ].
      exact (Hinc n HRr).
  Qed.

  Lemma step_preserves_sane inputs s1 s2 :
    good_input_facts inputs ->
    sane_state inputs s1 ->
    comp_step s1 s2 ->
    sane_state inputs s2.
  Proof.
    intros Hinp Hsane Hstep.
    destruct Hsane as [Hmf_inp Hmf_sent Hcount Hinp_sane Hinp_propagated].
    invert Hstep.
    rename H into Hin_r. rename H0 into Hfire.
    cbv [fire_at_rule] in Hfire.
    assert (Hcount' : forall pat0,
              exists msgs num_inp num_known,
                Forall2 (fun r0 m => Existsn (message.matches pat0) m
                           (get_or_default (mupd_with_default (cons new_fact) (sents s1) r) r0))
                        sender_rules msgs /\
                  Existsn (message.matches pat0) num_inp inputs /\
                  Existsn (message.matches pat0) num_known (new_fact :: s1.(known_facts)) /\
                  num_known = num_inp + list_sum msgs).
    { intros pat0.
      destruct (Hcount pat0) as (msgs & num_inp & num_known & Hf2 & Hni & Hnk & Hsum).
      assert (Hd : exists d, forall l c,
                 Existsn (message.matches pat0) c l ->
                 Existsn (message.matches pat0) (c + d) (new_fact :: l)).
      { destruct (classic (message.matches pat0 new_fact)) as [Hm | Hm].
        - exists 1. intros. rewrite Nat.add_1_r. apply Existsn_yes; assumption.
        - exists 0. intros. rewrite Nat.add_0_r. apply Existsn_no; assumption. }
      destruct Hd as (d & Hd).
      edestruct (sane_count_forall2_fire (message.matches pat0) (sents s1) r
                   new_fact msgs d Hin_r (Hd _) Hf2) as (msgs' & Hf2' & Hsum').
      exists msgs', num_inp, (num_known + d).
      ssplit; [ exact Hf2' | exact Hni | apply Hd; exact Hnk | lia ]. }
    destruct new_fact as [nf | pat src cnt].
    - cbn [node.can_deduce node.state.known node.state.sent node_prog program.rules program.meta_rules] in Hfire.
      destruct Hfire as (Hex & Hfresh). invert_list_stuff.
      assert (Hnf_noninput : is_input nf.(normal_fact.rel) = false)
        by (eapply can_deduce_implies_not_input; eassumption).
      constructor; cbn [known_facts sents].
      + intros pat0 num [Heq | Hin]; [ discriminate | exact (Hmf_inp _ _ Hin) ].
      + intros pat0 r0 num [Heq | Hin]; [ discriminate | ].
        specialize (Hmf_sent _ _ _ Hin). destruct Hmf_sent as (HE & HI).
        rewrite get_or_default_mupd. destr (eqb r r0).
        * assert (Hnmatch : ~ message.matches pat0 (message.normal nf)).
          { intros Hmatch. apply Hfresh. exists pat0, num. auto. }
          split; [ apply Existsn_no; [ exact Hnmatch | exact HE ] | right; exact HI ].
        * split; [ exact HE | exact HI ].
      + exact Hcount'.
      + intros pat0 HR. specialize (Hinp_sane pat0 HR). destruct Hinp_sane as (HForall & Hnone). split.
        * rewrite mupd_with_default_eq_put.
          apply Forall_values_put; [ exact HForall | ].
          apply Existsn_no; [ intros (Hrel & _); congruence | ].
          apply get_or_default_values; [ exact HForall | apply Existsn_nil ].
        * intros r0 num [Heq | Hin]; [ discriminate | exact (Hnone _ _ Hin) ].
      + intros f Hf. right. exact (Hinp_propagated f Hf).
    - cbn [node.can_deduce node.state.known node.state.sent node_prog program.rules program.meta_rules] in Hfire.
      destruct Hfire as (Hsrc & Hexmr & Hexn & Hsat). subst src.
      assert (Hpat_noninput : is_input pat.(fact_pattern.rel) = false).
      { apply Exists_exists in Hexmr. destruct Hexmr as (mr & Hmr & mhyps & Hpi & _).
        eapply pattern_concl_not_input; eassumption. }
      constructor; cbn [known_facts sents].
      + intros pat0 num [Heq | Hin]; [ discriminate | exact (Hmf_inp _ _ Hin) ].
      + intros pat0 r0 num Hin. rewrite get_or_default_mupd. destr (eqb r r0).
        * destruct Hin as [Heq | Hin].
          -- invert Heq.
             split; [ apply Existsn_no; [ intros [] | exact Hexn ] | left; reflexivity ].
          -- specialize (Hmf_sent _ _ _ Hin). destruct Hmf_sent as (HE & HI).
             split; [ apply Existsn_no; [ intros [] | exact HE ] | right; exact HI ].
        * destruct Hin as [Heq | Hin].
          -- invert Heq. congruence.
          -- specialize (Hmf_sent _ _ _ Hin). destruct Hmf_sent as (HE & HI). auto.
      + exact Hcount'.
      + intros pat0 HR. specialize (Hinp_sane pat0 HR). destruct Hinp_sane as (HForall & Hnone). split.
        * rewrite mupd_with_default_eq_put.
          apply Forall_values_put; [ exact HForall | ].
          apply Existsn_no; [ intros [] | ].
          apply get_or_default_values; [ exact HForall | apply Existsn_nil ].
        * intros r0 num [Heq | Hin].
          -- invert Heq. congruence.
          -- exact (Hnone _ _ Hin).
      + intros f Hf. right. exact (Hinp_propagated f Hf).
  Qed.

  Lemma sane_allowed_inputs inputs s :
    good_input_facts inputs ->
    sane_state inputs s ->
    allowed_inputs s.(known_facts).
  Proof.
    intros Hinp Hsane pat ems Hf2.
    assert (Hexp : expects_num_facts s.(known_facts) pat (list_sum ems))
      by (exists ems; split; [ exact Hf2 | reflexivity ]).
    rewrite expects_num_facts_eq in Hexp.
    destruct (Hsane.(sane_count) pat) as (msgs & num_inp & num_known & Hms & Hinp_cnt & Hkn_cnt & Hsum).
    eapply Existsn_le_of_Existsn; [ exact Hkn_cnt | ]. rewrite Hsum.
    destruct (is_input pat.(fact_pattern.rel)) eqn:ER; cbv iota in Hexp.
    - apply Hsane.(sane_input_meta) in Hexp.
      destruct Hinp as (_ & Hgc). destruct (Hgc _ _ Hexp) as (_ & num' & Hle & Hex').
      pose proof (Existsn_unique _ _ _ _ Hinp_cnt Hex') as ->.
      rewrite (sane_input_sents_0 _ _ _ _ Hsane ER Hms), Nat.add_0_r. exact Hle.
    - destruct Hexp as (emss & Hexpp0 & Hsum_ems).
      pose proof (Existsn_unique _ _ _ _ Hinp_cnt (no_matching_inputs _ _ Hinp ER)) as ->.
      cbn [Nat.add]. rewrite Hsum_ems.
      enough (msgs = emss) as -> by lia.
      eapply sane_sent_counts_eq_dones; eassumption.
  Qed.

  Lemma comp_step_known_cons s s' :
    comp_step s s' -> exists f, s'.(known_facts) = f :: s.(known_facts).
  Proof. intros H. invert H. cbn [known_facts]. eauto. Qed.

  Lemma comp_step_knows_incl inputs s s' :
    good_input_facts inputs ->
    sane_state inputs s ->
    comp_step s s' ->
    knows_incl s.(known_facts) s'.(known_facts).
  Proof.
    intros Hinp Hsane Hstep.
    destruct (comp_step_known_cons _ _ Hstep) as (f & Hf).
    apply node.knows_incl_of_submultiset.
    - exists [f]. rewrite Hf. apply Permutation_cons_append.
    - exact (sane_allowed_inputs _ _ Hinp (step_preserves_sane _ _ _ Hinp Hsane Hstep)).
  Qed.

  Lemma meta_facts_correct_at_rule_mono mrs k1 k2 r sent :
    knows_incl k1 k2 ->
    meta_facts_correct_at_rule mrs k1 r sent ->
    meta_facts_correct_at_rule mrs k2 r sent.
  Proof.
    intros Hincl H pat num HIn.
    destruct (H _ _ HIn) as (mr & mhyps & Hin & Hexn & Hpi & Hkn & Hns).
    exists mr, mhyps. ssplit; try assumption.
    eapply Forall_impl; [ exact Hkn | ]. intros mh Hmh.
    exact (Hincl (fact.meta mh) Hmh).
  Qed.

  Lemma at_rule_cons_tail mrs k1 k2 r f sent pat num :
    knows_incl k1 k2 ->
    ~ message.matches pat f ->
    meta_facts_correct_at_rule mrs k1 r sent ->
    In (message.done_with pat (from_rule r) num) sent ->
    exists mr mhyps,
      In mr mrs /\
        Existsn (message.matches pat) num (f :: sent) /\
        meta_rule.pattern_interp mr pat (map meta_fact.pattern mhyps) /\
        Forall (knows_meta_fact k2) mhyps /\
        Forall (fun mh => mh.(meta_fact.pattern) <> pat) mhyps.
  Proof.
    intros Hincl Hnm H HIn.
    destruct (H _ _ HIn) as (mr & mhyps & Hin0 & Hexn0 & Hpi0 & Hkn0 & Hns0).
    exists mr, mhyps. ssplit; try assumption.
    - apply Existsn_no; assumption.
    - eapply Forall_impl; [ exact Hkn0 | ]. intros mh Hmh.
      exact (Hincl (fact.meta mh) Hmh).
  Qed.

  Lemma step_preserves_mfs_correct inputs s s' :
    good_input_facts inputs ->
    sane_state inputs s ->
    meta_facts_correct s ->
    comp_step s s' ->
    meta_facts_correct s'.
  Proof.
    intros Hinp Hsane Hmfc Hstep.
    pose proof (comp_step_knows_incl _ _ _ Hinp Hsane Hstep) as Hmono.
    pose proof Hsane as Hsane0. destruct Hsane0 as [_ Hmf_sent _ _ _].
    invert Hstep. rename H into Hin_r. rename H0 into Hfire.
    cbv [fire_at_rule] in Hfire.
    cbn [node.can_deduce node.state.known node.state.sent node_prog
           program.rules program.meta_rules] in Hfire.
    cbv [meta_facts_correct] in Hmfc |- *. cbn [known_facts sents] in Hmono |- *.
    pose proof (Hmfc r Hin_r) as Hmfc_r.
    intros r0 Hr0. rewrite get_or_default_mupd. destr (eqb r r0);
      [ | eapply meta_facts_correct_at_rule_mono; [ exact Hmono | exact (Hmfc r0 Hr0) ] ].
    intros pat num HIn.
    destruct new_fact as [nf | npat nsrc ncnt].
    + destruct Hfire as (Hex & Hfresh).
      destruct HIn as [Heq | HIn]; [ discriminate | ].
      eapply at_rule_cons_tail; [ exact Hmono | | exact Hmfc_r | exact HIn ].
      intros Hmatch. apply Hfresh. exists pat, num. auto.
    + destruct Hfire as (Hsrc & Hexmr & Hexn & Hsat). subst nsrc.
      destruct HIn as [Heq_nf | HIn_old].
      2:{ eapply at_rule_cons_tail; [ exact Hmono | intros [] | exact Hmfc_r | exact HIn_old ]. }
      invert Heq_nf.
      apply Exists_exists in Hexmr. destruct Hexmr as (mr & Hmr_in & mhyps & Hpi & Hkn).
      assert (HNI : is_input pat.(fact_pattern.rel) = false)
        by (eapply pattern_concl_not_input; eassumption).
      destruct (classic (exists mh, In mh mhyps /\ mh.(meta_fact.pattern) = pat))
        as [Hself | Hnoself].
      * destruct Hself as (mh & Hin_mh & Hmh_pat).
        rewrite Forall_forall in Hkn. pose proof (Hkn _ Hin_mh) as Hk_mh.
        destruct Hk_mh as (num_self & Hexp_self & _ & _).
        rewrite Hmh_pat in Hexp_self.
        rewrite expects_num_facts_eq, HNI in Hexp_self.
        destruct Hexp_self as (expected_msgss & Hf2 & _).
        destruct (Forall2_In_l _ _ _ _ Hf2 (In_sender_rules r0 Hin_r))
          as (num_old & _ & Hin_x_known). cbv beta in Hin_x_known.
        specialize (Hmf_sent _ _ _ Hin_x_known). destruct Hmf_sent as (_ & Hin_x_sent).
        destruct (Hmfc_r _ _ Hin_x_sent)
          as (mr_old & mhyps_old & Hin_mr_old & Hexn_old & Hpi_old & Hkn_old & Hns_old).
        exists mr_old, mhyps_old. ssplit; try assumption.
        -- apply Existsn_no; [ intros [] | exact Hexn ].
        -- eapply Forall_impl; [ exact Hkn_old | ]. intros mh0 Hmh0.
           exact (Hmono (fact.meta mh0) Hmh0).
      * exists mr, mhyps. ssplit; try assumption.
        -- apply Existsn_no; [ intros [] | exact Hexn ].
        -- eapply Forall_impl; [ exact Hkn | ]. intros mh0 Hmh0.
           exact (Hmono (fact.meta mh0) Hmh0).
        -- apply Forall_forall. intros mh0 Hmh0 Heq. apply Hnoself. eauto.
  Qed.

  Lemma steps_preserves_sane inputs s s' :
    good_input_facts inputs ->
    sane_state inputs s ->
    comp_step^* s s' ->
    sane_state inputs s'.
  Proof.
    intros Hinp Hsane Hsteps. induction Hsteps; auto.
    apply IHHsteps; auto.
    eapply step_preserves_sane; eassumption.
  Qed.

  Lemma steps_preserves_mfs_correct inputs s s' :
    good_input_facts inputs ->
    sane_state inputs s ->
    meta_facts_correct s ->
    comp_step^* s s' ->
    meta_facts_correct s'.
  Proof.
    intros Hinp Hsane Hmfc Hsteps. induction Hsteps; auto.
    apply IHHsteps; auto.
    - eapply step_preserves_sane; eassumption.
    - eapply step_preserves_mfs_correct; eassumption.
  Qed.

  Definition has_derived_datalog_fact (s : state) (f : fact) :=
    match f with
    | fact.normal nf => In (message.normal nf) s.(known_facts)
    | fact.meta mf =>
        if is_input (meta_fact.rel mf) then
          exists num,
            In (message.done_with mf.(meta_fact.pattern) from_input num) s.(known_facts) /\
              Existsn (message.matches mf.(meta_fact.pattern)) num s.(known_facts)
        else
          forall r, In r p.(program.rules) ->
            exists num,
              In (message.done_with mf.(meta_fact.pattern) (from_rule r) num) s.(known_facts)
    end.

  Definition mf_consistent_state (s : state) (f : fact) :=
    match f with
    | fact.normal _ => True
    | fact.meta mf =>
        fact.set_consistent_with mf (fun nf => In (message.normal nf) s.(known_facts))
    end.

  Definition state_correct (inputs : list message) (s : state) :=
    forall f,
      has_derived_datalog_fact s f /\ mf_consistent_state s f ->
      program.interp p (knows_fact inputs) f.

  Lemma knows_fact_local_lift_has_derived s h :
    knows_fact s.(known_facts) h ->
    has_derived_datalog_fact s h.
  Proof.
    intros Hkdf. destruct h as [nf | mf]; cbn [has_derived_datalog_fact].
    - exact Hkdf.
    - destruct Hkdf as (num & Hexp & Hexn & _).
      rewrite expects_num_facts_eq in Hexp.
      cbv [meta_fact.rel]. destruct (is_input mf.(meta_fact.pattern).(fact_pattern.rel)) eqn:HER.
      + exists num. split; [ exact Hexp | exact Hexn ].
      + intros r Hr. destruct Hexp as (msgss & Hf2 & _).
        destruct (Forall2_In_l _ _ _ _ Hf2 (In_sender_rules r Hr))
          as (m & _ & Hin_m). cbv beta in Hin_m.
        exists m. exact Hin_m.
  Qed.

  Lemma knows_fact_local_lift_mf_consistent s h :
    knows_fact s.(known_facts) h ->
    mf_consistent_state s h.
  Proof.
    intros Hkdf.
    destruct h as [nf | mf]; cbn [mf_consistent_state]; [exact I|].
    destruct Hkdf as (num & _ & _ & Hbic). exact Hbic.
  Qed.

  Lemma good_inputs_knows_fact_inputs inputs :
    good_input_facts inputs ->
    0 < length p.(program.rules) ->
    program.good_input_set p (knows_fact inputs).
  Proof.
    intros Hinp Hlt. split.
    - intros f Hf. destruct f as [nf | mf]; simpl in Hf.
      + destruct Hinp as (Hinp_all & _). rewrite Forall_forall in Hinp_all.
        specialize (Hinp_all _ Hf). simpl in Hinp_all.
        intros Hin_concl.
        pose proof (concl_rel_not_input _ Hin_concl) as HR0.
        cbv [fact.rel] in *. congruence.
      + destruct Hf as (num0 & Hexp & _ & _).
        rewrite expects_num_facts_eq in Hexp.
        cbv [fact.rel meta_fact.rel].
        destruct (is_input mf.(meta_fact.pattern).(fact_pattern.rel)) eqn:HER.
        * intros Hin_concl.
          pose proof (concl_rel_not_input _ Hin_concl) as HR0. congruence.
        * destruct Hexp as (msgss & Hf2_msgs & _).
          destruct (length_pos_In _ Hlt) as (r0 & Hin_r0).
          destruct (Forall2_In_l _ _ _ _ Hf2_msgs (In_sender_rules r0 Hin_r0)) as (m0 & _ & Hin_m0).
          cbv beta in Hin_m0.
          destruct Hinp as (Hinp_all & _). rewrite Forall_forall in Hinp_all.
          specialize (Hinp_all _ Hin_m0). simpl in Hinp_all. congruence.
    - intros mf Hin. simpl in Hin. destruct Hin as (num0 & _ & _ & Hbic). exact Hbic.
  Qed.

  Definition exactly_pat (nf : normal_fact) : fact_pattern :=
    {| fact_pattern.rel := nf.(normal_fact.rel);
      fact_pattern.args := map value_pattern.exactly nf.(normal_fact.args) |}.

  Lemma matches_exactly_pat (nf : normal_fact) (g : message) :
    message.matches (exactly_pat nf) g <-> g = message.normal nf.
  Proof.
    split.
    - destruct g as [nf'|]; [|intros []].
      intros (Hrel & Hargs). cbn [exactly_pat fact_pattern.rel fact_pattern.args] in *.
      apply value_pattern.matches_map_exactly_inv in Hargs. simp. fwd. congruence.
    - intros ->. cbn [message.matches exactly_pat]. split; [reflexivity|].
      simpl. apply value_pattern.matches_map_exactly.
  Qed.

  Lemma sent_implies_knows inputs s nf r :
    sane_state inputs s ->
    In r p.(program.rules) ->
    In (message.normal nf) (get_or_default s.(sents) r) ->
    In (message.normal nf) s.(known_facts).
  Proof.
    intros Hsane Hin_r Hin_nf.
    destruct (Hsane.(sane_count) (exactly_pat nf))
      as (msgs_sents & num_inp & num_known & Hf2_sent & _ & Hkn & Hsum).
    destruct (Forall2_In_l _ _ _ _ Hf2_sent (In_sender_rules r Hin_r))
      as (ms & Hin_comb & Hexn_sent). cbv beta in Hexn_sent.
    assert (Hms_pos : 1 <= ms).
    { destruct ms; [|lia]. apply Existsn_0_Forall_not in Hexn_sent.
      rewrite Forall_forall in Hexn_sent. exfalso.
      apply (Hexn_sent (message.normal nf) Hin_nf).
      apply matches_exactly_pat. reflexivity. }
    assert (Hpos : 1 <= num_known).
    { rewrite Hsum. pose proof (in_le_list_sum ms msgs_sents (in_combine_r _ _ _ _ Hin_comb)). lia. }
    destruct num_known; [lia|].
    apply Existsn_S in Hkn. destruct Hkn as (l1 & xx & l2 & -> & Hpx & _).
    apply matches_exactly_pat in Hpx. subst xx. apply in_or_app. right. left. reflexivity.
  Qed.

  Lemma use_meta_facts_correct (pat : fact_pattern) inputs s :
    good_input_facts inputs ->
    sane_state inputs s ->
    meta_facts_correct s ->
    meta_facts_ok s ->
    is_input pat.(fact_pattern.rel) = false ->
    0 < length p.(program.rules) ->
    (forall mf',
        mf'.(meta_fact.pattern) <> pat ->
        has_derived_datalog_fact s (fact.meta mf') /\
        mf_consistent_state s (fact.meta mf') ->
        program.interp p (knows_fact inputs) (fact.meta mf')) ->
    has_derived_datalog_fact s
      (fact.meta {| meta_fact.pattern := pat; meta_fact.set := fun _ => True |}) ->
    forall nf,
      fact_pattern.matches pat nf ->
      program.interp p (knows_fact inputs) (fact.normal nf) ->
      In (message.normal nf) s.(known_facts).
  Proof.
    intros Hinp Hsane Hmf Hmf_ok HER Hlen HRs HR nf Hmatch Hprog.
    invert Hprog.
    - simpl in H.
      destruct Hinp as (Hinp_all & _). rewrite Forall_forall in Hinp_all.
      specialize (Hinp_all _ H). simpl in Hinp_all.
      destruct Hmatch as (Hrel & _). congruence.
    - invert H; fwd.
      rename H2p0 into Hin_rk. rename H2p1 into Hri. rename H0 into Hhyps.
      rename l into hyps.
      cbv [has_derived_datalog_fact meta_fact.rel] in HR. simpl in HR.
      rewrite HER in HR.
      specialize (HR _ Hin_rk). destruct HR as (num_k & Hkknows).
      pose proof Hsane as [_ Hmf_sent _ _ _].
      pose proof (Hmf_sent _ _ _ Hkknows) as (Hexn_k & Hin_k_sent).
      destruct (Hmf _ Hin_rk _ _ Hin_k_sent)
        as (mr & mhyps & Hin_mr & Hexn_c & Hpi & Hkdf_h & Hnoself).
      pose proof (Hmf_ok _ Hin_rk _ _ Hin_k_sent) as Hsound_can.
      assert (Hgood_Q : program.good_input_set p (knows_fact inputs))
        by (apply good_inputs_knows_fact_inputs; assumption).
      pose proof (program.valid_impl_honest p Hmeta_rules _ Hgood_Q) as Hhonest.
      assert (Hcan_nf : can_deduce_normal_fact x s.(known_facts) nf).
      { exists hyps. split; [exact Hri|].
        pose proof (Hmeta_rules _ _ Hin_mr Hin_rk _ _ _ _ Hpi Hri Hmatch) as Hcov.
        rewrite Forall_forall. intros h Hh.
        rewrite Forall_forall in Hcov, Hkdf_h, Hhyps, Hnoself.
        pose proof (Hcov _ Hh) as Hcov_h.
        pose proof (Hhyps _ Hh) as Hprog_h.
        cbv [fact.covered_by_pats] in Hcov_h. apply Exists_exists in Hcov_h.
        destruct Hcov_h as (fp & Hfp & Hcov_h). apply in_map_iff in Hfp.
        destruct Hfp as (mh & Hfp & Hin_mh). subst fp.
        pose proof (Hkdf_h _ Hin_mh) as Hk_mh.
        pose proof (Hnoself _ Hin_mh) as Hmh_ne.
        assert (Hprog_mh : program.interp p (knows_fact inputs) (fact.meta mh)).
        { apply (HRs mh Hmh_ne). split.
          - apply (knows_fact_local_lift_has_derived s (fact.meta mh)). exact Hk_mh.
          - apply (knows_fact_local_lift_mf_consistent s (fact.meta mh)). exact Hk_mh. }
        pose proof (Hhonest _ Hprog_mh) as Hcon_mh.
        cbv [fact.set_consistent_with fact.normal_subset] in Hcon_mh.
        destruct Hk_mh as (num_m & Hexp_m & Hexn_m & Hbic_m).
        cbv [fact.set_consistent_with] in Hbic_m.
        destruct h as [nf_h | mf_h]; simpl in Hcov_h.
        + specialize (Hcon_mh _ Hcov_h). specialize (Hbic_m _ Hcov_h).
          simpl. apply Hbic_m. apply Hcon_mh. exact Hprog_h.
        + pose proof (Hhonest _ Hprog_h) as Hcon_h.
          cbv [fact.set_consistent_with fact.normal_subset] in Hcon_h.
          simpl. exists num_m. rewrite Hcov_h in Hexp_m, Hexn_m.
          split; [exact Hexp_m|]. split; [exact Hexn_m|].
          intros nf0 Hm0.
          assert (Hm0' : fact_pattern.matches mh.(meta_fact.pattern) nf0)
            by (rewrite Hcov_h; exact Hm0).
          specialize (Hbic_m _ Hm0'). specialize (Hcon_mh _ Hm0'). specialize (Hcon_h _ Hm0).
          rewrite Hcon_h, <- Hcon_mh. exact Hbic_m. }
      specialize (Hsound_can _ Hcan_nf Hmatch).
      eapply sent_implies_knows; [ exact Hsane | exact Hin_rk | exact Hsound_can ].
  Qed.

  Lemma ok_to_deduce_grow k1 k2 r sent pat mr mhyps :
    In r p.(program.rules) ->
    knows_incl k1 k2 ->
    In mr p.(program.meta_rules) ->
    meta_rule.pattern_interp mr pat (map meta_fact.pattern mhyps) ->
    Forall (knows_meta_fact k1) mhyps ->
    ok_to_deduce r k1 sent pat ->
    ok_to_deduce r k2 sent pat.
  Proof.
    intros Hin_r Hincl Hin_mr Hpi Hkn Hok nf Hcdn Hmatch.
    destruct Hcdn as (local_hyps & Hri & Hknown_big).
    pose proof (Hmeta_rules _ _ Hin_mr Hin_r _ _ _ _ Hpi Hri Hmatch) as Hcov.
    apply (Hok nf); [| exact Hmatch].
    exists local_hyps. split; [exact Hri |].
    rewrite Forall_forall in Hknown_big, Hcov |- *. intros h Hh.
    eapply node.knows_fact_transfer_down;
      [ exact Hincl | exact Hkn | eauto | eauto ].
  Qed.

  Lemma meta_facts_ok_at_rule_grow k1 k2 r sent :
    In r p.(program.rules) ->
    knows_incl k1 k2 ->
    meta_facts_correct_at_rule p.(program.meta_rules) k1 r sent ->
    meta_facts_ok_at_rule k1 r sent ->
    meta_facts_ok_at_rule k2 r sent.
  Proof.
    intros Hin_r Hincl Hc Hok pat num HIn.
    destruct (Hc _ _ HIn) as (mr & mhyps & Hin_mr & _ & Hpi & Hkn & _).
    eapply ok_to_deduce_grow; try eassumption. eapply Hok. eassumption.
  Qed.

  Lemma step_preserves_meta_facts_ok inputs s s' :
    good_input_facts inputs ->
    sane_state inputs s ->
    meta_facts_correct s ->
    meta_facts_ok s ->
    comp_step s s' ->
    meta_facts_ok s'.
  Proof.
    intros Hinp Hsane Hmfc Hmf_ok Hstep.
    pose proof (comp_step_knows_incl _ _ _ Hinp Hsane Hstep) as Hmono.
    invert Hstep. rename H into Hin_r. rename H0 into Hfire.
    cbv [fire_at_rule] in Hfire.
    cbn [node.can_deduce node.state.known node.state.sent node_prog
           program.rules program.meta_rules] in Hfire.
    cbv [meta_facts_ok] in Hmf_ok |- *. cbv [meta_facts_correct] in Hmfc.
    cbn [known_facts sents] in Hmono |- *.
    pose proof (Hmf_ok r Hin_r) as Hmfok_r. pose proof (Hmfc r Hin_r) as Hmfc_r.
    intros r0 Hr0. rewrite get_or_default_mupd. destr (eqb r r0);
      [ | eapply meta_facts_ok_at_rule_grow;
          [ exact Hr0 | exact Hmono | exact (Hmfc r0 Hr0) | exact (Hmf_ok r0 Hr0) ] ].
    intros pat num HIn.
    destruct new_fact as [nf | npat nsrc ncnt].
    - destruct HIn as [Heq | HIn_old]; [ discriminate | ].
      intros nf0 Hcdn0 Hmatch0. right.
      exact (meta_facts_ok_at_rule_grow _ _ _ _ Hin_r Hmono Hmfc_r Hmfok_r
               pat num HIn_old nf0 Hcdn0 Hmatch0).
    - destruct Hfire as (Hsrc & Hexmr & Hexn & Hsat). subst nsrc.
      destruct HIn as [Heq | HIn_old].
      2:{ intros nf0 Hcdn0 Hmatch0. right.
          exact (meta_facts_ok_at_rule_grow _ _ _ _ Hin_r Hmono Hmfc_r Hmfok_r
                   pat num HIn_old nf0 Hcdn0 Hmatch0). }
      invert Heq.
      apply Exists_exists in Hexmr. destruct Hexmr as (mr & Hmr_in & mhyps & Hpi & Hkn).
      assert (Hok0 : ok_to_deduce r0 s.(known_facts) (get_or_default (sents s) r0) pat).
      { intros nf0 Hcdn0 Hm0. apply (Hsat r0 nf0); auto. left. reflexivity. }
      intros nf0 Hcdn0 Hmatch0. right.
      eapply ok_to_deduce_grow; try eassumption.
  Qed.

  Lemma has_derived_input_meta_cons_bw mf F s :
    is_input (meta_fact.rel mf) = true ->
    ~ message.matches mf.(meta_fact.pattern) F ->
    (forall num, F <> message.done_with mf.(meta_fact.pattern) from_input num) ->
    has_derived_datalog_fact (add_known_fact F s) (fact.meta mf) ->
    has_derived_datalog_fact s (fact.meta mf).
  Proof.
    intros HER Hnm Hnd Hf. cbv [has_derived_datalog_fact add_known_fact] in Hf |- *.
    cbn [known_facts] in Hf. rewrite HER in Hf |- *.
    destruct Hf as (num & Hin & Hexn). exists num. split.
    - destruct Hin as [Heq | Hin]; [ exfalso; exact (Hnd num Heq) | exact Hin ].
    - exact (Existsn_cons_no _ _ _ _ Hnm Hexn).
  Qed.

  Lemma comp_step_sound inputs s s' :
    good_input_facts inputs ->
    sane_state inputs s ->
    meta_facts_correct s ->
    meta_facts_ok s ->
    state_correct inputs s ->
    comp_step s s' ->
    state_correct inputs s'.
  Proof.
    intros Hinp Hsane Hmfc Hmf_ok Hsound Hstep f (Hf1 & Hf2).
    pose proof Hstep as Hstep_save.
    invert Hstep. rename H into Hin_r. rename H0 into Hfire.
    cbv [fire_at_rule] in Hfire.
    assert (Hlift : forall h, knows_fact s.(known_facts) h ->
                     program.interp p (knows_fact inputs) h).
    { intros h Hh. apply Hsound. split;
        [ apply knows_fact_local_lift_has_derived; exact Hh
        | apply knows_fact_local_lift_mf_consistent; exact Hh ]. }
    cbn [known_facts sents] in Hf1, Hf2 |- *.
    destruct new_fact as [nnf | npat nsrc ncnt].
    { cbn [node.can_deduce node.state.known node.state.sent node_prog
             program.rules program.meta_rules] in Hfire.
      destruct Hfire as (Hex & Hfresh). invert_list_stuff.
      match goal with Hc : can_deduce_normal_fact _ _ _ |- _ => rename Hc into Hded end.
      destruct f as [nf | mf].
      - cbv [has_derived_datalog_fact] in Hf1.
        destruct Hf1 as [Heq | Hf1].
        + invert Heq.
          destruct Hded as (hyps & Hri & Hkdf_hyps).
          eapply pftree.step.
          * constructor. apply Exists_exists. eauto.
          * rewrite Forall_forall in Hkdf_hyps |- *. intros h Hin_h.
            apply Hlift. exact (Hkdf_hyps _ Hin_h).
        + apply Hsound. split; [ exact Hf1 | exact I ].
      - assert (HNI_nf : is_input nnf.(normal_fact.rel) = false)
          by (eapply can_deduce_implies_not_input; eassumption).
        assert (Hf1_s : has_derived_datalog_fact s (fact.meta mf)).
        { cbv [has_derived_datalog_fact] in Hf1 |- *.
          destruct (is_input (meta_fact.rel mf)) eqn:HER.
          - destruct Hf1 as (num & Hin & Hexn). exists num. split.
            + destruct Hin as [Heq | Hin]; [ discriminate | exact Hin ].
            + eapply Existsn_cons_no; [ | exact Hexn ].
              intros (Hrel & _). cbv [meta_fact.rel] in HER. congruence.
          - intros r' Hr'. destruct (Hf1 r' Hr') as (num & Hin).
            destruct Hin as [Heq | Hin]; [ discriminate | exists num; exact Hin ]. }
        assert (Hf2_s : mf_consistent_state s (fact.meta mf)).
        { cbv [mf_consistent_state fact.set_consistent_with] in Hf2 |- *.
          intros nf0 Hm0. specialize (Hf2 _ Hm0). rewrite Hf2. split.
          - intros [Heq | Hk]; [ | exact Hk ].
            invert Heq. exfalso.
            cbv [has_derived_datalog_fact meta_fact.rel] in Hf1_s.
            destruct Hm0 as (Hrel0 & Hargs0).
            rewrite Hrel0, HNI_nf in Hf1_s. cbv iota in Hf1_s.
            destruct (Hf1_s _ Hin_r) as (num & Hknows).
            pose proof (Hsane.(sane_local_meta) _ _ _ Hknows) as (_ & Hin_x).
            apply Hfresh. exists mf.(meta_fact.pattern), num.
            split; [exact Hin_x |]. split; [exact Hrel0 |]. exact Hargs0.
          - intros Hk. right. exact Hk. }
        apply Hsound. split; [ exact Hf1_s | exact Hf2_s ]. }
    { cbn [node.can_deduce node.state.known node.state.sent node_prog
             program.rules program.meta_rules] in Hfire.
      destruct Hfire as (Hsrc & Hexmr & Hexn_F & Hsat). subst nsrc.
      apply Exists_exists in Hexmr.
      destruct Hexmr as (mr & Hin_mr & mhyps & Hpi & Hknown_h_fire).
      assert (Hkd_normal : forall nf0,
                 In (message.normal nf0)
                   (message.done_with npat (from_rule r) ncnt :: s.(known_facts)) <->
                 In (message.normal nf0) s.(known_facts)).
      { intros. split; [ intros [Heq | Hk]; [ discriminate | exact Hk ] | intros Hk; right; exact Hk ]. }
      destruct f as [nf | mf].
      - cbv [has_derived_datalog_fact] in Hf1. apply Hkd_normal in Hf1.
        apply Hsound. split; [ exact Hf1 | exact I ].
      - assert (Hf2_s : mf_consistent_state s (fact.meta mf)).
        { cbv [mf_consistent_state fact.set_consistent_with] in Hf2 |- *.
          intros nf0 Hm0. specialize (Hf2 _ Hm0). rewrite Hf2. exact (Hkd_normal nf0). }
        destruct (is_input (meta_fact.rel mf)) eqn:HER.
        + assert (Hnm : ~ message.matches mf.(meta_fact.pattern)
                          (message.done_with npat (from_rule r) ncnt))
            by (intros []).
          assert (Hnd : forall num,
                     message.done_with npat (from_rule r) ncnt
                     <> message.done_with mf.(meta_fact.pattern) from_input num)
            by (intros num Heq; invert Heq).
          apply Hsound. split; [ | exact Hf2_s ].
          eapply (has_derived_input_meta_cons_bw mf _ s HER Hnm Hnd).
          cbv [add_known_fact]. exact Hf1.
        + destruct (classic (mf.(meta_fact.pattern) = npat)) as [Hpe | HNeq].
          * destruct (classic (exists num0,
                        In (message.done_with npat (from_rule r) num0) s.(known_facts)))
              as [HA1 | HA2].
            -- assert (Hf1_s : has_derived_datalog_fact s (fact.meta mf)).
               { cbv [has_derived_datalog_fact] in Hf1 |- *.
                 rewrite HER in Hf1 |- *. rewrite Hpe in *.
                 intros r' Hr'. destruct (classic (r' = r)) as [-> | Hrne]; [ exact HA1 |].
                 destruct (Hf1 r' Hr') as (num & Hin). destruct Hin as [Heq | Hk_s];
                   [ invert Heq; congruence | exists num; exact Hk_s ]. }
               apply Hsound. split; [ exact Hf1_s | exact Hf2_s ].
            -- set (s' := {| known_facts :=
                               message.done_with npat (from_rule r) ncnt
                               :: known_facts s;
                             sents :=
                               mupd_with_default
                                 (cons (message.done_with npat (from_rule r) ncnt))
                                 (sents s) r |}) in Hstep_save, Hf1, Hf2.
               pose (mf_constr :=
                       {| meta_fact.pattern := npat;
                         meta_fact.set :=
                           fun args =>
                             rule.one_step_derives p.(program.rules) mhyps
                               {| normal_fact.rel := npat.(fact_pattern.rel);
                                 normal_fact.args := args |} |}).
               assert (Hprog_constr :
                         program.interp p (knows_fact inputs) (fact.meta mf_constr)).
               { eapply pftree.step.
                 - constructor. apply Exists_exists. exists mr. split; [exact Hin_mr|].
                   exists npat. split; [exact Hpi|]. split; [reflexivity|].
                   intros. reflexivity.
                 - apply Forall_forall. intros h Hh. apply in_map_iff in Hh. fwd.
                   apply Hlift. cbn [node.knows_fact].
                   rewrite Forall_forall in Hknown_h_fire. auto. }
               assert (HNI_npat : is_input npat.(fact_pattern.rel) = false)
                 by (eapply pattern_concl_not_input; eassumption).
               assert (Hgood_Q : program.good_input_set p (knows_fact inputs))
                 by (apply good_inputs_knows_fact_inputs;
                     eauto using In_length_pos).
               pose proof (program.valid_impl_honest p Hmeta_rules _ Hgood_Q) as Hhonest.
               pose proof (Hhonest _ Hprog_constr) as Hcon_constr.
               cbv [fact.set_consistent_with fact.normal_subset] in Hcon_constr.
               assert (Hequiv : fact.equiv (fact.meta mf_constr) (fact.meta mf)).
               { subst mf_constr. cbv [fact.equiv meta_fact.equiv]. simpl.
                 split; [congruence|].
                 intros args Hargs.
                 pose proof (step_preserves_sane _ _ _ Hinp Hsane Hstep_save) as Hsane_s'.
                 pose proof (step_preserves_mfs_correct _ _ _ Hinp Hsane Hmfc Hstep_save)
                   as Hmfc_s'.
                 pose proof (step_preserves_meta_facts_ok _ _ _ Hinp Hsane Hmfc Hmf_ok
                               Hstep_save) as Hmf_ok_s'.
                 assert (HRs_umfc :
                   forall mf',
                     mf'.(meta_fact.pattern) <> npat ->
                     has_derived_datalog_fact s' (fact.meta mf') /\
                     mf_consistent_state s' (fact.meta mf') ->
                     program.interp p (knows_fact inputs) (fact.meta mf')).
                 { intros mf' Hne (Hhd' & Hmc').
                   apply Hsound. split.
                   - cbv [has_derived_datalog_fact] in Hhd' |- *.
                     subst s'. cbn [known_facts sents] in Hhd'.
                     destruct (is_input (meta_fact.rel mf')) eqn:HERmf'.
                     + destruct Hhd' as (num & Hin & Hexn). exists num. split.
                       * destruct Hin as [Heq | Hin]; [ invert Heq | exact Hin ].
                       * eapply Existsn_cons_no; [ | exact Hexn ]. intros [].
                     + intros r' Hr'. destruct (Hhd' r' Hr') as (num & Hin).
                       destruct Hin as [Heq | Hin]; [ | exists num; exact Hin ].
                       invert Heq. congruence.
                   - cbv [mf_consistent_state fact.set_consistent_with] in Hmc' |- *.
                     intros nf2 Hm2. specialize (Hmc' _ Hm2). subst s'.
                     cbn [known_facts] in Hmc'. rewrite Hmc'. exact (Hkd_normal nf2). }
                 assert (Hf1_True : has_derived_datalog_fact s'
                            (fact.meta {| meta_fact.pattern := npat;
                                         meta_fact.set := fun _ => True |})).
                 { cbv [has_derived_datalog_fact meta_fact.rel] in Hf1 |- *. simpl.
                   rewrite Hpe in Hf1. exact Hf1. }
                 pose proof (use_meta_facts_correct npat inputs s'
                               Hinp Hsane_s' Hmfc_s' Hmf_ok_s' HNI_npat
                               ltac:(eauto using In_length_pos) HRs_umfc Hf1_True)
                   as Humfc.
                 assert (Hm_npat : fact_pattern.matches npat
                            {| normal_fact.rel := npat.(fact_pattern.rel);
                              normal_fact.args := args |})
                   by (split; [reflexivity | exact Hargs]).
                 assert (Hm_mf : fact_pattern.matches mf.(meta_fact.pattern)
                            {| normal_fact.rel := npat.(fact_pattern.rel);
                              normal_fact.args := args |})
                   by (rewrite Hpe; exact Hm_npat).
                 specialize (Hcon_constr _ Hm_npat).
                 cbn [meta_fact.set meta_fact.pattern normal_fact.args] in Hcon_constr.
                 cbv [mf_consistent_state fact.set_consistent_with] in Hf2.
                 specialize (Hf2 _ Hm_mf). cbn [normal_fact.args] in Hf2.
                 rewrite Hcon_constr, Hf2. subst s'. cbn [known_facts].
                 split.
                 - intros Hprog. exact (Humfc _ Hm_npat Hprog).
                 - intros HIn. apply Hkd_normal in HIn.
                   apply Hsound. split; [ exact HIn | exact I ]. }
               destruct (program.interp_ext _ _ _ _ Hprog_constr Hequiv)
                 as [HQbad | Hgoal]; [| exact Hgoal].
               exfalso. subst mf_constr.
               destruct HQbad as (num & Hexp & _ & _). cbn [meta_fact.pattern] in Hexp.
               rewrite expects_num_facts_eq, HNI_npat in Hexp.
               destruct Hexp as (msgss & Hf2m & _).
               destruct (Forall2_In_l _ _ _ _ Hf2m (In_sender_rules r Hin_r))
                 as (m & _ & Hin_m). cbv beta in Hin_m.
               destruct Hinp as (Hinp_all & _). rewrite Forall_forall in Hinp_all.
               specialize (Hinp_all _ Hin_m). simpl in Hinp_all. congruence.
          * assert (Hf1_s : has_derived_datalog_fact s (fact.meta mf)).
            { cbv [has_derived_datalog_fact] in Hf1 |- *. rewrite HER in Hf1 |- *.
              intros r' Hr'. destruct (Hf1 r' Hr') as (num & Hin).
              destruct Hin as [Heq | Hk_s]; [ | exists num; exact Hk_s ].
              invert Heq. congruence. }
            apply Hsound. split; [ exact Hf1_s | exact Hf2_s ]. }
  Qed.

  (* ===== Monotonicity helpers for completeness ===== *)

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

  Lemma comp_step_known_incl s s' :
    comp_step s s' -> incl s.(known_facts) s'.(known_facts).
  Proof. intros Hstep. invert Hstep. cbn [known_facts]. apply incl_tl, incl_refl. Qed.

  Lemma comp_steps_known_incl s s' :
    comp_step^* s s' -> incl s.(known_facts) s'.(known_facts).
  Proof.
    intros Hsteps. induction Hsteps; [apply incl_refl|].
    eapply incl_tran; [ apply comp_step_known_incl; exact H | exact IHHsteps ].
  Qed.

  Lemma step_preserves_has_derived s s' f :
    comp_step s s' ->
    has_derived_datalog_fact s f -> has_derived_datalog_fact s' f.
  Proof.
    intros Hstep Hd.
    invert Hstep. rename H into Hin_r. rename H0 into Hfire.
    cbv [fire_at_rule] in Hfire.
    destruct f as [nf | mf]; cbv [has_derived_datalog_fact] in *; cbn [known_facts].
    - apply in_cons. exact Hd.
    - destruct (is_input (meta_fact.rel mf)) eqn:HER.
      + destruct Hd as (num & Hin & Hexn). exists num. split; [ apply in_cons; exact Hin |].
        assert (Hnm : ~ message.matches mf.(meta_fact.pattern) new_fact).
        { destruct new_fact as [nnf | npat nsrc ncnt]; [| intros [] ].
          intros (Hrel & _).
          cbn [node.can_deduce node.state.known node.state.sent node_prog
               program.rules program.meta_rules] in Hfire.
          destruct Hfire as (Hex & _). invert_list_stuff.
          assert (Hni : is_input nnf.(normal_fact.rel) = false)
            by (eapply can_deduce_implies_not_input; eassumption).
          cbv [meta_fact.rel] in HER. congruence. }
        apply Existsn_no; [ exact Hnm | exact Hexn ].
      + intros r' Hr'. destruct (Hd r' Hr') as (num & Hin). exists num. apply in_cons. exact Hin.
  Qed.

  Lemma steps_preserves_has_derived s s' f :
    comp_step^* s s' ->
    has_derived_datalog_fact s f -> has_derived_datalog_fact s' f.
  Proof.
    intros Hsteps Hd. induction Hsteps; [exact Hd|].
    apply IHHsteps. eapply step_preserves_has_derived; eassumption.
  Qed.

  Lemma extract_per_source_dones s pat :
    (forall r, In r p.(program.rules) ->
       exists num, In (message.done_with pat (from_rule r) num) s.(known_facts)) ->
    exists nums,
      Forall2 (fun r num => In (message.done_with pat (from_rule r) num) s.(known_facts))
              sender_rules nums.
  Proof.
    intros H. apply Forall_exists_r_Forall2. apply Forall_forall. intros r Hr.
    apply H. exact (sender_rules_In r Hr).
  Qed.

  Lemma derived_consistent_impl_knows inputs s h :
    good_input_facts inputs ->
    sane_state inputs s ->
    has_derived_datalog_fact s h ->
    mf_consistent_state s h ->
    knows_fact s.(known_facts) h.
  Proof.
    intros Hinp Hsane Hd Hc.
    destruct h as [nf | mf]; [ exact Hd |].
    cbv [has_derived_datalog_fact mf_consistent_state] in Hd, Hc.
    cbn [node.knows_fact]. cbv [meta_fact.rel] in Hd |- *.
    destruct (is_input mf.(meta_fact.pattern).(fact_pattern.rel)) eqn:HER.
    - destruct Hd as (num & Hin & Hexn). exists num. ssplit.
      + rewrite expects_num_facts_eq, HER. exact Hin.
      + exact Hexn.
      + exact Hc.
    - pose proof (extract_per_source_dones s mf.(meta_fact.pattern) Hd) as (nums & Hf2).
      exists (list_sum nums). ssplit.
      + rewrite expects_num_facts_eq, HER. exists nums. split; [exact Hf2 | reflexivity].
      + destruct (Hsane.(sane_count) mf.(meta_fact.pattern))
          as (msgs & num_inp & num_kn & Hf2m & Hexn_inp & Hexn_kn & Hsum).
        pose proof (Existsn_unique _ _ _ _ Hexn_inp (no_matching_inputs _ _ Hinp HER)) as ->.
        pose proof (sane_sent_counts_eq_dones _ _ _ _ _ Hsane Hf2 Hf2m) as ->.
        subst num_kn. exact Hexn_kn.
      + exact Hc.
  Qed.

  Lemma comp_steps_sound inputs s s' :
    good_input_facts inputs ->
    sane_state inputs s ->
    meta_facts_correct s ->
    meta_facts_ok s ->
    state_correct inputs s ->
    comp_step^* s s' ->
    state_correct inputs s'.
  Proof.
    intros Hinp Hsane Hmfc Hmf_ok Hsound Hsteps. revert Hsane Hmfc Hmf_ok Hsound.
    induction Hsteps; intros; auto.
    apply IHHsteps.
    - eapply step_preserves_sane; eassumption.
    - eapply step_preserves_mfs_correct; eassumption.
    - eapply step_preserves_meta_facts_ok; eassumption.
    - eapply comp_step_sound; eassumption.
  Qed.

  Lemma steps_preserves_meta_facts_ok inputs s s' :
    good_input_facts inputs ->
    sane_state inputs s ->
    meta_facts_correct s ->
    meta_facts_ok s ->
    comp_step^* s s' ->
    meta_facts_ok s'.
  Proof.
    intros Hinp Hsane Hmfc Hmf_ok Hsteps. revert Hsane Hmfc Hmf_ok.
    induction Hsteps; intros; auto.
    apply IHHsteps.
    - eapply step_preserves_sane; eassumption.
    - eapply step_preserves_mfs_correct; eassumption.
    - eapply step_preserves_meta_facts_ok; eassumption.
  Qed.

  Lemma compose_completion inputs s hyps :
    good_input_facts inputs ->
    sane_state inputs s ->
    meta_facts_correct s ->
    meta_facts_ok s ->
    state_correct inputs s ->
    Forall (fun h =>
      forall s0,
        sane_state inputs s0 ->
        meta_facts_correct s0 ->
        meta_facts_ok s0 ->
        state_correct inputs s0 ->
        exists s', comp_step^* s0 s' /\ has_derived_datalog_fact s' h) hyps ->
    exists s',
      comp_step^* s s' /\
      Forall (has_derived_datalog_fact s') hyps.
  Proof.
    intros Hinp Hsane Hmfc Hmf_ok Hsound HF.
    revert s Hsane Hmfc Hmf_ok Hsound.
    induction HF as [|h hs Hh Hhs IH]; intros s Hsane Hmfc Hmf_ok Hsound.
    - exists s. split; [apply rt1n_refl|]. constructor.
    - specialize (IH s Hsane Hmfc Hmf_ok Hsound).
      destruct IH as (s_mid & Hsteps_mid & Hderived_hs).
      assert (Hsane_mid : sane_state inputs s_mid) by eauto using steps_preserves_sane.
      assert (Hmfc_mid : meta_facts_correct s_mid) by eauto using steps_preserves_mfs_correct.
      assert (Hmf_ok_mid : meta_facts_ok s_mid) by eauto using steps_preserves_meta_facts_ok.
      assert (Hsound_mid : state_correct inputs s_mid) by eauto using comp_steps_sound.
      destruct (Hh s_mid Hsane_mid Hmfc_mid Hmf_ok_mid Hsound_mid) as (s' & Hsteps' & Hh_derived).
      exists s'. ssplit.
      + eapply crt1n_trans_compose; eassumption.
      + constructor; [exact Hh_derived|].
        eapply Forall_impl; [ exact Hderived_hs | ].
        cbv beta. intros h0. eapply steps_preserves_has_derived; eauto.
  Qed.

  Lemma knows_fact_inputs_has_derived inputs s f :
    good_input_facts inputs ->
    sane_state inputs s ->
    knows_fact inputs f ->
    has_derived_datalog_fact s f.
  Proof.
    intros Hinp Hsane Hkdf.
    pose proof Hsane.(sane_inputs_known) as Hinp_known.
    destruct f as [nf | mf]; cbv [has_derived_datalog_fact] in *.
    - apply Hinp_known. exact Hkdf.
    - simpl in Hkdf. destruct Hkdf as (num & Hexp & Hexn & _).
      rewrite expects_num_facts_eq in Hexp.
      cbv [meta_fact.rel].
      destruct (is_input mf.(meta_fact.pattern).(fact_pattern.rel)) eqn:HER.
      + exists num. split; [ apply Hinp_known; exact Hexp |].
        destruct (Hsane.(sane_count) mf.(meta_fact.pattern))
          as (msgs & num_inp & num_kn & Hf2 & Hexn_inp & Hexn_kn & Hsum).
        pose proof (Existsn_unique _ _ _ _ Hexn_inp Hexn) as ->.
        rewrite (sane_input_sents_0 _ _ _ _ Hsane HER Hf2), Nat.add_0_r in Hsum.
        subst num_kn. exact Hexn_kn.
      + intros r' Hr'. destruct Hexp as (msgss & Hf2 & _).
        destruct (Forall2_In_l _ _ _ _ Hf2 (In_sender_rules r' Hr'))
          as (mk & _ & Hin_mk). cbv beta in Hin_mk.
        exists mk. apply Hinp_known. exact Hin_mk.
  Qed.

  Lemma correct_impl_consistent inputs s f :
    good_input_facts inputs ->
    0 < length p.(program.rules) ->
    state_correct inputs s ->
    program.interp p (knows_fact inputs) f ->
    has_derived_datalog_fact s f ->
    mf_consistent_state s f.
  Proof.
    intros Hinp Hlen Hsound Himpl Hderived.
    destruct f as [nf | mf]; [exact I|].
    cbv [mf_consistent_state fact.set_consistent_with]. intros nf0 Hmatch.
    pose (mf0 := {| meta_fact.pattern := mf.(meta_fact.pattern);
                   meta_fact.set := fun args' =>
                     In (message.normal
                           {| normal_fact.rel := mf.(meta_fact.pattern).(fact_pattern.rel);
                             normal_fact.args := args' |}) s.(known_facts) |}).
    assert (Hc0 : mf_consistent_state s (fact.meta mf0)).
    { intros [nrel nargs] (Hrel & _). cbn in Hrel |- *.
      replace nrel with mf.(meta_fact.pattern).(fact_pattern.rel) by congruence.
      reflexivity. }
    assert (Hd0 : has_derived_datalog_fact s (fact.meta mf0)) by exact Hderived.
    pose proof (Hsound (fact.meta mf0) (conj Hd0 Hc0)) as Himpl0.
    destruct (good_inputs_knows_fact_inputs inputs Hinp Hlen) as (Hrel_disj & Hdoesnt_lie).
    assert (HQagree : forall mf1 mf2,
               knows_fact inputs (fact.meta mf1) ->
               knows_fact inputs (fact.meta mf2) ->
               meta_fact.agree mf1 mf2)
      by eauto using fact.set_doesnt_lie_agree.
    pose proof (program.meta_facts_consistent p (knows_fact inputs) mf mf0
                  Hrel_disj HQagree Hmeta_rules Himpl Himpl0) as Hagree.
    rewrite (Hagree nf0 Hmatch Hmatch). exact (Hc0 nf0 Hmatch).
  Qed.

  (* Fire one deducible normal fact into node [k]'s sent list.  The no-conflict
     precondition of the fire step is discharged from [meta_facts_ok]: a matching
     done-message in [k]'s sent list would, by [ok_to_deduce], already have put the
     fact there, contradicting that it is absent. *)
  Lemma comp_step_fire_normal inputs s rn nf :
    sane_state inputs s ->
    meta_facts_ok s ->
    In rn p.(program.rules) ->
    can_deduce_normal_fact rn s.(known_facts) nf ->
    ~ In (message.normal nf) (get_or_default s.(sents) rn) ->
    exists s',
      comp_step s s' /\
        s'.(known_facts) = message.normal nf :: s.(known_facts) /\
        get_or_default s'.(sents) rn = message.normal nf :: get_or_default s.(sents) rn.
  Proof.
    intros Hsane Hmf_ok Hin_rn Hcdn Hnot_in.
    exists {| known_facts := message.normal nf :: s.(known_facts);
             sents := mupd_with_default (cons (message.normal nf)) s.(sents) rn |}.
    ssplit.
    - apply (fire_rule (message.normal nf) s rn); [ exact Hin_rn |].
      cbv [fire_at_rule].
      cbn [node.can_deduce node.state.known node.state.sent node_prog
           program.rules program.meta_rules].
      split.
      + constructor. exact Hcdn.
      + intros (pat & num & Hin_meta & Hmatch).
        pose proof (Hmf_ok rn Hin_rn _ _ Hin_meta) as Hmfor.
        exact (Hnot_in (Hmfor nf Hcdn Hmatch)).
    - cbn [known_facts]. reflexivity.
    - cbn [sents]. rewrite get_or_default_mupd. destr (eqb rn rn); [ reflexivity | congruence ].
  Qed.

  (* Drive node [rn] to sent-broadcast every fact matching [mf]'s pattern
     that its rule can deduce, so that firing the [(from_rule rn)] done-message
     is [ok_to_deduce].  Termination: the set of such facts is bounded by the
     finite list [l] from [meta_facts_finite] applied to the (real) meta-fact. *)
  Lemma rule_can_force_normal_facts inputs s rn (mf : meta_fact) :
    good_input_facts inputs ->
    0 < length p.(program.rules) ->
    sane_state inputs s ->
    meta_facts_correct s ->
    meta_facts_ok s ->
    state_correct inputs s ->
    In rn p.(program.rules) ->
    program.interp p (knows_fact inputs) (fact.meta mf) ->
    exists s',
      comp_step^* s s' /\
        ok_to_deduce rn s'.(known_facts) (get_or_default s'.(sents) rn)
          mf.(meta_fact.pattern).
  Proof.
    intros Hinp Hlen_pos Hsane Hmfc Hmf_ok Hsound Hin_rn Hpi_meta.
    assert (Hpremise : forall mf',
               knows_fact inputs (fact.meta mf') ->
               exists l, forall args,
                 Forall2 value_pattern.matches
                   mf'.(meta_fact.pattern).(fact_pattern.args) args ->
                 mf'.(meta_fact.set) args -> In args l).
    { intros mf' Hk. destruct Hk as (num & _ & _ & Hbi).
      exists (map (fun m => match m with
                       | message.normal nf0 => nf0.(normal_fact.args)
                       | _ => []
                       end) inputs).
      intros args Hmatch HS.
      specialize (Hbi {| normal_fact.rel := mf'.(meta_fact.pattern).(fact_pattern.rel);
                        normal_fact.args := args |}
                    ltac:(split; [reflexivity | exact Hmatch])).
      cbn [normal_fact.args] in Hbi. apply Hbi in HS.
      apply in_map_iff. eexists. split; [| exact HS]. reflexivity. }
    pose proof (good_inputs_knows_fact_inputs inputs Hinp Hlen_pos) as Hgi.
    pose proof (program.valid_impl_honest p Hmeta_rules _ Hgi) as Hhonest.
    pose proof (Hhonest _ Hpi_meta) as Hcons_meta.
    cbv [fact.set_consistent_with fact.normal_subset] in Hcons_meta.
    assert (Hl_nf : exists l, forall nf,
               fact_pattern.matches mf.(meta_fact.pattern) nf ->
               mf.(meta_fact.set) nf.(normal_fact.args) -> In nf l).
    { destruct (Hmeta_finite (knows_fact inputs) Hpremise mf Hpi_meta) as (l0 & Hl0).
      exists (map (fun a => {| normal_fact.rel := mf.(meta_fact.pattern).(fact_pattern.rel);
                          normal_fact.args := a |}) l0).
      intros [nrel nargs] (Hrel & Hargs) HS. cbn in *.
      apply in_map_iff. exists nargs. split.
      - f_equal. congruence.
      - eauto. }
    destruct Hl_nf as (l & Hl_bound).
    assert (Hl_reachable : forall nf s',
              comp_step^* s s' ->
              In (message.normal nf) s'.(known_facts) ->
              fact_pattern.matches mf.(meta_fact.pattern) nf -> In nf l).
    { intros nf s' Hsteps' Hknows Hmatch.
      apply Hl_bound; [exact Hmatch|]. apply (Hcons_meta nf Hmatch).
      assert (Hsane' : sane_state inputs s') by eauto using steps_preserves_sane.
      assert (Hsound' : state_correct inputs s') by eauto using comp_steps_sound.
      apply Hsound'. split; [ exact Hknows | exact I ]. }
    assert (Hcand0 : forall nf s',
              comp_step^* s s' ->
              In (message.normal nf) s'.(known_facts) ->
              fact_pattern.matches mf.(meta_fact.pattern) nf ->
              In (message.normal nf) (get_or_default s.(sents) rn) \/ In nf l).
    { intros nf s' Hsteps' Hknows Hmatch. right. eapply Hl_reachable; eassumption. }
    clear Hl_reachable Hpi_meta Hl_bound Hhonest Hcons_meta Hgi Hpremise.
    remember (length l) as len eqn:Elen.
    assert (Hlen : length l < S len) by lia. clear Elen.
    revert l s Hlen Hsane Hmfc Hmf_ok Hsound Hcand0. generalize (S len). clear len.
    intros len. induction len as [|len IH]; intros l s Hlen Hsane Hmfc Hmf_ok Hsound Hcand; [lia|].
    destruct (classic (Exists (fun nf =>
                          can_deduce_normal_fact rn s.(known_facts) nf /\
                          fact_pattern.matches mf.(meta_fact.pattern) nf /\
                          ~ In (message.normal nf) (get_or_default s.(sents) rn)) l)) as [Hex | Hno].
    - rewrite Exists_exists in Hex.
      destruct Hex as (nf & Hin_l & Hcdn_nf & Hmatch & Hnot_in_sent).
      apply in_split in Hin_l. destruct Hin_l as (l1 & l2 & Hl_split).
      pose proof (comp_step_fire_normal inputs s rn nf
                    Hsane Hmf_ok Hin_rn Hcdn_nf Hnot_in_sent)
        as (s_fire & Hstep_fire & Hkn_fire & Hgd_fire).
      assert (Hsteps_fire : comp_step^* s s_fire)
        by (eapply Relation_Operators.rt1n_trans; [exact Hstep_fire | apply rt1n_refl]).
      assert (Hsane_fire : sane_state inputs s_fire) by eauto using step_preserves_sane.
      assert (Hmfc_fire : meta_facts_correct s_fire) by eauto using step_preserves_mfs_correct.
      assert (Hmf_ok_fire : meta_facts_ok s_fire) by eauto using step_preserves_meta_facts_ok.
      assert (Hsound_fire : state_correct inputs s_fire) by eauto using comp_step_sound.
      assert (Hcand_fire : forall nf0 s'',
                comp_step^* s_fire s'' ->
                In (message.normal nf0) s''.(known_facts) ->
                fact_pattern.matches mf.(meta_fact.pattern) nf0 ->
                In (message.normal nf0) (get_or_default s_fire.(sents) rn) \/ In nf0 (l1 ++ l2)).
      { intros nf0 s'' Hsteps'' Hkn'' Hmatch''.
        assert (Hsteps_tot : comp_step^* s s'')
          by (eapply crt1n_trans_compose; [exact Hsteps_fire | exact Hsteps'']).
        specialize (Hcand nf0 s'' Hsteps_tot Hkn'' Hmatch'').
        destruct Hcand as [Hc | Hc].
        - left. rewrite Hgd_fire. right. exact Hc.
        - rewrite Hl_split in Hc. apply in_app_iff in Hc. destruct Hc as [Hc | [Hc | Hc]].
          + right. apply in_app_iff. left. exact Hc.
          + subst nf0. left. rewrite Hgd_fire. left. reflexivity.
          + right. apply in_app_iff. right. exact Hc. }
      assert (Hlen' : length (l1 ++ l2) < len).
      { rewrite Hl_split, length_app in Hlen. rewrite length_app. simpl in Hlen. lia. }
      destruct (IH (l1 ++ l2) s_fire Hlen' Hsane_fire Hmfc_fire Hmf_ok_fire Hsound_fire Hcand_fire)
        as (s' & Hsteps' & Hforcing').
      exists s'. ssplit;
        [ eapply crt1n_trans_compose; [exact Hsteps_fire | exact Hsteps'] | exact Hforcing' ].
    - exists s. ssplit; [ apply rt1n_refl |].
      cbv [ok_to_deduce]. intros nf Hcdn_nf Hmatch.
      destruct (classic (In (message.normal nf) (get_or_default s.(sents) rn)))
        as [Hin | Hnin]; [exact Hin|].
      exfalso.
      pose proof (comp_step_fire_normal inputs s rn nf
                    Hsane Hmf_ok Hin_rn Hcdn_nf Hnin)
        as (s_fire & Hstep_fire & Hkn_fire & _).
      assert (Hin_kn_fire : In (message.normal nf) s_fire.(known_facts))
        by (rewrite Hkn_fire; left; reflexivity).
      assert (Hsteps1 : comp_step^* s s_fire)
        by (eapply Relation_Operators.rt1n_trans; [exact Hstep_fire | apply rt1n_refl]).
      specialize (Hcand nf s_fire Hsteps1 Hin_kn_fire Hmatch).
      destruct Hcand as [Hc | Hc].
      + apply Hnin. exact Hc.
      + apply Hno. apply Exists_exists. exists nf.
        split; [exact Hc | split; [exact Hcdn_nf | split; [exact Hmatch | exact Hnin]]].
  Qed.

  (* Fire the [(from_rule rn)] done-message for [pat] at node [rn], given the
     rule's concl/hyp interpretation, that its hyps are known, and [ok_to_deduce]. *)
  Lemma comp_step_fire_meta inputs s rn mr pat mhyps ms :
    sane_state inputs s ->
    In rn p.(program.rules) ->
    In mr p.(program.meta_rules) ->
    Existsn (message.matches pat) ms (get_or_default s.(sents) rn) ->
    meta_rule.pattern_interp mr pat (map meta_fact.pattern mhyps) ->
    Forall (knows_meta_fact s.(known_facts)) mhyps ->
    ok_to_deduce rn s.(known_facts) (get_or_default s.(sents) rn) pat ->
    exists s',
      comp_step s s' /\
        s'.(known_facts) = message.done_with pat (from_rule rn) ms :: s.(known_facts).
  Proof.
    intros Hsane Hin_rn Hin_mr Hexn Hpi Hknow Hok.
    exists {| known_facts := message.done_with pat (from_rule rn) ms :: s.(known_facts);
             sents := mupd_with_default (cons (message.done_with pat (from_rule rn) ms))
                        s.(sents) rn |}.
    split; [| cbn [known_facts]; reflexivity ].
    apply (fire_rule (message.done_with pat (from_rule rn) ms) s rn); [ exact Hin_rn |].
    cbv [fire_at_rule].
    cbn [node.can_deduce node.state.known node.state.sent node_prog
         program.rules program.meta_rules].
    ssplit.
    - reflexivity.
    - apply Exists_exists. exists mr. split; [ exact Hin_mr |].
      exists mhyps. split; [ exact Hpi | exact Hknow ].
    - exact Hexn.
    - intros r0 nf Hin0 Hcdn Hm.
      cbn [node_prog program.rules] in Hin0. destruct Hin0 as [Heq | []]. subst r0.
      exact (Hok nf Hcdn Hm).
  Qed.

  Lemma good_layout_complete_rule inputs s f hyps :
    good_input_facts inputs ->
    sane_state inputs s ->
    meta_facts_correct s ->
    meta_facts_ok s ->
    state_correct inputs s ->
    program.interp_step p f hyps ->
    Forall (has_derived_datalog_fact s) hyps ->
    Forall (mf_consistent_state s) hyps ->
    exists s',
      comp_step^* s s' /\
        has_derived_datalog_fact s' f.
  Proof.
    intros Hinp Hsane Hmfc Hmf_ok Hsound Himpl Hderived Hcons.
    invert Himpl.
    - rename f0 into nf. apply Exists_exists in H. destruct H as (rn & Hin_rn & Hri).
      destruct (classic (In (message.normal nf) s.(known_facts))) as [Hin | Hnin].
      + exists s. split; [apply rt1n_refl | exact Hin].
      + assert (Hcdn : can_deduce_normal_fact rn s.(known_facts) nf).
        { exists hyps. split; [ exact Hri |].
          rewrite Forall_forall. intros h Hh. eapply derived_consistent_impl_knows;
            [ exact Hinp | exact Hsane
            | rewrite Forall_forall in Hderived; apply Hderived; exact Hh
            | rewrite Forall_forall in Hcons; apply Hcons; exact Hh ]. }
        assert (Hnin_sent : ~ In (message.normal nf) (get_or_default s.(sents) rn)).
        { intros Hs. apply Hnin.
          eapply sent_implies_knows; [ exact Hsane | exact Hin_rn | exact Hs ]. }
        pose proof (comp_step_fire_normal inputs s rn nf Hsane Hmf_ok Hin_rn Hcdn Hnin_sent)
          as (s' & Hstep & Hkn & _).
        exists s'. split.
        * eapply Relation_Operators.rt1n_trans; [exact Hstep | apply rt1n_refl].
        * cbv [has_derived_datalog_fact]. rewrite Hkn. left. reflexivity.
    - rename f0 into mf, hyps0 into mhyps.
      apply Exists_exists in H. destruct H as (mr & Hin_mr & Hmri).
      pose proof Hmri as Hmri_save.
      destruct Hmri as (pat & Hpi & Hequiv).
      destruct Hequiv as (Hpe & _). cbn [meta_fact.pattern] in Hpe.
      assert (HR_noninput : is_input pat.(fact_pattern.rel) = false)
        by (eapply pattern_concl_not_input; eassumption).
      assert (Hpi_hyps : Forall (program.interp p (knows_fact inputs)) (map fact.meta mhyps)).
      { rewrite Forall_forall. intros h Hh. apply Hsound. split;
          [ rewrite Forall_forall in Hderived; apply Hderived; exact Hh
          | rewrite Forall_forall in Hcons; apply Hcons; exact Hh ]. }
      assert (Hpi_meta : program.interp p (knows_fact inputs) (fact.meta mf)).
      { eapply pftree.step.
        - constructor. apply Exists_exists. exists mr. split; [exact Hin_mr | exact Hmri_save].
        - exact Hpi_hyps. }
      assert (Hgoal_n : forall rs, incl rs p.(program.rules) ->
                exists s', comp_step^* s s' /\
                  (forall r, In r rs -> exists num,
                     In (message.done_with pat (from_rule r) num) s'.(known_facts))).
      { induction rs as [|r0 rs IH]; intros Hincl.
        - exists s. split; [apply rt1n_refl|]. intros r [].
        - destruct (IH ltac:(intros x Hx; apply Hincl; right; exact Hx))
            as (s' & Hsteps' & Hrs_forced).
          assert (Hin_r0 : In r0 p.(program.rules)) by (apply Hincl; left; reflexivity).
          pose proof (In_length_pos _ _ Hin_r0) as Hlen_pos.
          assert (Hsane' : sane_state inputs s') by eauto using steps_preserves_sane.
          assert (Hmfc' : meta_facts_correct s') by eauto using steps_preserves_mfs_correct.
          assert (Hmf_ok' : meta_facts_ok s') by eauto using steps_preserves_meta_facts_ok.
          assert (Hsound' : state_correct inputs s') by eauto using comp_steps_sound.
          pose proof (rule_can_force_normal_facts inputs s' r0 mf
                        Hinp Hlen_pos Hsane' Hmfc' Hmf_ok' Hsound' Hin_r0 Hpi_meta)
            as (s'' & Hsteps_force & Hforcing).
          rewrite Hpe in Hforcing.
          assert (Hsteps'' : comp_step^* s s'')
            by (eapply crt1n_trans_compose; [exact Hsteps' | exact Hsteps_force]).
          assert (Hsane'' : sane_state inputs s'') by eauto using steps_preserves_sane.
          assert (Hsound'' : state_correct inputs s'') by eauto using comp_steps_sound.
          assert (Hknow_hyps'' : Forall (knows_meta_fact s''.(known_facts)) mhyps).
          { rewrite Forall_forall. intros mh Hmh.
            assert (Hh : In (fact.meta mh) (map fact.meta mhyps)) by (apply in_map, Hmh).
            assert (Hd'' : has_derived_datalog_fact s'' (fact.meta mh)).
            { eapply steps_preserves_has_derived; [ exact Hsteps'' |].
              rewrite Forall_forall in Hderived. apply Hderived. exact Hh. }
            assert (Hc'' : mf_consistent_state s'' (fact.meta mh)).
            { eapply correct_impl_consistent;
                [ exact Hinp | lia | exact Hsound''
                | rewrite Forall_forall in Hpi_hyps; apply Hpi_hyps; exact Hh | exact Hd'' ]. }
            exact (derived_consistent_impl_knows inputs s'' (fact.meta mh)
                     Hinp Hsane'' Hd'' Hc''). }
          destruct (Existsn_total (message.matches pat) (get_or_default s''.(sents) r0))
            as (ms & Hexn_ms).
          pose proof (comp_step_fire_meta inputs s'' r0 mr pat mhyps ms
                        Hsane'' Hin_r0 Hin_mr Hexn_ms Hpi Hknow_hyps'' Hforcing)
            as (s''' & Hstep_fire & Hkn_fire).
          exists s'''. split.
          + eapply crt1n_trans_compose; [ exact Hsteps'' |].
            eapply Relation_Operators.rt1n_trans; [ exact Hstep_fire | apply rt1n_refl ].
          + intros r Hr. destruct Hr as [-> | Hr].
            * exists ms. rewrite Hkn_fire. left. reflexivity.
            * destruct (Hrs_forced r Hr) as (num & Hin_num). exists num.
              pose proof (comp_step_known_incl _ _ Hstep_fire) as Hincl_fire.
              pose proof (comp_steps_known_incl _ _ Hsteps_force) as Hincl_force.
              apply Hincl_fire, Hincl_force. exact Hin_num. }
      specialize (Hgoal_n p.(program.rules) (incl_refl _)).
      destruct Hgoal_n as (s' & Hsteps & Hall).
      exists s'. split; [exact Hsteps|].
      cbv [has_derived_datalog_fact meta_fact.rel]. rewrite Hpe, HR_noninput.
      intros r Hr. apply Hall. exact Hr.
  Qed.

  Definition state_complete (inputs : list message) (s : state) :=
    forall f,
      program.interp p (knows_fact inputs) f ->
      exists s',
        comp_step^* s s' /\
          has_derived_datalog_fact s' f.

  Lemma comp_step_complete inputs s :
    good_input_facts inputs ->
    0 < length p.(program.rules) ->
    sane_state inputs s ->
    meta_facts_correct s ->
    meta_facts_ok s ->
    state_correct inputs s ->
    state_complete inputs s.
  Proof.
    intros Hinp Hlen Hsane Hmfc Hmf_ok Hsound f Himpl.
    set (R := fun (f0 : fact) =>
                forall s0,
                  sane_state inputs s0 ->
                  meta_facts_correct s0 ->
                  meta_facts_ok s0 ->
                  state_correct inputs s0 ->
                  exists s', comp_step^* s0 s' /\ has_derived_datalog_fact s' f0).
    enough (HR : R f).
    { apply HR; assumption. }
    revert f Himpl.
    apply pftree.ind.
    - intros f0 Hkdf s0 Hsane0 Hmfc0 Hmf_ok0 Hsound0.
      exists s0. split; [apply rt1n_refl|].
      eapply knows_fact_inputs_has_derived; eassumption.
    - intros f0 hyps Hstep0 Hforall_pi Hforall_R s0 Hsane0 Hmfc0 Hmf_ok0 Hsound0.
      pose proof (compose_completion inputs s0 hyps Hinp Hsane0 Hmfc0 Hmf_ok0 Hsound0 Hforall_R)
        as (s1 & Hsteps1 & Hderived1).
      assert (Hsane1 : sane_state inputs s1) by eauto using steps_preserves_sane.
      assert (Hmfc1 : meta_facts_correct s1) by eauto using steps_preserves_mfs_correct.
      assert (Hmf_ok1 : meta_facts_ok s1) by eauto using steps_preserves_meta_facts_ok.
      assert (Hsound1 : state_correct inputs s1) by eauto using comp_steps_sound.
      assert (Hcons1 : Forall (mf_consistent_state s1) hyps).
      { apply Forall_forall.
        intros h Hin_h.
        eapply correct_impl_consistent.
        - exact Hinp.
        - exact Hlen.
        - exact Hsound1.
        - rewrite Forall_forall in Hforall_pi. apply Hforall_pi. assumption.
        - rewrite Forall_forall in Hderived1. apply Hderived1. assumption. }
      pose proof (good_layout_complete_rule inputs s1 f0 hyps
                    Hinp Hsane1 Hmfc1 Hmf_ok1 Hsound1 Hstep0 Hderived1 Hcons1)
        as (s2 & Hsteps2 & Hderived2).
      exists s2. split; [|exact Hderived2].
      eapply crt1n_trans_compose; eassumption.
  Qed.

  Definition initial (inputs : list message) : state :=
    {| known_facts := inputs; sents := map.empty |}.

  Lemma good_input_no_node_meta (inputs : list message) pat r num :
    good_input_facts inputs -> ~ In (message.done_with pat (from_rule r) num) inputs.
  Proof.
    intros [Hall _] Hin. rewrite Forall_forall in Hall.
    specialize (Hall _ Hin). cbn in Hall. discriminate.
  Qed.

  Lemma mfc_initial (inputs : list message) : meta_facts_correct (initial inputs).
  Proof.
    unfold meta_facts_correct, initial. cbn [known_facts sents].
    intros r Hr pat num Hin. rewrite get_or_default_empty in Hin. destruct Hin.
  Qed.

  Lemma mfok_initial (inputs : list message) : meta_facts_ok (initial inputs).
  Proof.
    unfold meta_facts_ok, initial. cbn [known_facts sents].
    intros r Hr pat num Hin. rewrite get_or_default_empty in Hin. destruct Hin.
  Qed.

  Lemma sane_initial (inputs : list message) :
    good_input_facts inputs -> sane_state inputs (initial inputs).
  Proof.
    intros Hg. unfold initial. constructor; cbn [known_facts sents].
    - intros pat num H. exact H.
    - intros pat r num H. exfalso. exact (good_input_no_node_meta inputs pat r num Hg H).
    - intros pat. destruct (Existsn_total (message.matches pat) inputs) as (nk & Hnk).
      exists (repeat 0 (length sender_rules)), nk, nk. split; [| split; [| split]].
      + apply Forall2_repeat_r. apply Forall_forall. intros r _.
        rewrite get_or_default_empty. apply Existsn_nil.
      + exact Hnk.
      + exact Hnk.
      + rewrite list_sum_repeat. lia.
    - intros pat HER. split.
      + rewrite values_empty. constructor.
      + intros r num. exact (good_input_no_node_meta inputs pat r num Hg).
    - intros g H. exact H.
  Qed.

  Lemma sc_initial (inputs : list message) :
    0 < length p.(program.rules) ->
    good_input_facts inputs -> state_correct inputs (initial inputs).
  Proof.
    intros Hlen Hg f (Hd & Hmc). destruct f as [nf | mf].
    - cbv [has_derived_datalog_fact] in Hd. unfold initial in Hd. cbn [known_facts] in Hd.
      apply pftree.leaf. exact Hd.
    - cbv [has_derived_datalog_fact] in Hd. cbv [mf_consistent_state] in Hmc.
      unfold initial in Hd, Hmc. cbn [known_facts] in Hd, Hmc.
      destruct (is_input (meta_fact.rel mf)) eqn:HER.
      + apply pftree.leaf. cbn [node.knows_fact].
        destruct Hd as (num & Hin & Hexn). exists num. ssplit.
        * rewrite expects_num_facts_eq. cbv [meta_fact.rel] in HER. rewrite HER. exact Hin.
        * exact Hexn.
        * exact Hmc.
      + exfalso. destruct (length_pos_In _ Hlen) as (r0 & Hin_r0).
        destruct (Hd r0 Hin_r0) as (num & Hin).
        exact (good_input_no_node_meta inputs mf.(meta_fact.pattern) r0 num Hg Hin).
  Qed.

  Theorem prog_impl_iff_comp_step (inputs : list message) (f : fact) :
    0 < length p.(program.rules) ->
    good_input_facts inputs ->
    (program.interp p (knows_fact inputs) f <->
     exists s', comp_step^* (initial inputs) s' /\
                has_derived_datalog_fact s' f /\ mf_consistent_state s' f).
  Proof.
    intros Hlen Hg.
    pose proof (sane_initial inputs Hg) as Hsane.
    pose proof (mfc_initial inputs) as Hmfc.
    pose proof (mfok_initial inputs) as Hmfok.
    pose proof (sc_initial inputs Hlen Hg) as Hsc.
    split.
    - intros Hprog.
      assert (Hcompl : state_complete inputs (initial inputs))
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

Arguments sane_state {_rel _exprvar _fn _aggregator _value rule_eqb sent_map} is_input p input_facts s.
