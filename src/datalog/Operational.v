(*I wrote the semantics, invariants, and most of the important lemma statements in this file.
  However, I wrote basically none of the proof script.  It was all written by Claude Code, with some amount of guidance,
  closely following the analogous proof in this file:
  https://github.com/OwenConoly/ddatalog/blob/30627bc76021fca7f47dd2224e2456d2290360f0/src/SimpleDataflow.v
  Although the proof here is basically conceptually identical to the proof in that file, there is no code shared
  between the two proofs---just a lot of parallels.
  Despite the fact that this proof should be simpler than that one, it is actually significantly longer...
  I will see how well I can get Claude to simplify it.
 *)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Classical_Prop.
From Stdlib Require Import Relations.Relation_Operators Relations.Operators_Properties.

From Datalog Require Import Map Tactics Fp List Datalog Graph Node Default.
From GraphSearch Require Import Dag.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option Eqb.

Import ListNotations.

Notation "R ^*" := (clos_refl_trans_1n _ R) (format "R ^*").
#[global] Hint Constructors clos_refl_trans_1n : core.

Section __.
  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.

  Implicit Types mf_rel : rel.
  Implicit Types mf_args : list (option T).
  Implicit Types nf_args : list T.

  Inductive non_meta_rule :=
  | nmr_normal (_ _ : list clause)
  | nmr_agg (_ : rel) (_ : aggregator) (_ : rel).

  Definition rule_of nmr :=
    match nmr with
    | nmr_normal concls hyps => normal_rule concls hyps
    | nmr_agg concl_rel agg hyp_rel => agg_rule concl_rel agg hyp_rel
    end.

  Context {nmr_eqb : Eqb non_meta_rule} {nmr_eqb_ok : Eqb_ok nmr_eqb}.

  Variant op_source :=
  | from_rule (r : non_meta_rule)
  | from_input.

  #[local] Instance mf_label : mf_labelT := op_source.

  Record prog :=
    { meta_rules : list (list meta_clause * list meta_clause);
      non_meta_rules : list non_meta_rule }.

  Implicit Types known_facts sent_facts input_facts inputs sent : list dfact.
  Implicit Types nf result : dfact.
  Implicit Types p : prog.
  Implicit Types r : non_meta_rule.

  Context {sent_map : map.map non_meta_rule (list dfact)} {sent_map_ok : map.ok sent_map}.

  Record state := { known_facts : list dfact; sents : sent_map }.

  Context (is_input : rel -> bool).

  Context (p : prog).

  Definition sender_rules : list non_meta_rule := dedup eqb p.(non_meta_rules).

  Definition R_senders : rel -> list op_source :=
    fun R => if is_input R then [from_input] else map from_rule sender_rules.

  Local Notation expect_num_R_facts := (expect_num_R_facts R_senders).
  Local Notation knows_datalog_fact := (knows_datalog_fact R_senders).
  Local Notation can_deduce_normal_fact := (can_deduce_normal_fact R_senders).
  Local Notation ok_to_deduce_fact := (ok_to_deduce_fact R_senders).
  Local Notation can_deduce_fact := (can_deduce_fact R_senders).
  Local Notation allowed_inputs := (Node.allowed_inputs R_senders).
  Local Notation knows_incl := (Node.knows_incl R_senders).

  (* [expect_num_R_facts] with the new [R_senders] recovers its old [is_input] form:
     for input relations, a single [None]-declaration; otherwise one [Some k] count
     per node. *)
  Lemma expect_num_R_facts_eq R mf_args known_facts num :
    expect_num_R_facts R mf_args known_facts num <->
    (if is_input R
     then In (meta_dfact R mf_args from_input num) known_facts
     else exists expected_msgss,
       Forall2 (fun r expected_msgs => In (meta_dfact R mf_args (from_rule r) expected_msgs) known_facts)
               sender_rules expected_msgss /\
       num = list_sum expected_msgss).
  Proof.
    unfold Node.expect_num_R_facts, R_senders.
    destruct (is_input R); cbn.
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

  Definition meta_facts_correct_at_rule mrs known r sent :=
    forall R mf_args num,
      In (meta_dfact R mf_args (from_rule r) num) sent ->
      exists mf_concls mf_hyps hyps,
        In (mf_concls, mf_hyps) mrs /\
          can_deduce_meta_fact mf_concls mf_hyps (from_rule r) sent (meta_dfact R mf_args (from_rule r) num) hyps /\
          Forall (knows_datalog_fact known) hyps /\
          (forall mf_set, ~In (meta_fact R mf_args mf_set) hyps).

  Definition meta_facts_correct (s : state) :=
    forall r, In r p.(non_meta_rules) ->
      meta_facts_correct_at_rule p.(meta_rules) s.(known_facts) r (get_or_default s.(sents) r).

  Definition meta_facts_ok_at_rule known r sent :=
    forall mf_rel mf_args num,
      In (meta_dfact mf_rel mf_args (from_rule r) num) sent ->
      ok_to_deduce_fact (rule_of r) known sent
        (meta_dfact mf_rel mf_args (from_rule r) num).

  Definition meta_facts_ok (s : state) :=
    forall r, In r p.(non_meta_rules) ->
      meta_facts_ok_at_rule s.(known_facts) r (get_or_default s.(sents) r).

  Definition add_known_fact f (s : state) :=
    {| known_facts := f :: s.(known_facts); sents := s.(sents) |}.

  Definition can_fire_rule_at r fired_rule :=
    fired_rule = rule_of r \/
      exists mr_concls mr_hyps,
        In (mr_concls, mr_hyps) p.(meta_rules) /\
          fired_rule = meta_rule mr_concls mr_hyps.

  (* The effect of node [r] firing fact [f]: given the global [known] pool and
     the node's sent list [sent], [r] fires some [fired_rule] that deduces [f]. *)
  Definition fire_at_rule (r : non_meta_rule) known (sent : list dfact) (f : dfact) : Prop :=
    exists fired_rule,
      can_fire_rule_at r fired_rule /\
        can_deduce_fact fired_rule (from_rule r) known sent f /\
        ok_to_deduce_fact (rule_of r) known sent f.

  Inductive comp_step : state -> state -> Prop :=
  | fire_rule new_fact s r :
    In r p.(non_meta_rules) ->
    fire_at_rule r s.(known_facts) (get_or_default s.(sents) r) new_fact ->
    comp_step s {| known_facts := new_fact :: s.(known_facts);
                  sents := mupd_with_default (cons new_fact) s.(sents) r |}.

  Definition is_input_fact (f : dfact) :=
    match f with
    | normal_dfact R _ => is_input R
    | meta_dfact R _ from_input _ => is_input R
    | meta_dfact _ _ (from_rule _) _ => false
    end.

  Definition rules_of : list rule :=
    map (fun '(c, h) => meta_rule c h) p.(meta_rules) ++ map rule_of p.(non_meta_rules).

  Context (Hmeta_rules : meta_rules_valid rules_of).

  Definition good_non_meta_rule (r : non_meta_rule) : Prop :=
    match r with
    | nmr_normal cs _ => Forall (fun c => is_input c.(clause_rel) = false) cs
    | nmr_agg concl _ _ => is_input concl = false
    end.

  Context (Hp_input : Forall good_non_meta_rule p.(non_meta_rules)).

  Definition good_meta_rule_inputs (mr : list meta_clause * list meta_clause) : Prop :=
    let '(concls, _) := mr in
    Forall (fun c => is_input c.(meta_clause_rel) = false) concls.

  Context (Hp_meta_input : Forall good_meta_rule_inputs p.(meta_rules)).

  (* Propagation of meta-fact finiteness: analog of SimpleDataflow.v:2505
     [meta_facts_finite].  We constrain the matching nf_args range only,
     because that is all the meta-fact semantics actually pin down (the
     S predicate is opaque on non-matching args).  This makes the leaf
     case provable from finiteness of the inputs list. *)
  Definition meta_facts_finite :=
    forall Q,
      (forall R mf_args S, Q (meta_fact R mf_args S) ->
                            exists l, forall args,
                              Forall2 matches mf_args args -> S args -> In args l) ->
      forall R mf_args S, prog_impl rules_of Q (meta_fact R mf_args S) ->
                          exists l, forall args,
                            Forall2 matches mf_args args -> S args -> In args l.

  Context (Hmeta_finite : meta_facts_finite).

  Definition good_input_facts input_facts :=
    Forall (fun f => is_input_fact f = true) input_facts /\
      (forall R mf_args num,
          In (meta_dfact R mf_args from_input num) input_facts ->
          (forall num0, In (meta_dfact R mf_args from_input num0) input_facts -> num0 = num) /\
            exists num',
              num' <= num /\
                Existsn (dfact_matches R mf_args) num' input_facts).

  Record sane_state {input_facts : list dfact} {s : state} : Prop := {
    sane_input_meta :
      forall R mf_args num,
        In (meta_dfact R mf_args from_input num) s.(known_facts) ->
        In (meta_dfact R mf_args from_input num) input_facts;
    sane_local_meta :
      forall R mf_args r num,
          In (meta_dfact R mf_args (from_rule r) num) s.(known_facts) ->
          Existsn (dfact_matches R mf_args) num (get_or_default s.(sents) r) /\
          In (meta_dfact R mf_args (from_rule r) num) (get_or_default s.(sents) r);
    sane_count :
      forall R mf_args,
        exists msgs_sents num_inp num_known,
          Forall2 (fun r m => Existsn (dfact_matches R mf_args) m (get_or_default s.(sents) r))
                  sender_rules msgs_sents /\
            Existsn (dfact_matches R mf_args) num_inp input_facts /\
            Existsn (dfact_matches R mf_args) num_known s.(known_facts) /\
            num_known = num_inp + list_sum msgs_sents;
    sane_input_rel :
      forall R,
          is_input R = true ->
          (forall mf_args, Forall (fun sent => Existsn (dfact_matches R mf_args) O sent) (values s.(sents))) /\
            (forall mf_args r num, ~In (meta_dfact R mf_args (from_rule r) num) s.(known_facts));
    sane_inputs_known :
      forall f, In f input_facts -> In f s.(known_facts);
  }.

  Arguments sane_state : clear implicits.

  Lemma can_deduce_implies_not_input r kf nf_rel nf_args :
    good_non_meta_rule r ->
    can_deduce_normal_fact (rule_of r) kf nf_rel nf_args ->
    is_input nf_rel = false.
  Proof.
    intros Hgood (hyps & Himpl & _).
    destruct r as [cs hs | concl agg hyp]; simpl in Himpl, Hgood.
    - invert Himpl.
      match goal with
      | H : Exists _ _ |- _ =>
        apply Exists_exists in H; destruct H as (c & Hin_c & Hint)
      end.
      cbv [interp_clause] in Hint. destruct Hint as (nfargs & _ & Heq).
      injection Heq as -> ->.
      rewrite Forall_forall in Hgood. apply Hgood; exact Hin_c.
    - invert Himpl. exact Hgood.
  Qed.

  Lemma sane_count_forall2_fire (P : dfact -> Prop) (m : sent_map) (r : non_meta_rule)
      (f : dfact) (msgs : list nat) (d : nat) :
    In r p.(non_meta_rules) ->
    (forall c, Existsn P c (get_or_default m r) -> Existsn P (c + d) (f :: get_or_default m r)) ->
    Forall2 (fun r0 c => Existsn P c (get_or_default m r0)) sender_rules msgs ->
    exists msgs',
      Forall2 (fun r0 c => Existsn P c (get_or_default (mupd_with_default (cons f) m r) r0)) sender_rules msgs'
      /\ list_sum msgs' = list_sum msgs + d.
  Proof.
    intros Hin_r Hinc Hf2.
    assert (Hoff : forall x c, In x sender_rules -> x <> r ->
              Existsn P c (get_or_default m x) ->
              Existsn P c (get_or_default (mupd_with_default (cons f) m r) x)).
    { intros x c Hx Hxr HRx. rewrite get_or_default_mupd.
      destr (eqb r x); [ exfalso; apply Hxr; congruence | exact HRx ]. }
    assert (Hatr : forall c, Existsn P c (get_or_default m r) ->
              exists c', Existsn P c' (get_or_default (mupd_with_default (cons f) m r) r) /\ id c' = id c + d).
    { intros c HRc. exists (c + d). split; [| reflexivity].
      rewrite get_or_default_mupd. destr (eqb r r); [ exact (Hinc c HRc) | congruence ]. }
    destruct (Forall2_update_at id
                (fun r0 c => Existsn P c (get_or_default m r0))
                (fun r0 c => Existsn P c (get_or_default (mupd_with_default (cons f) m r) r0))
                r d sender_rules msgs
                ltac:(unfold sender_rules; apply NoDup_dedup)
                (proj1 (dedup_preserves_In p.(non_meta_rules) r) Hin_r)
                Hf2 Hoff Hatr) as (msgs' & HF2' & Hsum).
    rewrite !map_id in Hsum.
    exists msgs'. split; [ exact HF2' | exact Hsum ].
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
    destruct Hfire as (fired_rule & Hcfr & Hcan_f & Hok_f).
    destruct new_fact as [nf_rel nf_args | mf_rel mf_args new_source num_msgs].
    - (* fire_rule with a normal_dfact *)
      cbv [can_deduce_fact] in Hcan_f. destruct Hcan_f as (Hcan & Hnometa). clear Hok_f.
      assert (Hfr_eq : fired_rule = rule_of r).
      { destruct Hcan as (hyps & Himpl & _).
        destruct Hcfr as [-> | (mc & mh & _ & ->)]; [reflexivity | invert Himpl]. }
      subst fired_rule.
      assert (Hnf_noninput : is_input nf_rel = false).
      { rewrite Forall_forall in Hp_input. specialize (Hp_input r Hin_r).
        eapply can_deduce_implies_not_input; eassumption. }
      constructor; cbn [known_facts sents].
      + intros R a num [Heq | Hin]; [ discriminate | exact (Hmf_inp _ _ _ Hin) ].
      + intros R a r0 num [Heq | Hin]; [ discriminate | ].
        specialize (Hmf_sent _ _ _ _ Hin). destruct Hmf_sent as (HE & HI).
        rewrite get_or_default_mupd. destr (eqb r r0).
        * assert (Hnmatch : ~ dfact_matches R a (normal_dfact nf_rel nf_args : dfact)).
          { intros (nf_args0 & Heqf & Hmatch). injection Heqf as -> ->.
            exact (Hnometa _ _ HI Hmatch). }
          split; [ apply Existsn_no; [ exact Hnmatch | exact HE ] | right; exact HI ].
        * split; [ exact HE | exact HI ].
      + intros R a. specialize (Hcount R a).
        destruct Hcount as (msgs & num_inp & num_known & Hf2 & Hni & Hnk & Hsum).
        destruct (classic (dfact_matches R a (normal_dfact nf_rel nf_args : dfact))) as [Hm | Hm].
        * assert (Hinc : forall c, Existsn (dfact_matches R a) c (get_or_default (sents s1) r) ->
                    Existsn (dfact_matches R a) (c + 1)
                      (normal_dfact nf_rel nf_args :: get_or_default (sents s1) r)).
          { intros c Hc. rewrite Nat.add_1_r. apply Existsn_yes; [ exact Hm | exact Hc ]. }
          edestruct (sane_count_forall2_fire (dfact_matches R a) (sents s1) r
                       (normal_dfact nf_rel nf_args) msgs 1 Hin_r Hinc Hf2) as (msgs' & Hf2' & Hsum').
          exists msgs', num_inp, (S num_known). ssplit;
            [ exact Hf2' | exact Hni | apply Existsn_yes; [ exact Hm | exact Hnk ] | lia ].
        * assert (Hinc : forall c, Existsn (dfact_matches R a) c (get_or_default (sents s1) r) ->
                    Existsn (dfact_matches R a) (c + 0)
                      (normal_dfact nf_rel nf_args :: get_or_default (sents s1) r)).
          { intros c Hc. rewrite Nat.add_0_r. apply Existsn_no; [ exact Hm | exact Hc ]. }
          edestruct (sane_count_forall2_fire (dfact_matches R a) (sents s1) r
                       (normal_dfact nf_rel nf_args) msgs 0 Hin_r Hinc Hf2) as (msgs' & Hf2' & Hsum').
          exists msgs', num_inp, num_known. ssplit;
            [ exact Hf2' | exact Hni | apply Existsn_no; [ exact Hm | exact Hnk ] | lia ].
      + intros R HR. specialize (Hinp_sane R HR). destruct Hinp_sane as (HForall & Hnone). split.
        * intros a. rewrite mupd_with_default_eq_put.
          apply Forall_values_put; [ exact (HForall a) | ].
          apply Existsn_no.
          -- intros (nf_args0 & Heqf & _). injection Heqf as -> _. congruence.
          -- pose proof (HForall a) as HFa. rewrite Forall_forall in HFa.
             destruct (map.get (sents s1) r) as [v|] eqn:Eg.
             ++ rewrite (get_or_default_Some _ _ _ Eg). apply HFa, In_values. exists r. exact Eg.
             ++ rewrite (get_or_default_None _ _ Eg). apply Existsn_nil.
        * intros a r0 num [Heq | Hin]; [ discriminate | exact (Hnone _ _ _ Hin) ].
      + intros f Hf. right. exact (Hinp_propagated f Hf).
    - (* fire_rule with a meta_dfact *)
      cbv [can_deduce_fact] in Hcan_f.
      destruct Hcan_f as (Hsrc & mr_concls & mr_hyps & hyps & Hfr_eq & Hcdmf & Hknow_hyps).
      subst new_source.
      assert (Hmr_in : In (mr_concls, mr_hyps) p.(meta_rules)).
      { destruct Hcfr as [Hrf_eq | (mc & mh & Hin_mr & Hrf_eq)].
        - rewrite Hrf_eq in Hfr_eq. destruct r; discriminate.
        - rewrite Hrf_eq in Hfr_eq. injection Hfr_eq as -> ->. exact Hin_mr. }
      subst fired_rule.
      cbv [can_deduce_meta_fact] in Hcdmf.
      destruct Hcdmf as (ctx & mfr_t & mfa_t & mfc_t & Hnf_eq & HsentExistsn & Hmc_concl & Hmc_hyps).
      cbv [mf_label] in *. fwd.
      assert (Hmf_rel_noninput : is_input mfr_t = false).
      { rewrite Forall_forall in Hp_meta_input. specialize (Hp_meta_input _ Hmr_in). cbn in Hp_meta_input.
        rewrite Forall_forall in Hp_meta_input.
        apply Exists_exists in Hmc_concl. destruct Hmc_concl as (c & Hin_c & Hint).
        cbv [interp_meta_clause] in Hint. destruct Hint as (mfa & mfs & _ & Heqc).
        injection Heqc as -> _ _. apply (Hp_meta_input _ Hin_c). }
      constructor; cbn [known_facts sents].
      + intros R a num [Heq | Hin]; [ discriminate | exact (Hmf_inp _ _ _ Hin) ].
      + intros R a r0 num Hin. rewrite get_or_default_mupd. destr (eqb r r0).
        * destruct Hin as [Heq | Hin].
          -- injection Heq as -> -> ->.
             split; [ apply Existsn_no; [ intros (? & Hq & _); discriminate | exact HsentExistsn ]
                    | left; reflexivity ].
          -- specialize (Hmf_sent _ _ _ _ Hin). destruct Hmf_sent as (HE & HI).
             split; [ apply Existsn_no; [ intros (? & Hq & _); discriminate | exact HE ]
                    | right; exact HI ].
        * destruct Hin as [Heq | Hin].
          -- injection Heq as -> -> Hr0 ->. congruence.
          -- specialize (Hmf_sent _ _ _ _ Hin). destruct Hmf_sent as (HE & HI).
             split; [ exact HE | exact HI ].
      + intros R a. specialize (Hcount R a).
        destruct Hcount as (msgs & num_inp & num_known & Hf2 & Hni & Hnk & Hsum).
        assert (Hnm : ~ dfact_matches R a (meta_dfact mfr_t mfa_t (from_rule r) mfc_t : dfact)).
        { intros (? & Hq & _). discriminate. }
        assert (Hinc : forall c, Existsn (dfact_matches R a) c (get_or_default (sents s1) r) ->
                  Existsn (dfact_matches R a) (c + 0)
                    (meta_dfact mfr_t mfa_t (from_rule r) mfc_t :: get_or_default (sents s1) r)).
        { intros c Hc. rewrite Nat.add_0_r. apply Existsn_no; [ exact Hnm | exact Hc ]. }
        edestruct (sane_count_forall2_fire (dfact_matches R a) (sents s1) r
                     (meta_dfact mfr_t mfa_t (from_rule r) mfc_t) msgs 0 Hin_r Hinc Hf2)
          as (msgs' & Hf2' & Hsum').
        exists msgs', num_inp, num_known. ssplit;
          [ exact Hf2' | exact Hni | apply Existsn_no; [ exact Hnm | exact Hnk ] | lia ].
      + intros R HR. specialize (Hinp_sane R HR). destruct Hinp_sane as (HForall & Hnone). split.
        * intros a. rewrite mupd_with_default_eq_put.
          apply Forall_values_put; [ exact (HForall a) | ].
          apply Existsn_no.
          -- intros (? & Hq & _). discriminate.
          -- pose proof (HForall a) as HFa. rewrite Forall_forall in HFa.
             destruct (map.get (sents s1) r) as [v|] eqn:Eg.
             ++ rewrite (get_or_default_Some _ _ _ Eg). apply HFa, In_values. exists r. exact Eg.
             ++ rewrite (get_or_default_None _ _ Eg). apply Existsn_nil.
        * intros a r0 num [Heq | Hin].
          -- injection Heq as -> _ _. congruence.
          -- exact (Hnone _ _ _ Hin).
      + intros f Hf. right. exact (Hinp_propagated f Hf).
  Qed.

  Lemma Forall2_nth_error_fwd {A B} (R : A -> B -> Prop) xs ys :
    Forall2 R xs ys ->
    forall n x y,
      nth_error xs n = Some x ->
      nth_error ys n = Some y ->
      R x y.
  Proof.
    induction 1; intros [|n] x' y' Hx Hy; simpl in *; try discriminate.
    - injection Hx as ->. injection Hy as ->. assumption.
    - eapply IHForall2; eassumption.
  Qed.

  Lemma sane_allowed_inputs inputs s :
    good_input_facts inputs ->
    sane_state inputs s ->
    allowed_inputs s.(known_facts).
  Proof.
    intros Hinp Hsane R mf_args ems Hf2.
    assert (Hexp : expect_num_R_facts R mf_args s.(known_facts) (list_sum ems))
      by (exists ems; split; [ exact Hf2 | reflexivity ]).
    rewrite expect_num_R_facts_eq in Hexp.
    destruct Hsane as [Hmf_inp Hmf_sent Hcount Hinp_rel Hinp_known].
    destruct (Hcount R mf_args) as (msgs & num_inp & num_known & Hms & Hinp_cnt & Hkn_cnt & Hsum).
    eapply Existsn_le_of_Existsn; [ exact Hkn_cnt | ]. rewrite Hsum.
    destruct (is_input R) eqn:ER; cbv iota in Hexp.
    - apply Hmf_inp in Hexp.
      destruct Hinp as (_ & Hgc). destruct (Hgc _ _ _ Hexp) as (_ & num' & Hle & Hex').
      pose proof (Existsn_unique _ _ _ _ Hinp_cnt Hex') as ->.
      assert (Hms0 : list_sum msgs = 0).
      { apply list_sum_zero.
        destruct (Hinp_rel R ER) as (Hz & _). specialize (Hz mf_args).
        clear -Hms Hz sent_map_ok nmr_eqb nmr_eqb_ok.
        induction Hms as [| r0 mm l l' Hr0 Hms' IH]; [ constructor | ].
        constructor; [ | exact IH ].
        assert (H0 : Existsn (dfact_matches R mf_args) 0 (get_or_default s.(sents) r0)).
        { destruct (map.get s.(sents) r0) as [v|] eqn:Eg.
          - rewrite (get_or_default_Some _ _ _ Eg).
            rewrite Forall_forall in Hz. apply Hz. rewrite In_values. exists r0. exact Eg.
          - rewrite (get_or_default_None _ _ Eg). apply Existsn_nil. }
        eapply Existsn_unique; [ exact H0 | exact Hr0 ]. }
      rewrite Hms0, Nat.add_0_r. exact Hle.
    - destruct Hexp as (emss & Hexpp0 & Hsum_ems).
      assert (Hni0 : num_inp = 0).
      { destruct Hinp as (Hrel & _).
        enough (Existsn (dfact_matches R mf_args) 0 inputs) as Hno
          by exact (Existsn_unique _ _ _ _ Hinp_cnt Hno).
        apply Forall_not_Existsn_0. apply Forall_forall. intros f Hin_f Hdf.
        destruct Hdf as (nfa & Heqf & _). subst f.
        rewrite Forall_forall in Hrel. specialize (Hrel _ Hin_f). simpl in Hrel. congruence. }
      subst num_inp. cbn [Nat.add]. rewrite Hsum_ems.
      enough (msgs = emss) as -> by lia.
      pose proof (Forall2_length Hms) as Hlen_ms.
      pose proof (Forall2_length Hexpp0) as Hlen_es.
      apply nth_error_ext. intros k.
      destruct (nth_error msgs k) as [mk|] eqn:Hmk, (nth_error emss k) as [ek|] eqn:Hek.
      + f_equal.
        destruct (nth_error sender_rules k) as [rk|] eqn:Hrk;
          [| apply nth_error_None in Hrk; apply nth_error_Some_bound_index in Hmk; lia ].
        pose proof (Forall2_nth_error_fwd _ _ _ Hms k rk mk Hrk Hmk) as HEm. cbv beta in HEm.
        pose proof (Forall2_nth_error_fwd _ _ _ Hexpp0 k rk ek Hrk Hek) as HEe. cbv beta in HEe.
        apply Hmf_sent in HEe. destruct HEe as (HEe_ex & _).
        eapply Existsn_unique; [ exact HEm | exact HEe_ex ].
      + apply nth_error_None in Hek. apply nth_error_Some_bound_index in Hmk. lia.
      + apply nth_error_None in Hmk. apply nth_error_Some_bound_index in Hek. lia.
      + reflexivity.
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
    apply knows_incl_of_submultiset.
    - exists [f]. rewrite Hf. apply Permutation_cons_append.
    - exact (sane_allowed_inputs _ _ Hinp (step_preserves_sane _ _ _ Hinp Hsane Hstep)).
  Qed.

  Lemma meta_facts_correct_at_rule_mono mrs k1 k2 n sent :
    knows_incl k1 k2 ->
    meta_facts_correct_at_rule mrs k1 n sent ->
    meta_facts_correct_at_rule mrs k2 n sent.
  Proof.
    intros Hincl H R mf_args num HIn.
    destruct (H R mf_args num HIn) as (mc & mh & hyps & Hin & Hcd & Hkn & Hns).
    exists mc, mh, hyps. split; [ exact Hin |]. split; [ exact Hcd |].
    split; [ eapply Forall_impl; [ exact Hincl | exact Hkn ] | exact Hns ].
  Qed.

  Lemma at_rule_cons_tail mrs k1 k2 r f sent R mf_args num :
    knows_incl k1 k2 ->
    ~ dfact_matches R mf_args f ->
    meta_facts_correct_at_rule mrs k1 r sent ->
    In (meta_dfact R mf_args (from_rule r) num) sent ->
    exists mfc mfh hyps,
      In (mfc, mfh) mrs /\
        can_deduce_meta_fact mfc mfh (from_rule r) (f :: sent)
          (meta_dfact R mf_args (from_rule r) num) hyps /\
        Forall (knows_datalog_fact k2) hyps /\
        (forall mf_set, ~ In (meta_fact R mf_args mf_set) hyps).
  Proof.
    intros Hincl Hnm H HIn.
    destruct (H R mf_args num HIn) as (mfc & mfh & hyps & Hin0 & Hcan0 & Hkn0 & Hns0).
    exists mfc, mfh, hyps. split; [ exact Hin0 |].
    cbv [can_deduce_meta_fact] in Hcan0 |- *.
    destruct Hcan0 as (ctx0 & mr0 & ma0 & mc0 & Hres0 & HEx0 & Hconcl0 & Hinterp0).
    injection Hres0 as Hr0 Ha0 Hc0. subst mr0 ma0 mc0.
    split; [| split].
    - exists ctx0, R, mf_args, num. split; [ reflexivity |].
      split; [ apply Existsn_no; [ exact Hnm | exact HEx0 ] |].
      split; [ exact Hconcl0 | exact Hinterp0 ].
    - eapply Forall_impl; [ exact Hincl | exact Hkn0 ].
    - exact Hns0.
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
    cbv [fire_at_rule] in Hfire. destruct Hfire as (fired_rule & Hcfr & Hcan_f & Hok_f).
    cbv [meta_facts_correct] in Hmfc |- *. cbn [known_facts sents] in Hmono |- *.
    pose proof (Hmfc r Hin_r) as Hmfc_r.
    intros r0 Hr0. rewrite get_or_default_mupd. destr (eqb r r0);
      [ | eapply meta_facts_correct_at_rule_mono; [ exact Hmono | exact (Hmfc r0 Hr0) ] ].
    intros R mf_args num HIn.
      destruct new_fact as [nf_rel nf_args | new_mfr new_mfa new_source new_mfc].
      + cbv [can_deduce_fact] in Hcan_f. destruct Hcan_f as (_ & Hnometa). clear Hok_f.
        destruct HIn as [Heq | HIn]; [ discriminate | ].
        eapply at_rule_cons_tail; [ exact Hmono | | exact Hmfc_r | exact HIn ].
        intros [nf2 [Heqm Hmatch]]. injection Heqm as -> ->.
        eapply Hnometa; [ exact HIn | exact Hmatch ].
      + cbv [can_deduce_fact] in Hcan_f.
        destruct Hcan_f as (Hsrc & mf_concls & mf_hyps & hyps & Hfr_eq & Hcan & Hknown_h).
        subst new_source.
        assert (Hmr_in : In (mf_concls, mf_hyps) p.(meta_rules)).
        { destruct Hcfr as [Hrf_eq | (mc & mh & Hin_mr & Hrf_eq)].
          - rewrite Hrf_eq in Hfr_eq. destruct r0; discriminate.
          - rewrite Hrf_eq in Hfr_eq. injection Hfr_eq as -> ->. exact Hin_mr. }
        subst fired_rule.
        destruct HIn as [Heq_nf | HIn_old].
        2:{ eapply at_rule_cons_tail; [ exact Hmono | | exact Hmfc_r | exact HIn_old ].
            intros [nf2 [Heqm _]]. discriminate. }
        cbv [can_deduce_meta_fact] in Hcan |- *.
        destruct Hcan as (ctx & mf_rel' & mf_args' & mf_cnt' & Hres & HEx & Hconcl & Hinterp).
        pose proof (eq_trans (eq_sym Heq_nf) Hres) as Hcombined.
        injection Hcombined as Heq_R Heq_args Heq_num. subst mf_rel' mf_args' mf_cnt'.
        assert (HNI_R : is_input R = false).
        { rewrite Forall_forall in Hp_meta_input.
          specialize (Hp_meta_input _ Hmr_in). simpl in Hp_meta_input.
          rewrite Forall_forall in Hp_meta_input.
          apply Exists_exists in Hconcl. destruct Hconcl as (c_concl & Hin_c & Hint_c).
          specialize (Hp_meta_input _ Hin_c).
          cbv [interp_meta_clause] in Hint_c.
          destruct Hint_c as (mfa_v & mfs_v & _ & Heqv).
          injection Heqv as Hrel _ _. rewrite <- Hrel in Hp_meta_input. exact Hp_meta_input. }
        destruct (classic (exists mfs', In (meta_fact R mf_args mfs') hyps)) as [Hself | Hnoself].
        * destruct Hself as (mfs' & Hin_hyp).
          rewrite Forall_forall in Hknown_h. pose proof (Hknown_h _ Hin_hyp) as Hkdf_self.
          simpl in Hkdf_self. destruct Hkdf_self as (num_self & Hexp_self & _ & _).
          rewrite expect_num_R_facts_eq, HNI_R in Hexp_self.
          destruct Hexp_self as (expected_msgss & Hf2 & _).
          destruct (Forall2_In_l _ _ _ _ Hf2
                      (proj1 (dedup_preserves_In p.(non_meta_rules) r0) Hin_r))
            as (num_old & _ & Hin_x_known). cbv beta in Hin_x_known.
          specialize (Hmf_sent _ _ _ _ Hin_x_known). destruct Hmf_sent as (_ & Hin_x_sent).
          specialize (Hmfc_r R mf_args num_old Hin_x_sent).
          destruct Hmfc_r as (mfc_old & mfh_old & hyps_old & Hin_mr_old & Hcan_old & Hknown_old & Hnoself_old).
          exists mfc_old, mfh_old, hyps_old. split; [ exact Hin_mr_old |].
          cbv [can_deduce_meta_fact] in Hcan_old |- *.
          destruct Hcan_old as (ctx_old & mro & mao & mco & Hres_old & HEx_old & Hconcl_old & Hinterp_old).
          injection Hres_old as Hr_o Ha_o _. subst mro mao.
          split; [| split].
          -- exists ctx_old, R, mf_args, num. split; [reflexivity|]. split.
             { apply Existsn_no; [| exact HEx]. intros [nf_args2 [Heq _]]. discriminate. }
             split; [exact Hconcl_old|]. exact Hinterp_old.
          -- eapply Forall_impl; [ exact Hmono | exact Hknown_old ].
          -- exact Hnoself_old.
        * exists mf_concls, mf_hyps, hyps. split; [ exact Hmr_in |].
          split; [| split].
          { exists ctx, R, mf_args, num. split; [reflexivity|]. split.
            { apply Existsn_no; [| exact HEx]. intros [nf_args2 [Heq _]]. discriminate. }
            split; [exact Hconcl|]. exact Hinterp. }
          { eapply Forall_impl; [ exact Hmono | exact Hknown_h ]. }
          { intros mfs Hin'. apply Hnoself. exists mfs. exact Hin'. }
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
    | normal_fact R args => In (normal_dfact R args) s.(known_facts)
    | meta_fact R mf_args mf_set =>
        if is_input R then
          exists num,
            In (meta_dfact R mf_args from_input num) s.(known_facts) /\
              Existsn (dfact_matches R mf_args) num s.(known_facts)
        else
          forall r, In r p.(non_meta_rules) ->
            exists num,
              In (meta_dfact R mf_args (from_rule r) num) s.(known_facts)
    end.

  Definition mf_consistent_state (s : state) (f : fact) :=
    match f with
    | normal_fact _ _ => True
    | meta_fact R mf_args mf_set =>
        forall nf_args,
          Forall2 matches mf_args nf_args ->
          mf_set nf_args <-> In (normal_dfact R nf_args) s.(known_facts)
    end.

  Definition state_correct (inputs : list dfact) (s : state) :=
    forall f,
      has_derived_datalog_fact s f /\ mf_consistent_state s f ->
      prog_impl rules_of (knows_datalog_fact inputs) f.

  (* Lift a per-rule [knows_datalog_fact rs.known h] to [has_derived_datalog_fact s h]
     for any rs in s.  For normal facts this is just "exists rs with the dfact".  For
     meta facts the input branch uses the [expect_num_R_facts] count directly; the
     non-input branch extracts the per-source-rule count witness from the Forall2. *)
  Lemma knows_datalog_fact_local_lift_has_derived s h :
    knows_datalog_fact s.(known_facts) h ->
    has_derived_datalog_fact s h.
  Proof.
    intros Hkdf. destruct h as [R0 args0 | R0 mf_args0 mf_set0]; cbn [has_derived_datalog_fact].
    - exact Hkdf.
    - destruct Hkdf as (num & Hexp & Hexn & _).
      rewrite expect_num_R_facts_eq in Hexp. destruct (is_input R0) eqn:HER0.
      + exists num. split; [ exact Hexp | exact Hexn ].
      + intros r Hr. destruct Hexp as (msgss & Hf2 & _).
        destruct (Forall2_In_l _ _ _ _ Hf2 (proj1 (dedup_preserves_In p.(non_meta_rules) r) Hr))
          as (m & _ & Hin_m). cbv beta in Hin_m.
        exists m. exact Hin_m.
  Qed.

  Lemma knows_datalog_fact_local_lift_mf_consistent s h :
    knows_datalog_fact s.(known_facts) h ->
    mf_consistent_state s h.
  Proof.
    intros Hkdf.
    destruct h as [R0 args0 | R0 mf_args0 mf_set0]; cbn [mf_consistent_state]; [exact I|].
    intros nf_args Hmatch. destruct Hkdf as (num & _ & _ & Hbic). exact (Hbic nf_args Hmatch).
  Qed.

  Lemma good_inputs_knows_datalog_fact_inputs inputs :
    good_input_facts inputs ->
    0 < length p.(non_meta_rules) ->
    good_inputs rules_of (knows_datalog_fact inputs).
  Proof.
    intros Hinp Hlt. split.
    - intros f Hf. destruct f as [R0 args0 | R0 mf_args0 mf_set0]; simpl in Hf.
      + destruct Hinp as (Hinp_all & _). rewrite Forall_forall in Hinp_all.
        specialize (Hinp_all _ Hf). simpl in Hinp_all.
        intros Hin_concl. apply in_flat_map in Hin_concl.
        destruct Hin_concl as (r0 & Hin_r0 & Hin_rel).
        unfold rules_of in Hin_r0. apply in_app_or in Hin_r0.
        destruct Hin_r0 as [Hin_meta | Hin_nm].
        * apply in_map_iff in Hin_meta.
          destruct Hin_meta as ((c0, h0) & Heq & Hin_mr0). subst r0.
          simpl in Hin_rel. apply in_map_iff in Hin_rel.
          destruct Hin_rel as (mc & Hrel_eq & Hin_mc).
          rewrite Forall_forall in Hp_meta_input.
          specialize (Hp_meta_input _ Hin_mr0). simpl in Hp_meta_input.
          rewrite Forall_forall in Hp_meta_input.
          specialize (Hp_meta_input _ Hin_mc).
          rewrite Hrel_eq in Hp_meta_input. congruence.
        * apply in_map_iff in Hin_nm.
          destruct Hin_nm as (nmr & Heq & Hin_nmr). subst r0.
          rewrite Forall_forall in Hp_input.
          specialize (Hp_input _ Hin_nmr).
          destruct nmr as [cs hs | cr ag hr]; simpl in Hin_rel, Hp_input.
          -- apply in_map_iff in Hin_rel.
             destruct Hin_rel as (c & Hrel_eq & Hin_c).
             rewrite Forall_forall in Hp_input. specialize (Hp_input _ Hin_c).
             rewrite Hrel_eq in Hp_input. congruence.
          -- destruct Hin_rel as [Hrel_eq|[]]. subst cr. congruence.
      + destruct Hf as (num0 & Hexp & _ & _).
        rewrite expect_num_R_facts_eq in Hexp.
        destruct (is_input R0) eqn:HER0.
        * intros Hin_concl. apply in_flat_map in Hin_concl.
          destruct Hin_concl as (r0 & Hin_r0 & Hin_rel).
          unfold rules_of in Hin_r0. apply in_app_or in Hin_r0.
          destruct Hin_r0 as [Hin_meta | Hin_nm].
          -- apply in_map_iff in Hin_meta.
             destruct Hin_meta as ((c0, h0) & Heq & Hin_mr0). subst r0.
             simpl in Hin_rel. apply in_map_iff in Hin_rel.
             destruct Hin_rel as (mc & Hrel_eq & Hin_mc).
             rewrite Forall_forall in Hp_meta_input.
             specialize (Hp_meta_input _ Hin_mr0). simpl in Hp_meta_input.
             rewrite Forall_forall in Hp_meta_input.
             specialize (Hp_meta_input _ Hin_mc).
             rewrite Hrel_eq in Hp_meta_input. simpl in Hp_meta_input. congruence.
          -- apply in_map_iff in Hin_nm.
             destruct Hin_nm as (nmr & Heq & Hin_nmr). subst r0.
             rewrite Forall_forall in Hp_input.
             specialize (Hp_input _ Hin_nmr).
             destruct nmr as [cs hs | cr ag hr]; simpl in Hin_rel, Hp_input.
             ++ apply in_map_iff in Hin_rel.
                destruct Hin_rel as (c & Hrel_eq & Hin_c).
                rewrite Forall_forall in Hp_input. specialize (Hp_input _ Hin_c).
                rewrite Hrel_eq in Hp_input. simpl in Hp_input. congruence.
             ++ destruct Hin_rel as [Hrel_eq|[]]. subst cr. simpl in Hp_input.
                congruence.
        * destruct Hexp as (msgss & Hf2_msgs & _).
          destruct p.(non_meta_rules) as [| r0 rest] eqn:Enm; [ simpl in Hlt; lia | ].
          assert (Hin_r0 : In r0 sender_rules).
          { unfold sender_rules. apply (proj1 (dedup_preserves_In p.(non_meta_rules) r0)).
            rewrite Enm. left. reflexivity. }
          destruct (Forall2_In_l _ _ _ _ Hf2_msgs Hin_r0) as (m0 & _ & Hin_m0).
          cbv beta in Hin_m0.
          destruct Hinp as (Hinp_all & _). rewrite Forall_forall in Hinp_all.
          specialize (Hinp_all _ Hin_m0). simpl in Hinp_all. congruence.
    - cbv [doesnt_lie consistent]. intros mfr0 mfa0 mfs0 Hin nf_args0 Hmatch_nf.
      simpl in Hin. destruct Hin as (num0 & _ & _ & Hbic).
      simpl. apply Hbic. exact Hmatch_nf.
  Qed.

  Lemma matches_map_Some (args ga : list T) :
    Forall2 matches (map Some args) ga -> ga = args.
  Proof.
    revert ga. induction args as [|a args IH]; intros [|y ga] H; invert H; auto.
    cbn [matches] in *. f_equal; [symmetry; assumption | apply IH; assumption].
  Qed.

  Lemma dfact_matches_exact (R : rel) (nf_args : list T) (g : dfact) :
    dfact_matches R (map Some nf_args) g <-> g = normal_dfact R nf_args.
  Proof.
    cbv [dfact_matches]. split.
    - intros (ga & -> & Hf2). apply matches_map_Some in Hf2. subst. reflexivity.
    - intros ->. exists nf_args. split; [reflexivity|].
      clear. induction nf_args as [|a l IH]; cbn [map]; constructor;
        [cbn [matches]; reflexivity | exact IH].
  Qed.

  (* A normal fact that some node has SENT is known somewhere in the system: firing
     it broadcast it to every node's waiting (and it stays in known∪waiting).  The
     [sane_state] count invariant pins this: a matching fact in any [sent] forces
     [num_known + num_wait >= 1] at every node. *)
  Lemma sent_implies_knows inputs s (R : rel) (nf_args : list T) r :
    sane_state inputs s ->
    In r p.(non_meta_rules) ->
    In (normal_dfact R nf_args) (get_or_default s.(sents) r) ->
    In (normal_dfact R nf_args) s.(known_facts).
  Proof.
    intros Hsane Hin_r Hin_nf.
    destruct (Hsane.(sane_count) R (map Some nf_args))
      as (msgs_sents & num_inp & num_known & Hf2_sent & _ & Hkn & Hsum).
    destruct (Forall2_In_l _ _ _ _ Hf2_sent
                (proj1 (dedup_preserves_In p.(non_meta_rules) r) Hin_r))
      as (ms & Hin_comb & Hexn_sent). cbv beta in Hexn_sent.
    assert (Hms_pos : 1 <= ms).
    { destruct ms; [|lia]. apply Existsn_0_Forall_not in Hexn_sent.
      rewrite Forall_forall in Hexn_sent. exfalso.
      apply (Hexn_sent (normal_dfact R nf_args) Hin_nf).
      apply dfact_matches_exact. reflexivity. }
    assert (Hpos : 1 <= num_known).
    { rewrite Hsum. pose proof (in_le_list_sum ms msgs_sents (in_combine_r _ _ _ _ Hin_comb)). lia. }
    destruct num_known; [lia|].
    apply Existsn_S in Hkn. destruct Hkn as (l1 & xx & l2 & -> & Hpx & _).
    apply dfact_matches_exact in Hpx. subst xx. apply in_or_app. right. left. reflexivity.
  Qed.

  Lemma use_meta_facts_correct (R : rel) (mf_args : list (option T))
    (inputs : list dfact) (s : state) :
    good_input_facts inputs ->
    sane_state inputs s ->
    meta_facts_correct s ->
    meta_facts_ok s ->
    is_input R = false ->
    (forall mf_rel' mf_args' mf_set',
        (R, mf_args) <> (mf_rel', mf_args') ->
        has_derived_datalog_fact s (meta_fact mf_rel' mf_args' mf_set') /\
        mf_consistent_state s (meta_fact mf_rel' mf_args' mf_set') ->
        prog_impl rules_of (knows_datalog_fact inputs) (meta_fact mf_rel' mf_args' mf_set')) ->
    has_derived_datalog_fact s (meta_fact R mf_args (fun _ => True)) ->
    forall nf_args,
      Forall2 matches mf_args nf_args ->
      prog_impl rules_of (knows_datalog_fact inputs) (normal_fact R nf_args) ->
      In (normal_dfact R nf_args) s.(known_facts).
  Proof.
    intros Hinp Hsane Hmf Hmf_ok HER HRs HR nf_args Hmatch Hprog.
    invert Hprog.
    - simpl in H.
      destruct Hinp as (Hinp_all & _). rewrite Forall_forall in Hinp_all.
      specialize (Hinp_all _ H). simpl in Hinp_all. congruence.
    - rename H into Hrule_exists. rename H0 into Hhyps. rename l into hyps.
      apply Exists_exists in Hrule_exists.
      destruct Hrule_exists as (r & Hin_r & Hrule_impl).
      invert Hrule_impl.
      match goal with H : non_meta_rule_impl _ _ _ _ |- _ => rename H into Hnmri end.
      unfold rules_of in Hin_r. apply in_app_or in Hin_r.
      destruct Hin_r as [Hin_meta_r | Hin_nonmeta_r].
      { apply in_map_iff in Hin_meta_r. destruct Hin_meta_r as ((c & h) & Heq_r & _).
        subst r. invert Hnmri. }
      apply in_map_iff in Hin_nonmeta_r.
      destruct Hin_nonmeta_r as (r_k & Heq_r & Hin_rk). subst r.
      simpl in HR. rewrite HER in HR.
      specialize (HR _ Hin_rk). destruct HR as (num_k & Hkknows).
      pose proof Hsane as [_ Hmf_sent _ _ _].
      pose proof (Hmf_sent _ _ _ _ Hkknows) as (Hexn_k & Hin_k_sent).
      pose proof (Hmf r_k Hin_rk _ _ _ Hin_k_sent) as Hmfc_rk.
      destruct Hmfc_rk as (mf_concls & mf_hyps & hyps_d & Hin_mr & Hcan & Hkdf_h & Hnoselfref_h).
      cbv [can_deduce_meta_fact] in Hcan.
      destruct Hcan as (ctx & mf_rel_c & mf_args_c & mf_cnt_c
                       & Heq_F & Hexn_F & Hconcl & Hf2_h).
      injection Heq_F as Hr_eq Ha_eq Hc_eq. subst mf_rel_c mf_args_c mf_cnt_c.
      pose proof (Hmf_ok r_k Hin_rk _ _ _ Hin_k_sent) as Hsound_can.
      cbv [ok_to_deduce_fact] in Hsound_can.
      assert (Hcan_nf : can_deduce_normal_fact (rule_of r_k) s.(known_facts) R nf_args).
      { cbv [can_deduce_normal_fact]. exists hyps. split; [exact Hnmri|].
        pose (S_constr := fun args'' => one_step_derives rules_of hyps_d R args'').
        assert (Hmr_impl :
                  rule_impl (one_step_derives rules_of) (meta_rule mf_concls mf_hyps)
                    (meta_fact R mf_args S_constr) hyps_d).
        { apply meta_rule_impl with (ctx := ctx).
          - eapply Exists_impl; [|exact Hconcl].
            intros c Hclause. cbv [interp_meta_clause] in Hclause |- *.
            destruct Hclause as (mfa_v & mfs_v & Hf2_v & Heq_v).
            injection Heq_v as Hcrel Hcargs _.
            exists mfa_v, S_constr. rewrite Hcargs. split; [exact Hf2_v|].
            rewrite <- Hcrel. reflexivity.
          - exact Hf2_h.
          - intros args'' Hmatch_args''. subst S_constr. reflexivity. }
        assert (Hnr_impl :
                  rule_impl (one_step_derives rules_of) (rule_of r_k)
                    (normal_fact R nf_args) hyps).
        { apply simple_rule_impl. exact Hnmri. }
        assert (Hin_mr_rules : In (meta_rule mf_concls mf_hyps) rules_of).
        { unfold rules_of. apply in_or_app. left. apply in_map_iff.
          exists (mf_concls, mf_hyps). split; [reflexivity|exact Hin_mr]. }
        assert (Hin_nr_rules : In (rule_of r_k) rules_of).
        { unfold rules_of. apply in_or_app. right. apply in_map. exact Hin_rk. }
        pose proof (Hmeta_rules _ _ _ _ _ Hin_mr_rules Hmr_impl _ _ _
                                Hin_nr_rules Hnr_impl Hmatch) as Hpot.
        rewrite Forall_forall. intros h Hh.
        rewrite Forall_forall in Hpot, Hkdf_h, Hhyps.
        pose proof (Hpot _ Hh) as Hpot_h.
        pose proof (Hhyps _ Hh) as Hprog_h.
        assert (Hgood_inputs_Q : good_inputs rules_of (knows_datalog_fact inputs)).
        { apply good_inputs_knows_datalog_fact_inputs; [exact Hinp|].
          remember p.(non_meta_rules) as nmrs eqn:E.
          destruct nmrs as [|a l0]; [ destruct Hin_rk | cbn [length]; lia ]. }
        pose proof (valid_impl_honest _ Hmeta_rules _ Hgood_inputs_Q) as Hhonest.
        cbv [doesnt_lie] in Hhonest.
        destruct h as [R' args' | R' mf_args' mf_set'_h].
        + cbv [fact_potentially_supported] in Hpot_h.
          destruct Hpot_h as (mf_args' & mf_set'_m & Hin_m & Hmatch_m).
          pose proof (Hkdf_h _ Hin_m) as Hkd_m.
          destruct (classic ((R, mf_args) = (R', mf_args'))) as [Heq | Hne].
          * exfalso. injection Heq as -> ->. apply (Hnoselfref_h mf_set'_m). exact Hin_m.
          * pose proof (knows_datalog_fact_local_lift_has_derived _ _ Hkd_m) as Hhd_m.
            pose proof (knows_datalog_fact_local_lift_mf_consistent _ _ Hkd_m) as Hmc_m.
            pose proof (HRs _ _ _ Hne (conj Hhd_m Hmc_m)) as Hprog_m.
            pose proof (Hhonest _ _ _ Hprog_m) as Hcon_m.
            cbv [consistent] in Hcon_m. specialize (Hcon_m _ Hmatch_m).
            apply Hcon_m in Hprog_h.
            simpl in Hkd_m. destruct Hkd_m as (num_m & _ & _ & Hbic_m).
            specialize (Hbic_m _ Hmatch_m). simpl. apply Hbic_m. exact Hprog_h.
        + cbv [fact_potentially_supported] in Hpot_h.
          destruct Hpot_h as (mf_set'_m & Hin_m).
          pose proof (Hkdf_h _ Hin_m) as Hkd_m.
          destruct (classic ((R, mf_args) = (R', mf_args'))) as [Heq | Hne].
          * exfalso. injection Heq as -> ->. apply (Hnoselfref_h mf_set'_m). exact Hin_m.
          * pose proof (knows_datalog_fact_local_lift_has_derived _ _ Hkd_m) as Hhd_m.
            pose proof (knows_datalog_fact_local_lift_mf_consistent _ _ Hkd_m) as Hmc_m.
            pose proof (HRs _ _ _ Hne (conj Hhd_m Hmc_m)) as Hprog_m.
            pose proof (Hhonest _ _ _ Hprog_m) as Hcon_m.
            pose proof (Hhonest _ _ _ Hprog_h) as Hcon_h.
            cbv [consistent] in Hcon_m, Hcon_h.
            simpl in Hkd_m |- *.
            destruct Hkd_m as (num_m & Hexp_m & Hexn_m & Hbic_m).
            exists num_m. split; [exact Hexp_m|]. split; [exact Hexn_m|].
            intros nf_args0 Hmatch_nf.
            specialize (Hbic_m _ Hmatch_nf).
            specialize (Hcon_m _ Hmatch_nf).
            specialize (Hcon_h _ Hmatch_nf).
            rewrite Hcon_h, <- Hcon_m. exact Hbic_m. }
      specialize (Hsound_can _ Hcan_nf Hmatch).
      eapply sent_implies_knows; [ exact Hsane | exact Hin_rk | exact Hsound_can ].
  Qed.

  Lemma ok_to_deduce_grow k1 k2 r sent node mf_rel mf_args num mf_concls mf_hyps mr_hyps_d :
    In r p.(non_meta_rules) ->
    knows_incl k1 k2 ->
    In (mf_concls, mf_hyps) p.(meta_rules) ->
    can_deduce_meta_fact mf_concls mf_hyps node sent (meta_dfact mf_rel mf_args node num) mr_hyps_d ->
    Forall (knows_datalog_fact k1) mr_hyps_d ->
    ok_to_deduce_fact (rule_of r) k1 sent (meta_dfact mf_rel mf_args node num) ->
    ok_to_deduce_fact (rule_of r) k2 sent (meta_dfact mf_rel mf_args node num).
  Proof.
    intros Hin_r Hincl Hin_mr Hcdmf Hknown_mr Hok nf_args Hcdn Hmatch.
    destruct Hcdn as (local_hyps & Hnmri & Hknown_local_big).
    pose (S_constr := fun args'' => one_step_derives rules_of mr_hyps_d mf_rel args'').
    assert (Hri_meta : rule_impl (one_step_derives rules_of) (meta_rule mf_concls mf_hyps)
                        (meta_fact mf_rel mf_args S_constr) mr_hyps_d).
    { cbv [can_deduce_meta_fact] in Hcdmf.
      destruct Hcdmf as (ctx_m & mr' & ma' & mc' & Heq_m & _ & Hconcl_m & Hinterp_m).
      inversion Heq_m. subst mr' ma' mc'. clear Heq_m.
      eapply meta_rule_impl with (ctx := ctx_m).
      - eapply Exists_impl; [| exact Hconcl_m].
        intros c (mfa & mfs & Hf2 & Heqv). injection Heqv as Hrel Hargs _.
        exists mfa, S_constr. split; [exact Hf2|]. rewrite Hargs, Hrel. reflexivity.
      - exact Hinterp_m.
      - intros args'' _. subst S_constr. reflexivity. }
    assert (Hri_normal : rule_impl (one_step_derives rules_of) (rule_of r)
                          (normal_fact mf_rel nf_args) local_hyps)
      by (apply simple_rule_impl; exact Hnmri).
    assert (Hin_mr_rules : In (meta_rule mf_concls mf_hyps) rules_of)
      by (cbv [rules_of]; apply in_app_iff; left; apply in_map_iff;
          exists (mf_concls, mf_hyps); split; [reflexivity | exact Hin_mr]).
    assert (Hin_nr_rules : In (rule_of r) rules_of)
      by (cbv [rules_of]; apply in_app_iff; right; apply in_map; exact Hin_r).
    pose proof (Hmeta_rules _ _ _ _ _ Hin_mr_rules Hri_meta _ _ _ Hin_nr_rules Hri_normal Hmatch)
      as Hpot.
    apply (Hok nf_args); [| exact Hmatch].
    exists local_hyps. split; [exact Hnmri |].
    rewrite Forall_forall in Hknown_local_big, Hpot |- *. intros h Hh.
    eapply knows_datalog_fact_transfer_down;
      [ exact Hincl | exact Hknown_mr | apply Hpot; exact Hh | apply Hknown_local_big; exact Hh ].
  Qed.

  Lemma meta_facts_ok_at_rule_grow k1 k2 r sent :
    In r p.(non_meta_rules) ->
    knows_incl k1 k2 ->
    meta_facts_correct_at_rule p.(meta_rules) k1 r sent ->
    meta_facts_ok_at_rule k1 r sent ->
    meta_facts_ok_at_rule k2 r sent.
  Proof.
    intros Hin_r Hincl Hc Hok mf_rel mf_args num HIn.
    destruct (Hc _ _ _ HIn) as (mf_concls & mf_hyps & mr_hyps_d & Hin_mr & Hcdmf & Hknown_mr & _).
    eapply ok_to_deduce_grow;
      [ exact Hin_r | exact Hincl | exact Hin_mr | exact Hcdmf | exact Hknown_mr
      | exact (Hok _ _ _ HIn) ].
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
    cbv [fire_at_rule] in Hfire. destruct Hfire as (fired_rule & Hcfr & Hcan_f & Hok_f).
    cbv [meta_facts_ok] in Hmf_ok |- *. cbv [meta_facts_correct] in Hmfc.
    cbn [known_facts sents] in Hmono |- *.
    pose proof (Hmf_ok r Hin_r) as Hmfok_r. pose proof (Hmfc r Hin_r) as Hmfc_r.
    intros r0 Hr0. rewrite get_or_default_mupd. destr (eqb r r0);
      [ | eapply meta_facts_ok_at_rule_grow;
          [ exact Hr0 | exact Hmono | exact (Hmfc r0 Hr0) | exact (Hmf_ok r0 Hr0) ] ].
    intros mf_rel mf_args num HIn.
    destruct new_fact as [nf_rel nf_args | new_mfr new_mfa new_source new_mfc].
    - destruct HIn as [Heq | HIn_old]; [ discriminate | ].
      intros nf_args0 Hcdn0 Hmatch0. right.
      exact (meta_facts_ok_at_rule_grow _ _ _ _ Hin_r Hmono Hmfc_r Hmfok_r
               mf_rel mf_args num HIn_old nf_args0 Hcdn0 Hmatch0).
    - destruct HIn as [Heq | HIn_old].
      2:{ intros nf_args0 Hcdn0 Hmatch0. right.
          exact (meta_facts_ok_at_rule_grow _ _ _ _ Hin_r Hmono Hmfc_r Hmfok_r
                   mf_rel mf_args num HIn_old nf_args0 Hcdn0 Hmatch0). }
      cbv [can_deduce_fact] in Hcan_f.
      destruct Hcan_f as (Hsrc & mf_concls & mf_hyps & hyps & Hfr_eq & Hcan & Hknown_h).
      subst new_source.
      assert (Hmr_in : In (mf_concls, mf_hyps) p.(meta_rules)).
      { destruct Hcfr as [Hrf_eq | (mc & mh & Hin_mr & Hrf_eq)].
        - rewrite Hrf_eq in Hfr_eq. destruct r0; discriminate.
        - rewrite Hrf_eq in Hfr_eq. injection Hfr_eq as -> ->. exact Hin_mr. }
      subst fired_rule.
      injection Heq as Hr Ha Hn. subst new_mfr new_mfa new_mfc.
      intros nf_args0 Hcdn0 Hmatch0. right.
      exact (ok_to_deduce_grow _ _ _ (get_or_default (sents s) r0) _ mf_rel mf_args num
               mf_concls mf_hyps hyps Hin_r Hmono Hmr_in Hcan Hknown_h Hok_f nf_args0 Hcdn0 Hmatch0).
  Qed.

  Lemma Existsn_cons_no_iff (P : dfact -> Prop) x n l :
    ~ P x -> (Existsn P n (x :: l) <-> Existsn P n l).
  Proof.
    intros Hx. split.
    - intro H. inversion H; subst; [ assumption | exfalso; auto ].
    - intro H. apply Existsn_no; assumption.
  Qed.

  Lemma has_derived_input_meta_cons_bw R mf_args mf_set F s :
    is_input R = true ->
    ~ dfact_matches R mf_args F ->
    (forall num, F <> meta_dfact R mf_args from_input num) ->
    has_derived_datalog_fact (add_known_fact F s) (meta_fact R mf_args mf_set) ->
    has_derived_datalog_fact s (meta_fact R mf_args mf_set).
  Proof.
    intros HER Hnm Hnd Hf. cbv [has_derived_datalog_fact add_known_fact] in Hf |- *.
    cbn [known_facts] in Hf. rewrite HER in Hf |- *.
    destruct Hf as (num & Hin & Hexn). exists num. split.
    - destruct Hin as [Heq | Hin]; [ exfalso; exact (Hnd num Heq) | exact Hin ].
    - exact (proj1 (Existsn_cons_no_iff _ F num s.(known_facts) Hnm) Hexn).
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
    cbv [fire_at_rule] in Hfire. destruct Hfire as (fired_rule & Hcfr & Hcan_f & Hok_f).
    assert (Hlift : forall h, knows_datalog_fact s.(known_facts) h ->
                     prog_impl rules_of (knows_datalog_fact inputs) h).
    { intros h Hh. apply Hsound. split;
        [ apply knows_datalog_fact_local_lift_has_derived; exact Hh
        | apply knows_datalog_fact_local_lift_mf_consistent; exact Hh ]. }
    cbn [known_facts sents] in Hf1, Hf2 |- *.
    destruct new_fact as [nf_rel nf_args | new_mfr new_mfa new_source new_mfc].
    { (* F = normal_dfact nf_rel nf_args *)
      cbv [can_deduce_fact] in Hcan_f. destruct Hcan_f as (Hded & Hno_sent). clear Hok_f.
      assert (Hfr_eq : fired_rule = rule_of r).
      { destruct Hcfr as [H' | (mc & mh & _ & H')]; [ exact H' |].
        destruct Hded as (hyps & Hnmri & _). subst fired_rule. invert Hnmri. }
      subst fired_rule.
      destruct f as [R args | R mf_args mf_set].
      - (* f = normal_fact R args *)
        cbv [has_derived_datalog_fact] in Hf1.
        destruct Hf1 as [Heq | Hf1].
        + injection Heq as -> ->.
          destruct Hded as (hyps & Hnmri & Hkdf_hyps).
          eapply prog_impl_step.
          * apply Exists_exists. exists (rule_of r). split.
            -- unfold rules_of. apply in_or_app. right. apply in_map. exact Hin_r.
            -- apply simple_rule_impl. exact Hnmri.
          * rewrite Forall_forall in Hkdf_hyps |- *. intros h Hin_h.
            apply Hlift. exact (Hkdf_hyps _ Hin_h).
        + apply Hsound. split; [ exact Hf1 | exact I ].
      - (* f = meta_fact R mf_args mf_set *)
        assert (HNI_nf : is_input nf_rel = false).
        { rewrite Forall_forall in Hp_input.
          eapply can_deduce_implies_not_input; [ apply Hp_input; exact Hin_r | exact Hded ]. }
        assert (Hf1_s : has_derived_datalog_fact s (meta_fact R mf_args mf_set)).
        { cbv [has_derived_datalog_fact] in Hf1 |- *. destruct (is_input R) eqn:HER.
          - destruct Hf1 as (num & Hin & Hexn). exists num. split.
            + destruct Hin as [Heq | Hin]; [ discriminate | exact Hin ].
            + revert Hexn. apply Existsn_cons_no_iff.
              intros (nfa & Heq & _). injection Heq as HR _. rewrite HR, HER in HNI_nf. discriminate.
          - intros r' Hr'. destruct (Hf1 r' Hr') as (num & Hin).
            destruct Hin as [Heq | Hin]; [ discriminate | exists num; exact Hin ]. }
        destruct (classic (R = nf_rel)) as [-> | HRne].
        + (* R = nf_rel: mf_consistent may need the firing rule *)
          assert (Hf2_s : mf_consistent_state s (meta_fact nf_rel mf_args mf_set)).
          { cbv [mf_consistent_state] in Hf2 |- *. intros nf_args0 Hmatch0.
            specialize (Hf2 _ Hmatch0).
            destruct (classic (nf_args0 = nf_args)) as [-> | HNe].
            - destruct (classic (In (normal_dfact nf_rel nf_args) s.(known_facts))) as [Hk | Hnk].
              + split; intros _; [ exact Hk | apply Hf2; right; exact Hk ].
              + exfalso.
                cbv [has_derived_datalog_fact] in Hf1_s. rewrite HNI_nf in Hf1_s.
                destruct (Hf1_s _ Hin_r) as (num & Hknows).
                pose proof (Hsane.(sane_local_meta) _ _ _ _ Hknows) as (_ & Hin_x).
                eapply Hno_sent; [ exact Hin_x | exact Hmatch0 ].
            - rewrite Hf2. split.
              + intros [Heq | Hk]; [ congruence | exact Hk ].
              + intros Hk. right. exact Hk. }
          apply Hsound. split; [ exact Hf1_s | exact Hf2_s ].
        + (* R <> nf_rel: normal In unchanged *)
          assert (Hf2_s : mf_consistent_state s (meta_fact R mf_args mf_set)).
          { cbv [mf_consistent_state] in Hf2 |- *. intros nf_args0 Hmatch0.
            specialize (Hf2 _ Hmatch0). rewrite Hf2. split.
            - intros [Heq | Hk]; [ congruence | exact Hk ].
            - intros Hk. right. exact Hk. }
          apply Hsound. split; [ exact Hf1_s | exact Hf2_s ]. }
    { (* F = meta_dfact new_mfr new_mfa (from_rule r) new_mfc *)
      cbv [can_deduce_fact] in Hcan_f.
      destruct Hcan_f as (Hsrc & mf_concls & mf_hyps & hyps & Hfr_eq & Hcan & Hknown_h_fire).
      subst new_source. subst fired_rule.
      assert (Hin_mr : In (mf_concls, mf_hyps) p.(meta_rules)).
      { destruct Hcfr as [Hreq | (mc' & mh' & Hin' & Hreq)].
        - destruct r; discriminate.
        - injection Hreq as -> ->. exact Hin'. }
      cbv [can_deduce_meta_fact] in Hcan.
      destruct Hcan as (ctx & Fmfr & Fmfa & Fmfc & HFeq & Hexn_F & Hexists_concl & Hf2_h).
      (* F = meta_dfact Fmfr Fmfa (from_rule r) Fmfc *)
      assert (Hkd_normal : forall R0 args0,
                 In (normal_dfact R0 args0) (meta_dfact new_mfr new_mfa (from_rule r) new_mfc :: s.(known_facts)) <->
                 In (normal_dfact R0 args0) s.(known_facts)).
      { intros. split; [ intros [Heq | Hk]; [ discriminate | exact Hk ] | intros Hk; right; exact Hk ]. }
      destruct f as [R args | R mf_args mf_set].
      - cbv [has_derived_datalog_fact] in Hf1. apply Hkd_normal in Hf1.
        apply Hsound. split; [ exact Hf1 | exact I ].
      - assert (Hf2_s : mf_consistent_state s (meta_fact R mf_args mf_set)).
        { cbv [mf_consistent_state] in Hf2 |- *. intros nf_args0 Hmatch0.
          specialize (Hf2 _ Hmatch0). rewrite Hf2. exact (Hkd_normal R nf_args0). }
        destruct (is_input R) eqn:HER.
        + (* input R: strip F (meta, non-input node) *)
          assert (Hnm : ~ dfact_matches R mf_args
                          (meta_dfact new_mfr new_mfa (from_rule r) new_mfc))
            by (intros (nfa & Heq & _); discriminate).
          assert (Hnd : forall num,
                     meta_dfact new_mfr new_mfa (from_rule r) new_mfc
                     <> meta_dfact R mf_args from_input num)
            by (intros num Heq; injection Heq as _ _ Hn _; discriminate).
          apply Hsound. split; [ | exact Hf2_s ].
          eapply (has_derived_input_meta_cons_bw R mf_args mf_set _ s HER Hnm Hnd).
          cbv [add_known_fact]. exact Hf1.
        + (* non-input R *)
          injection HFeq as HFr HFa HFc. subst Fmfr Fmfa Fmfc.
          destruct (classic (R = new_mfr /\ mf_args = new_mfa)) as [[-> ->] | HNeq].
          * destruct (classic (exists num0,
                        In (meta_dfact new_mfr new_mfa (from_rule r) num0) s.(known_facts)))
              as [HA1 | HA2].
            -- (* A.1 *)
               assert (Hf1_s : has_derived_datalog_fact s (meta_fact new_mfr new_mfa mf_set)).
               { cbv [has_derived_datalog_fact] in Hf1 |- *. rewrite HER in Hf1 |- *.
                 intros r' Hr'. destruct (classic (r' = r)) as [-> | Hrne]; [ exact HA1 |].
                 destruct (Hf1 r' Hr') as (num & Hin). destruct Hin as [Heq | Hk_s];
                   [ congruence | exists num; exact Hk_s ]. }
               apply Hsound. split; [ exact Hf1_s | exact Hf2_s ].
            -- (* A.2: derive via the firing meta-rule *)
               set (s' := {| known_facts :=
                               meta_dfact new_mfr new_mfa (from_rule r) new_mfc
                               :: known_facts s;
                             sents :=
                               mupd_with_default
                                 (cons (meta_dfact new_mfr new_mfa (from_rule r) new_mfc))
                                 (sents s) r |}) in Hstep_save, Hf1, Hf2.
               pose (S_constr := fun args'' => one_step_derives rules_of hyps new_mfr args'').
               assert (Hprog_constr :
                         prog_impl rules_of (knows_datalog_fact inputs)
                           (meta_fact new_mfr new_mfa S_constr)).
               { eapply prog_impl_step.
                 - apply Exists_exists. exists (meta_rule mf_concls mf_hyps). split.
                   + unfold rules_of. apply in_or_app. left. apply in_map_iff.
                     exists (mf_concls, mf_hyps). split; [reflexivity|exact Hin_mr].
                   + apply meta_rule_impl with (ctx := ctx).
                     * eapply Exists_impl; [|exact Hexists_concl].
                       intros c Hclause. cbv [interp_meta_clause] in Hclause |- *.
                       destruct Hclause as (mfa_v & mfs_v & Hf2_v & Heq_v).
                       injection Heq_v as Hcrel Hcargs _.
                       exists mfa_v, S_constr. rewrite Hcargs. split; [exact Hf2_v|].
                       rewrite <- Hcrel. reflexivity.
                     * exact Hf2_h.
                     * intros args'' _. subst S_constr. reflexivity.
                 - rewrite Forall_forall in Hknown_h_fire |- *. intros h Hin_h.
                   apply Hlift. exact (Hknown_h_fire _ Hin_h). }
               eapply prog_impl_mf_ext'; [ exact Hprog_constr | | ].
               ++ intros nf_args1 Hmatch1.
                  pose proof (step_preserves_sane _ _ _ Hinp Hsane Hstep_save) as Hsane_s'.
                  pose proof (step_preserves_mfs_correct _ _ _ Hinp Hsane Hmfc Hstep_save) as Hmfc_s'.
                  pose proof (step_preserves_meta_facts_ok _ _ _ Hinp Hsane Hmfc Hmf_ok Hstep_save)
                    as Hmf_ok_s'.
                  assert (HRs_umfc :
                    forall mf_rel' mf_args' mf_set',
                      (new_mfr, new_mfa) <> (mf_rel', mf_args') ->
                      has_derived_datalog_fact s' (meta_fact mf_rel' mf_args' mf_set') /\
                      mf_consistent_state s' (meta_fact mf_rel' mf_args' mf_set') ->
                      prog_impl rules_of (knows_datalog_fact inputs)
                        (meta_fact mf_rel' mf_args' mf_set')).
                  { intros mfr' mfa' mfs' Hne (Hhd' & Hmc').
                    subst s'. apply Hsound. split.
                    - cbv [has_derived_datalog_fact] in Hhd' |- *.
                      cbn [known_facts sents] in Hhd'. destruct (is_input mfr') eqn:HERmfr'.
                      + destruct Hhd' as (num & Hin & Hexn). exists num. split.
                        * destruct Hin as [Heq | Hin]; [ | exact Hin ].
                          injection Heq as -> -> _ _. exfalso. apply Hne. reflexivity.
                        * revert Hexn. apply Existsn_cons_no_iff.
                          intros (nfa & Heq & _). discriminate.
                      + intros r' Hr'. cbn [known_facts sents] in Hhd'.
                        destruct (Hhd' r' Hr') as (num & Hin).
                        destruct Hin as [Heq | Hin]; [ | exists num; exact Hin ].
                        injection Heq as -> -> _ _. exfalso. apply Hne. reflexivity.
                    - cbv [mf_consistent_state] in Hmc' |- *. intros nf_args2 Hmatch2.
                      specialize (Hmc' _ Hmatch2). cbn [known_facts sents] in Hmc'.
                      rewrite Hmc'. exact (Hkd_normal mfr' nf_args2). }
                  assert (Hf1_True : has_derived_datalog_fact s'
                                       (meta_fact new_mfr new_mfa (fun _ => True))).
                  { cbv [has_derived_datalog_fact] in Hf1 |- *. rewrite HER in Hf1 |- *. exact Hf1. }
                  pose proof (use_meta_facts_correct new_mfr new_mfa inputs s'
                                Hinp Hsane_s' Hmfc_s' Hmf_ok_s' HER HRs_umfc
                                Hf1_True nf_args1 Hmatch1) as Humfc.
                  subst s'.
                  assert (Hgood_inputs_Q : good_inputs rules_of (knows_datalog_fact inputs)).
                  { apply good_inputs_knows_datalog_fact_inputs; [ exact Hinp | ].
                    remember p.(non_meta_rules) as nmrs eqn:Enm.
                    destruct nmrs as [|a l0]; [ destruct Hin_r | cbn [length]; lia ]. }
                  pose proof (valid_impl_honest _ Hmeta_rules _ Hgood_inputs_Q) as Hhonest.
                  cbv [doesnt_lie] in Hhonest.
                  pose proof (Hhonest _ _ _ Hprog_constr) as Hcon_constr.
                  cbv [consistent] in Hcon_constr. specialize (Hcon_constr _ Hmatch1).
                  rewrite Hcon_constr. split.
                  ** intros Hprog. apply Humfc in Hprog.
                     apply (proj2 (Hf2 _ Hmatch1)). exact Hprog.
                  ** intros Hms. apply (proj1 (Hf2 _ Hmatch1)) in Hms.
                     apply Hkd_normal in Hms. apply Hsound. split; [ exact Hms | exact I ].
               ++ intros HQ. simpl in HQ. destruct HQ as (num & Hexp & _ & _).
                  rewrite expect_num_R_facts_eq, HER in Hexp.
                  destruct Hexp as (msgss & Hf2_msgs & _).
                  destruct (Forall2_In_l _ _ _ _ Hf2_msgs
                              (proj1 (dedup_preserves_In p.(non_meta_rules) r) Hin_r))
                    as (m & _ & Hin_m). cbv beta in Hin_m.
                  destruct Hinp as (Hinp_all & _). rewrite Forall_forall in Hinp_all.
                  specialize (Hinp_all _ Hin_m). simpl in Hinp_all. congruence.
          * (* Case B: F doesn't match target; lift Hf1 *)
            assert (Hf1_s : has_derived_datalog_fact s (meta_fact R mf_args mf_set)).
            { cbv [has_derived_datalog_fact] in Hf1 |- *. rewrite HER in Hf1 |- *.
              intros r' Hr'. destruct (Hf1 r' Hr') as (num & Hin).
              destruct Hin as [Heq | Hk_s]; [ | exists num; exact Hk_s ].
              injection Heq as -> -> _ _. exfalso. apply HNeq. split; reflexivity. }
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

  Lemma step_preserves_has_derived inputs s s' f :
    sane_state inputs s ->
    comp_step s s' ->
    has_derived_datalog_fact s f -> has_derived_datalog_fact s' f.
  Proof.
    intros Hsane Hstep Hd.
    pose proof (comp_step_known_incl _ _ Hstep) as Hincl.
    invert Hstep. rename H into Hin_r. rename H0 into Hfire.
    cbn [known_facts sents] in Hincl |- *.
    cbv [fire_at_rule] in Hfire. destruct Hfire as (fired_rule & Hcfr & Hcan_f & _).
    destruct f as [R args | R mf_args mf_set]; cbv [has_derived_datalog_fact] in *.
    - apply in_cons. exact Hd.
    - destruct (is_input R) eqn:HER.
      + destruct Hd as (num & Hin & Hexn). exists num. split; [ apply in_cons; exact Hin |].
        assert (Hnm : ~ dfact_matches R mf_args new_fact).
        { destruct new_fact as [nf_rel nf_args | ? ? ? ?].
          - intros (nfa & Heq & _). injection Heq as HRr _.
            cbv [can_deduce_fact] in Hcan_f. destruct Hcan_f as (Hded & _).
            assert (Hfr : fired_rule = rule_of r).
            { destruct Hcfr as [H'|(mc & mh & _ & H')]; [exact H'|].
              subst fired_rule. destruct Hded as (hyps & Hnmri & _). invert Hnmri. }
            subst fired_rule.
            assert (Hni : is_input nf_rel = false) by
              (eapply can_deduce_implies_not_input;
               [ rewrite Forall_forall in Hp_input; apply Hp_input; exact Hin_r | exact Hded ]).
            rewrite HRr in Hni. congruence.
          - intros (nfa & Heq & _). discriminate. }
        exact (proj2 (Existsn_cons_no_iff _ new_fact num s.(known_facts) Hnm) Hexn).
      + intros r' Hr'. destruct (Hd r' Hr') as (num & Hin). exists num. apply in_cons. exact Hin.
  Qed.

  Lemma steps_preserves_has_derived inputs s s' f :
    good_input_facts inputs ->
    sane_state inputs s ->
    comp_step^* s s' ->
    has_derived_datalog_fact s f -> has_derived_datalog_fact s' f.
  Proof.
    intros Hinp Hsane Hsteps. revert Hsane.
    induction Hsteps; intros Hsane Hd; [exact Hd|].
    apply IHHsteps; [ eapply step_preserves_sane; eassumption |].
    eapply step_preserves_has_derived; eassumption.
  Qed.

  Lemma extract_per_source_meta_dfacts s R mf_args :
    (forall r, In r p.(non_meta_rules) ->
       exists num, In (meta_dfact R mf_args (from_rule r) num) s.(known_facts)) ->
    exists nums,
      Forall2 (fun r num => In (meta_dfact R mf_args (from_rule r) num) s.(known_facts))
              sender_rules nums.
  Proof.
    intros H. apply Forall_exists_r_Forall2. apply Forall_forall. intros r Hr.
    apply H. exact (proj2 (dedup_preserves_In p.(non_meta_rules) r) Hr).
  Qed.

  (* In the single global pool, a fact that is [has_derived] and [mf_consistent]
     is already [knows_datalog_fact] of the pool: the per-node done-messages give
     the expected count, [sane_count] pins the pool's matching count to that sum
     (inputs contribute none for a non-input relation), and consistency is the
     [mf_set] bicondition. *)
  Lemma derived_consistent_impl_knows inputs s h :
    good_input_facts inputs ->
    sane_state inputs s ->
    has_derived_datalog_fact s h ->
    mf_consistent_state s h ->
    knows_datalog_fact s.(known_facts) h.
  Proof.
    intros Hinp Hsane Hd Hc.
    destruct h as [R args | R mf_args mf_set]; [ exact Hd |].
    cbv [has_derived_datalog_fact mf_consistent_state] in Hd, Hc.
    cbn [knows_datalog_fact].
    destruct (is_input R) eqn:HER.
    - destruct Hd as (num & Hin & Hexn). exists num. ssplit.
      + rewrite expect_num_R_facts_eq, HER. exact Hin.
      + exact Hexn.
      + exact Hc.
    - pose proof (extract_per_source_meta_dfacts s R mf_args Hd) as (nums & Hf2).
      exists (list_sum nums). ssplit.
      + rewrite expect_num_R_facts_eq, HER. exists nums. split; [exact Hf2 | reflexivity].
      + (* pool matching count = sum of per-node counts *)
        destruct (Hsane.(sane_count) R mf_args) as (msgs & num_inp & num_kn & Hf2m & Hexn_inp & Hexn_kn & Hsum).
        assert (Hinp0 : num_inp = 0).
        { enough (HE : Existsn (dfact_matches R mf_args) 0 inputs)
            by (exact (Existsn_unique _ _ _ _ Hexn_inp HE)).
          apply Forall_not_Existsn_0. destruct Hinp as (Hinp_all & _).
          rewrite Forall_forall in Hinp_all |- *. intros g Hin_g (nfa & Hg & _).
          specialize (Hinp_all _ Hin_g). subst g. cbn [is_input_fact] in Hinp_all. congruence. }
        assert (Hmsgs_eq : list_sum msgs = list_sum nums).
        { f_equal.
          pose proof (Forall2_length Hf2m) as Hlm. pose proof (Forall2_length Hf2) as Hln.
          apply nth_error_ext. intros i.
          destruct (nth_error msgs i) as [mi|] eqn:Hmi, (nth_error nums i) as [ni|] eqn:Hni.
          - f_equal.
            destruct (nth_error sender_rules i) as [ri|] eqn:Hri;
              [| apply nth_error_None in Hri; apply nth_error_Some_bound_index in Hmi; lia ].
            pose proof (Forall2_nth_error_fwd _ _ _ Hf2m i ri mi Hri Hmi) as Hexn_mi. cbv beta in Hexn_mi.
            pose proof (Forall2_nth_error_fwd _ _ _ Hf2 i ri ni Hri Hni) as Hin_i. cbv beta in Hin_i.
            pose proof (Hsane.(sane_local_meta) _ _ _ _ Hin_i) as (Hexn_ni & _).
            exact (Existsn_unique _ _ _ _ Hexn_mi Hexn_ni).
          - apply nth_error_None in Hni. apply nth_error_Some_bound_index in Hmi. lia.
          - apply nth_error_None in Hmi. apply nth_error_Some_bound_index in Hni. lia.
          - reflexivity. }
        rewrite Hinp0, Nat.add_0_l, Hmsgs_eq in Hsum. subst num_kn. exact Hexn_kn.
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
        eapply Forall_impl; [|exact Hderived_hs].
        cbv beta. intros h0. eapply steps_preserves_has_derived; eauto.
  Qed.

  Lemma knows_datalog_fact_inputs_has_derived inputs s f :
    good_input_facts inputs ->
    sane_state inputs s ->
    knows_datalog_fact inputs f ->
    has_derived_datalog_fact s f.
  Proof.
    intros Hinp Hsane Hkdf.
    pose proof Hsane.(sane_inputs_known) as Hinp_known.
    destruct f as [R args | R mf_args mf_set]; cbv [has_derived_datalog_fact] in *.
    - apply Hinp_known. exact Hkdf.
    - simpl in Hkdf. destruct Hkdf as (num & Hexp & Hexn & _).
      rewrite expect_num_R_facts_eq in Hexp.
      destruct (is_input R) eqn:HER.
      + exists num. split; [ apply Hinp_known; exact Hexp |].
        destruct (Hsane.(sane_count) R mf_args) as (msgs & num_inp & num_kn & Hf2 & Hexn_inp & Hexn_kn & Hsum).
        pose proof (Existsn_unique _ _ _ _ Hexn_inp Hexn) as ->.
        destruct (Hsane.(sane_input_rel) R HER) as (Hsent0 & _). specialize (Hsent0 mf_args).
        assert (Hsum0 : list_sum msgs = 0).
        { apply list_sum_zero.
          clear -Hf2 Hsent0 sent_map_ok nmr_eqb nmr_eqb_ok.
          induction Hf2 as [|r0 m sr ms Hex Hrest IH]; [ constructor | ].
          constructor; [ | exact IH ].
          assert (H0 : Existsn (dfact_matches R mf_args) 0 (get_or_default (sents s) r0)).
          { destruct (map.get (sents s) r0) as [v|] eqn:Eg.
            - rewrite (get_or_default_Some _ _ _ Eg). rewrite Forall_forall in Hsent0.
              apply Hsent0. rewrite In_values. exists r0. exact Eg.
            - rewrite (get_or_default_None _ _ Eg). apply Existsn_nil. }
          eapply Existsn_unique; [ exact H0 | exact Hex ]. }
        rewrite Hsum0, Nat.add_0_r in Hsum. subst num_kn. exact Hexn_kn.
      + intros r' Hr'. destruct Hexp as (msgss & Hf2 & _).
        destruct (Forall2_In_l _ _ _ _ Hf2 (proj1 (dedup_preserves_In p.(non_meta_rules) r') Hr'))
          as (mk & _ & Hin_mk). cbv beta in Hin_mk.
        exists mk. apply Hinp_known. exact Hin_mk.
  Qed.

  (* Lifts soundness in the reverse direction: if a fact is both prog_impl-derivable
     and has_derived in s, then its mf_consistent_state holds in s.
     Analog of SimpleDataflow's correct_impl_consistent.
     Uses meta_facts_consistent (from Datalog.v) as the uniqueness argument.
     The 0 < length non_meta_rules precondition flows from
     good_inputs_knows_datalog_fact_inputs. *)
  Lemma correct_impl_consistent inputs s f :
    good_input_facts inputs ->
    0 < length p.(non_meta_rules) ->
    state_correct inputs s ->
    prog_impl rules_of (knows_datalog_fact inputs) f ->
    has_derived_datalog_fact s f ->
    mf_consistent_state s f.
  Proof.
    intros Hinp Hlen Hsound Himpl Hderived.
    destruct f as [R args | R mf_args mf_set]; [exact I|].
    cbv [mf_consistent_state]. intros nf_args Hmatch.
    (* Build S0 *)
    pose (S0 := fun args' => In (normal_dfact R args') s.(known_facts)).
    (* has_derived s (meta_fact R mf_args S0) holds (depends only on R, mf_args) *)
    assert (Hd0 : has_derived_datalog_fact s (meta_fact R mf_args S0)).
    { cbv [has_derived_datalog_fact] in *. exact Hderived. }
    (* mf_consistent_state s (meta_fact R mf_args S0) holds trivially *)
    assert (Hc0 : mf_consistent_state s (meta_fact R mf_args S0)).
    { cbv [mf_consistent_state]. intros nf_args' Hmatch'.
      unfold S0. reflexivity. }
    (* By state_correct, prog_impl ... (meta_fact R mf_args S0) *)
    pose proof (Hsound (meta_fact R mf_args S0) (conj Hd0 Hc0)) as Himpl0.
    (* Apply meta_facts_consistent to get mf_set <-> S0 *)
    pose proof (good_inputs_knows_datalog_fact_inputs inputs Hinp Hlen) as Hgi.
    destruct Hgi as (Hrel_disj & Hdoesnt_lie).
    assert (Hpair_unique : forall mfr mfa1 mfa2 mfs1 mfs2,
              knows_datalog_fact inputs (meta_fact mfr mfa1 mfs1) ->
              knows_datalog_fact inputs (meta_fact mfr mfa2 mfs2) ->
              forall nfa, Forall2 matches mfa1 nfa -> Forall2 matches mfa2 nfa ->
              mfs1 nfa <-> mfs2 nfa).
    { intros mfr mfa1 mfa2 mfs1 mfs2 HQ1 HQ2 nfa Hm1 Hm2.
      pose proof (Hdoesnt_lie mfr mfa1 mfs1 HQ1 nfa Hm1) as H1.
      pose proof (Hdoesnt_lie mfr mfa2 mfs2 HQ2 nfa Hm2) as H2.
      cbv [rel_of] in H1, H2.
      rewrite H1, H2. reflexivity. }
    pose proof (meta_facts_consistent rules_of (knows_datalog_fact inputs)
                  R mf_args mf_args mf_set S0
                  Hrel_disj Hpair_unique Hmeta_rules
                  Himpl Himpl0 nf_args Hmatch Hmatch) as Hbic.
    rewrite Hbic. unfold S0. reflexivity.
  Qed.

  (* Fire one deducible normal fact into node [k]'s sent list.  The no-conflict
     precondition of the fire step is discharged from [meta_facts_ok]: a matching
     done-message in [k]'s sent list would, by [ok_to_deduce], already have put the
     fact there, contradicting that it is absent. *)
  Lemma comp_step_fire_normal inputs s rn R args :
    sane_state inputs s ->
    meta_facts_ok s ->
    In rn p.(non_meta_rules) ->
    can_deduce_normal_fact (rule_of rn) s.(known_facts) R args ->
    ~ In (normal_dfact R args) (get_or_default s.(sents) rn) ->
    exists s',
      comp_step s s' /\
        s'.(known_facts) = normal_dfact R args :: s.(known_facts) /\
        get_or_default s'.(sents) rn = normal_dfact R args :: get_or_default s.(sents) rn.
  Proof.
    intros Hsane Hmf_ok Hin_rn Hcdn Hnot_in.
    assert (Hno_conflict :
              forall mf_args num,
                In (meta_dfact R mf_args (from_rule rn) num) (get_or_default s.(sents) rn) ->
                Forall2 matches mf_args args -> False).
    { intros mf_args num Hin_meta Hmatch.
      pose proof (Hmf_ok rn Hin_rn) as Hmfor.
      specialize (Hmfor R mf_args num Hin_meta). cbv [ok_to_deduce_fact] in Hmfor.
      exact (Hnot_in (Hmfor args Hcdn Hmatch)). }
    exists {| known_facts := normal_dfact R args :: s.(known_facts);
              sents := mupd_with_default (cons (normal_dfact R args)) s.(sents) rn |}.
    ssplit.
    - apply (fire_rule (normal_dfact R args) s rn); [ exact Hin_rn |].
      cbv [fire_at_rule]. exists (rule_of rn). ssplit.
      + left. reflexivity.
      + cbn [can_deduce_fact]. split; [ exact Hcdn | exact Hno_conflict ].
      + exact I.
    - cbn [known_facts]. reflexivity.
    - cbn [sents]. rewrite get_or_default_mupd. destr (eqb rn rn); [ reflexivity | congruence ].
  Qed.

  (* Drive node [rn] to sent-broadcast every [R_concl]-fact matching [args_concl]
     that its rule can deduce, so that firing the [(from_rule rn)] done-message
     is [ok_to_deduce].  Termination: the set of such facts is bounded by the
     finite list [l] from [meta_facts_finite] applied to the (real) meta-fact. *)
  Lemma rule_can_force_normal_dfacts inputs s rn R_concl args_concl S_set :
    good_input_facts inputs ->
    0 < length p.(non_meta_rules) ->
    sane_state inputs s ->
    meta_facts_correct s ->
    meta_facts_ok s ->
    state_correct inputs s ->
    In rn p.(non_meta_rules) ->
    prog_impl rules_of (knows_datalog_fact inputs) (meta_fact R_concl args_concl S_set) ->
    exists s',
      comp_step^* s s' /\
        ok_to_deduce_fact (rule_of rn) s'.(known_facts) (get_or_default s'.(sents) rn)
          (meta_dfact R_concl args_concl (from_rule rn) 0).
  Proof.
    intros Hinp Hlen_pos Hsane Hmfc Hmf_ok Hsound Hin_rn Hpi_meta.
    assert (Hpremise : forall R mf_args S,
               knows_datalog_fact inputs (meta_fact R mf_args S) ->
               exists l, forall args, Forall2 matches mf_args args -> S args -> In args l).
    { intros R0 mf0 S0 Hk. cbv [knows_datalog_fact] in Hk. destruct Hk as (num & _ & _ & Hbi).
      exists (map (fun df => match df with normal_dfact _ a => a | _ => nil end) inputs).
      intros args Hmatch HS. apply Hbi in HS; [| exact Hmatch].
      apply in_map_iff. exists (normal_dfact R0 args). split; [reflexivity | exact HS]. }
    pose proof (Hmeta_finite (knows_datalog_fact inputs) Hpremise R_concl args_concl S_set Hpi_meta)
      as (l & Hl_bound).
    pose proof (good_inputs_knows_datalog_fact_inputs inputs Hinp Hlen_pos) as Hgi.
    pose proof (valid_impl_honest _ Hmeta_rules _ Hgi) as Hhonest.
    cbv [doesnt_lie] in Hhonest.
    pose proof (Hhonest R_concl args_concl S_set Hpi_meta) as Hcons_meta.
    cbv [consistent] in Hcons_meta.
    assert (Hl_reachable : forall nf_args s',
              comp_step^* s s' ->
              In (normal_dfact R_concl nf_args) s'.(known_facts) ->
              Forall2 matches args_concl nf_args -> In nf_args l).
    { intros nf_args s' Hsteps' Hknows Hmatch.
      apply Hl_bound; [exact Hmatch|]. apply (Hcons_meta nf_args Hmatch).
      assert (Hsane' : sane_state inputs s') by eauto using steps_preserves_sane.
      assert (Hsound' : state_correct inputs s') by eauto using comp_steps_sound.
      apply Hsound'. split; [ cbv [has_derived_datalog_fact]; exact Hknows | exact I ]. }
    assert (Hcand0 : forall nf_args s',
              comp_step^* s s' ->
              In (normal_dfact R_concl nf_args) s'.(known_facts) ->
              Forall2 matches args_concl nf_args ->
              In (normal_dfact R_concl nf_args) (get_or_default s.(sents) rn) \/ In nf_args l).
    { intros nf_args s' Hsteps' Hknows Hmatch. right. eapply Hl_reachable; eassumption. }
    clear Hl_reachable Hpi_meta Hl_bound Hhonest Hcons_meta Hgi Hpremise.
    remember (length l) as len eqn:Elen.
    assert (Hlen : length l < S len) by lia. clear Elen.
    revert l s Hlen Hsane Hmfc Hmf_ok Hsound Hcand0. generalize (S len). clear len.
    intros len. induction len as [|len IH]; intros l s Hlen Hsane Hmfc Hmf_ok Hsound Hcand; [lia|].
    destruct (classic (Exists (fun nf : list T =>
                          can_deduce_normal_fact (rule_of rn) s.(known_facts) R_concl nf /\
                          Forall2 matches args_concl nf /\
                          ~ In (normal_dfact R_concl nf) (get_or_default s.(sents) rn)) l)) as [Hex | Hno].
    - rewrite Exists_exists in Hex.
      destruct Hex as (nf & Hin_l & Hcdn_nf & Hmatch & Hnot_in_sent).
      apply in_split in Hin_l. destruct Hin_l as (l1 & l2 & Hl_split).
      pose proof (comp_step_fire_normal inputs s rn R_concl nf
                    Hsane Hmf_ok Hin_rn Hcdn_nf Hnot_in_sent)
        as (s_fire & Hstep_fire & Hkn_fire & Hgd_fire).
      assert (Hsteps_fire : comp_step^* s s_fire)
        by (eapply Relation_Operators.rt1n_trans; [exact Hstep_fire | apply rt1n_refl]).
      assert (Hsane_fire : sane_state inputs s_fire) by eauto using step_preserves_sane.
      assert (Hmfc_fire : meta_facts_correct s_fire) by eauto using step_preserves_mfs_correct.
      assert (Hmf_ok_fire : meta_facts_ok s_fire) by eauto using step_preserves_meta_facts_ok.
      assert (Hsound_fire : state_correct inputs s_fire) by eauto using comp_step_sound.
      assert (Hcand_fire : forall nf_args s'',
                comp_step^* s_fire s'' ->
                In (normal_dfact R_concl nf_args) s''.(known_facts) ->
                Forall2 matches args_concl nf_args ->
                In (normal_dfact R_concl nf_args) (get_or_default s_fire.(sents) rn) \/ In nf_args (l1 ++ l2)).
      { intros nf_args s'' Hsteps'' Hkn'' Hmatch''.
        assert (Hsteps_tot : comp_step^* s s'')
          by (eapply crt1n_trans_compose; [exact Hsteps_fire | exact Hsteps'']).
        specialize (Hcand nf_args s'' Hsteps_tot Hkn'' Hmatch'').
        destruct Hcand as [Hc | Hc].
        - left. rewrite Hgd_fire. right. exact Hc.
        - rewrite Hl_split in Hc. apply in_app_iff in Hc. destruct Hc as [Hc | [Hc | Hc]].
          + right. apply in_app_iff. left. exact Hc.
          + subst nf_args. left. rewrite Hgd_fire. left. reflexivity.
          + right. apply in_app_iff. right. exact Hc. }
      assert (Hlen' : length (l1 ++ l2) < len).
      { rewrite Hl_split, length_app in Hlen. rewrite length_app. simpl in Hlen. lia. }
      destruct (IH (l1 ++ l2) s_fire Hlen' Hsane_fire Hmfc_fire Hmf_ok_fire Hsound_fire Hcand_fire)
        as (s' & Hsteps' & Hforcing').
      exists s'. ssplit;
        [ eapply crt1n_trans_compose; [exact Hsteps_fire | exact Hsteps'] | exact Hforcing' ].
    - exists s. ssplit; [ apply rt1n_refl |].
      cbv [ok_to_deduce_fact]. intros nf_args Hcdn_nf Hmatch.
      destruct (classic (In (normal_dfact R_concl nf_args) (get_or_default s.(sents) rn)))
        as [Hin | Hnin]; [exact Hin|].
      exfalso.
      pose proof (comp_step_fire_normal inputs s rn R_concl nf_args
                    Hsane Hmf_ok Hin_rn Hcdn_nf Hnin)
        as (s_fire & Hstep_fire & Hkn_fire & _).
      assert (Hin_kn_fire : In (normal_dfact R_concl nf_args) s_fire.(known_facts))
        by (rewrite Hkn_fire; left; reflexivity).
      assert (Hsteps1 : comp_step^* s s_fire)
        by (eapply Relation_Operators.rt1n_trans; [exact Hstep_fire | apply rt1n_refl]).
      specialize (Hcand nf_args s_fire Hsteps1 Hin_kn_fire Hmatch).
      destruct Hcand as [Hc | Hc].
      + apply Hnin. exact Hc.
      + apply Hno. apply Exists_exists. exists nf_args.
        split; [exact Hc | split; [exact Hcdn_nf | split; [exact Hmatch | exact Hnin]]].
  Qed.

  (* Fire the [(from_rule rn)] done-message for [(R, args)] at node [rn], given the
     rule's concl/hyp interpretation, that its hyps are known, and [ok_to_deduce]. *)
  Lemma comp_step_fire_meta inputs s rn rule_concls rule_hyps ctx R args S hyps ms :
    sane_state inputs s ->
    In rn p.(non_meta_rules) ->
    In (rule_concls, rule_hyps) p.(meta_rules) ->
    Existsn (dfact_matches R args) ms (get_or_default s.(sents) rn) ->
    Exists (fun c => interp_meta_clause ctx c (meta_fact R args S)) rule_concls ->
    Forall2 (interp_meta_clause ctx) rule_hyps hyps ->
    Forall (knows_datalog_fact s.(known_facts)) hyps ->
    ok_to_deduce_fact (rule_of rn) s.(known_facts) (get_or_default s.(sents) rn)
      (meta_dfact R args (from_rule rn) ms) ->
    exists s',
      comp_step s s' /\
        s'.(known_facts) = meta_dfact R args (from_rule rn) ms :: s.(known_facts).
  Proof.
    intros Hsane Hin_rn Hin_mr Hexn Hconcl Hhyps Hknow Hok.
    exists {| known_facts := meta_dfact R args (from_rule rn) ms :: s.(known_facts);
              sents := mupd_with_default (cons (meta_dfact R args (from_rule rn) ms)) s.(sents) rn |}.
    split; [| cbn [known_facts]; reflexivity ].
    apply (fire_rule (meta_dfact R args (from_rule rn) ms) s rn); [ exact Hin_rn |].
    cbv [fire_at_rule]. exists (meta_rule rule_concls rule_hyps). ssplit.
    - right. exists rule_concls, rule_hyps. split; [exact Hin_mr | reflexivity].
    - cbn [can_deduce_fact]. split; [reflexivity|].
      exists rule_concls, rule_hyps, hyps. split; [reflexivity|]. split.
      + cbv [can_deduce_meta_fact]. exists ctx, R, args, ms. ssplit.
        * reflexivity.
        * exact Hexn.
        * eapply Exists_impl; [| exact Hconcl ]. intros c Hc.
          cbv [interp_meta_clause] in Hc |- *. destruct Hc as (mfa & mfs & Hf2 & Heq).
          injection Heq as Hrel Hmfa _. exists args, (fun _ => False). split.
          -- rewrite Hmfa. exact Hf2.
          -- rewrite <- Hrel. reflexivity.
        * exact Hhyps.
      + exact Hknow.
    - cbn [ok_to_deduce_fact] in Hok |- *. exact Hok.
  Qed.

  Lemma good_layout_complete_rule inputs s (ru : rule) f hyps :
    good_input_facts inputs ->
    sane_state inputs s ->
    meta_facts_correct s ->
    meta_facts_ok s ->
    state_correct inputs s ->
    In ru rules_of ->
    rule_impl (one_step_derives rules_of) ru f hyps ->
    Forall (has_derived_datalog_fact s) hyps ->
    Forall (mf_consistent_state s) hyps ->
    exists s',
      comp_step^* s s' /\
        has_derived_datalog_fact s' f.
  Proof.
    intros Hinp Hsane Hmfc Hmf_ok Hsound Hin_r Himpl Hderived Hcons.
    pose proof Himpl as Himpl_save.
    invert Himpl.
    - (* simple_rule_impl: f = normal_fact R args *)
      rename H into Hnmri.
      assert (Hin_nmr : exists nmr, In nmr p.(non_meta_rules) /\ rule_of nmr = ru).
      { cbv [rules_of] in Hin_r. apply in_app_or in Hin_r. destruct Hin_r as [Hm | Hnm].
        - exfalso. apply in_map_iff in Hm. destruct Hm as ((c, h) & Heq & _).
          rewrite <- Heq in Hnmri. invert Hnmri.
        - apply in_map_iff in Hnm. destruct Hnm as (nmr & Heq & Hin). exists nmr. auto. }
      destruct Hin_nmr as (nmr & Hin_nmr & Hnmr_eq).
      destruct (classic (In (normal_dfact R args) s.(known_facts))) as [Hin | Hnin].
      + exists s. split; [apply rt1n_refl | exact Hin].
      + assert (Hcdn : can_deduce_normal_fact (rule_of nmr) s.(known_facts) R args).
        { exists hyps. split; [ rewrite Hnmr_eq; exact Hnmri |].
          rewrite Forall_forall. intros h Hh. eapply derived_consistent_impl_knows;
            [ exact Hinp | exact Hsane
            | rewrite Forall_forall in Hderived; apply Hderived; exact Hh
            | rewrite Forall_forall in Hcons; apply Hcons; exact Hh ]. }
        assert (Hnin_sent : ~ In (normal_dfact R args) (get_or_default s.(sents) nmr)).
        { intros Hs. apply Hnin.
          eapply sent_implies_knows; [ exact Hsane | exact Hin_nmr | exact Hs ]. }
        pose proof (comp_step_fire_normal inputs s nmr R args Hsane Hmf_ok Hin_nmr Hcdn Hnin_sent)
          as (s' & Hstep & Hkn & _).
        exists s'. split.
        * eapply Relation_Operators.rt1n_trans; [exact Hstep | apply rt1n_refl].
        * cbv [has_derived_datalog_fact]. rewrite Hkn. left. reflexivity.
    - (* meta_rule_impl: f = meta_fact R args S *)
      rename H into Hconcl, H0 into Hforall2_hyps, H1 into HS_def.
      assert (Hin_mr : In (rule_concls, rule_hyps) p.(meta_rules)).
      { cbv [rules_of] in Hin_r. apply in_app_or in Hin_r. destruct Hin_r as [Hm | Hnm].
        - apply in_map_iff in Hm. destruct Hm as ((c, h) & Heq & Hin). injection Heq as -> ->. exact Hin.
        - exfalso. apply in_map_iff in Hnm. destruct Hnm as (nmr & Heq & _). destruct nmr; discriminate. }
      assert (HR_noninput : is_input R = false).
      { rewrite Forall_forall in Hp_meta_input. specialize (Hp_meta_input _ Hin_mr).
        cbn [good_meta_rule_inputs] in Hp_meta_input. rewrite Forall_forall in Hp_meta_input.
        apply Exists_exists in Hconcl. destruct Hconcl as (c & Hin_c & Hint).
        cbv [interp_meta_clause] in Hint. destruct Hint as (mfa & mfs & _ & Heq).
        injection Heq as -> _ _. apply (Hp_meta_input _ Hin_c). }
      assert (Hpi_hyps : Forall (prog_impl rules_of (knows_datalog_fact inputs)) hyps).
      { rewrite Forall_forall. intros h Hh. apply Hsound. split;
          [ rewrite Forall_forall in Hderived; apply Hderived; exact Hh
          | rewrite Forall_forall in Hcons; apply Hcons; exact Hh ]. }
      assert (Hpi_meta : prog_impl rules_of (knows_datalog_fact inputs) (meta_fact R args S)).
      { eapply prog_impl_step.
        - apply Exists_exists. exists (meta_rule rule_concls rule_hyps). split.
          + cbv [rules_of]. apply in_or_app. left. apply in_map_iff.
            exists (rule_concls, rule_hyps). split; [reflexivity | exact Hin_mr].
          + exact Himpl_save.
        - exact Hpi_hyps. }
      assert (Hgoal_n : forall rs, incl rs p.(non_meta_rules) ->
                exists s', comp_step^* s s' /\
                  (forall r, In r rs -> exists num,
                     In (meta_dfact R args (from_rule r) num) s'.(known_facts))).
      { induction rs as [|r0 rs IH]; intros Hincl.
        - exists s. split; [apply rt1n_refl|]. intros r [].
        - destruct (IH ltac:(intros x Hx; apply Hincl; right; exact Hx))
            as (s' & Hsteps' & Hrs_forced).
          assert (Hin_r0 : In r0 p.(non_meta_rules)) by (apply Hincl; left; reflexivity).
          assert (Hlen_pos : 0 < length p.(non_meta_rules)).
          { remember p.(non_meta_rules) as nmrs eqn:Enm.
            destruct nmrs as [|a l0]; [ destruct Hin_r0 | cbn [length]; lia ]. }
          assert (Hsane' : sane_state inputs s') by eauto using steps_preserves_sane.
          assert (Hmfc' : meta_facts_correct s') by eauto using steps_preserves_mfs_correct.
          assert (Hmf_ok' : meta_facts_ok s') by eauto using steps_preserves_meta_facts_ok.
          assert (Hsound' : state_correct inputs s') by eauto using comp_steps_sound.
          pose proof (rule_can_force_normal_dfacts inputs s' r0 R args S
                        Hinp Hlen_pos Hsane' Hmfc' Hmf_ok' Hsound' Hin_r0 Hpi_meta)
            as (s'' & Hsteps_force & Hforcing).
          assert (Hsteps'' : comp_step^* s s'')
            by (eapply crt1n_trans_compose; [exact Hsteps' | exact Hsteps_force]).
          assert (Hsane'' : sane_state inputs s'') by eauto using steps_preserves_sane.
          assert (Hsound'' : state_correct inputs s'') by eauto using comp_steps_sound.
          assert (Hknow_hyps'' : Forall (knows_datalog_fact s''.(known_facts)) hyps).
          { rewrite Forall_forall. intros h Hh.
            assert (Hd'' : has_derived_datalog_fact s'' h).
            { eapply steps_preserves_has_derived; [ exact Hinp | exact Hsane | exact Hsteps'' |].
              rewrite Forall_forall in Hderived; apply Hderived; exact Hh. }
            eapply derived_consistent_impl_knows; [ exact Hinp | exact Hsane'' | exact Hd'' |].
            eapply correct_impl_consistent;
              [ exact Hinp | lia | exact Hsound''
              | rewrite Forall_forall in Hpi_hyps; apply Hpi_hyps; exact Hh | exact Hd'' ]. }
          destruct (Existsn_total (dfact_matches R args) (get_or_default s''.(sents) r0)) as (ms & Hexn_ms).
          pose proof (comp_step_fire_meta inputs s'' r0 rule_concls rule_hyps ctx R args S hyps ms
                        Hsane'' Hin_r0 Hin_mr Hexn_ms Hconcl Hforall2_hyps Hknow_hyps'' Hforcing)
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
      specialize (Hgoal_n p.(non_meta_rules) (incl_refl _)).
      destruct Hgoal_n as (s' & Hsteps & Hall).
      exists s'. split; [exact Hsteps|].
      cbv [has_derived_datalog_fact]. rewrite HR_noninput. intros r Hr. apply Hall. exact Hr.
  Qed.

  Definition state_complete (inputs : list dfact) (s : state) :=
    forall f,
      prog_impl rules_of (knows_datalog_fact inputs) f ->
      exists s',
        comp_step^* s s' /\
          has_derived_datalog_fact s' f.

  Lemma comp_step_complete inputs s :
    good_input_facts inputs ->
    0 < length p.(non_meta_rules) ->
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
    apply prog_impl_ind.
    - (* base case: knows_datalog_fact inputs f *)
      intros f0 Hkdf s0 Hsane0 Hmfc0 Hmf_ok0 Hsound0.
      exists s0. split; [apply rt1n_refl|].
      eapply knows_datalog_fact_inputs_has_derived; eassumption.
    - (* step case *)
      intros f0 hyps Hexists Hforall_pi Hforall_R s0 Hsane0 Hmfc0 Hmf_ok0 Hsound0.
      apply Exists_exists in Hexists.
      destruct Hexists as (ru & Hin_r & Hrule_impl).
      (* Apply compose_completion to get s1 reachable with Forall has_derived s1 hyps *)
      pose proof (compose_completion inputs s0 hyps Hinp Hsane0 Hmfc0 Hmf_ok0 Hsound0 Hforall_R)
        as (s1 & Hsteps1 & Hderived1).
      assert (Hsane1 : sane_state inputs s1) by eauto using steps_preserves_sane.
      assert (Hmfc1 : meta_facts_correct s1) by eauto using steps_preserves_mfs_correct.
      assert (Hmf_ok1 : meta_facts_ok s1) by eauto using steps_preserves_meta_facts_ok.
      assert (Hsound1 : state_correct inputs s1) by eauto using comp_steps_sound.
      (* Build mf_consistent_state for hyps at s1 via correct_impl_consistent *)
      assert (Hcons1 : Forall (mf_consistent_state s1) hyps).
      { apply Forall_forall.
        intros h Hin_h.
        eapply correct_impl_consistent.
        - exact Hinp.
        - exact Hlen.
        - exact Hsound1.
        - rewrite Forall_forall in Hforall_pi. apply Hforall_pi. assumption.
        - rewrite Forall_forall in Hderived1. apply Hderived1. assumption. }
      (* Apply good_layout_complete_rule *)
      pose proof (good_layout_complete_rule inputs s1 ru f0 hyps
                    Hinp Hsane1 Hmfc1 Hmf_ok1 Hsound1 Hin_r Hrule_impl Hderived1 Hcons1)
        as (s2 & Hsteps2 & Hderived2).
      exists s2. split; [|exact Hderived2].
      eapply crt1n_trans_compose; eassumption.
  Qed.

  Definition start (inputs : list dfact) : state :=
    {| known_facts := inputs; sents := map.empty |}.

  Lemma good_input_no_node_meta (inputs : list dfact) R a r num :
    good_input_facts inputs -> ~ In (meta_dfact R a (from_rule r) num) inputs.
  Proof.
    intros [Hall _] Hin. rewrite Forall_forall in Hall.
    specialize (Hall _ Hin). cbn in Hall. discriminate.
  Qed.

  Lemma get_or_default_empty r : get_or_default (map.empty : sent_map) r = [].
  Proof. rewrite (get_or_default_None (map.empty : sent_map) r) by apply map.get_empty. reflexivity. Qed.

  Lemma mfc_start (inputs : list dfact) : meta_facts_correct (start inputs).
  Proof.
    unfold meta_facts_correct, start. cbn [known_facts sents].
    intros r Hr R mf_args num Hin. rewrite get_or_default_empty in Hin. destruct Hin.
  Qed.

  Lemma mfok_start (inputs : list dfact) : meta_facts_ok (start inputs).
  Proof.
    unfold meta_facts_ok, start. cbn [known_facts sents].
    intros r Hr mf_rel mf_args num Hin. rewrite get_or_default_empty in Hin. destruct Hin.
  Qed.

  Lemma sane_start (inputs : list dfact) :
    good_input_facts inputs -> sane_state inputs (start inputs).
  Proof.
    intros Hg. unfold start. constructor; cbn [known_facts sents].
    - intros R a num H. exact H.
    - intros R a r num H. exfalso. exact (good_input_no_node_meta inputs R a r num Hg H).
    - intros R a. destruct (Existsn_total (dfact_matches R a) inputs) as (nk & Hnk).
      exists (repeat 0 (length sender_rules)), nk, nk. split; [| split; [| split]].
      + apply Forall2_repeat_r. apply Forall_forall. intros r _.
        rewrite get_or_default_empty. apply Existsn_nil.
      + exact Hnk.
      + exact Hnk.
      + rewrite list_sum_repeat. lia.
    - intros R HER. split.
      + intros a. rewrite values_empty. constructor.
      + intros a r num. exact (good_input_no_node_meta inputs R a r num Hg).
    - intros g H. exact H.
  Qed.

  Lemma sc_start (inputs : list dfact) :
    0 < length p.(non_meta_rules) ->
    good_input_facts inputs -> state_correct inputs (start inputs).
  Proof.
    intros Hlen Hg f (Hd & Hmc). destruct f as [R args | R mf_args mf_set].
    - cbv [has_derived_datalog_fact] in Hd. unfold start in Hd. cbn [known_facts] in Hd.
      apply prog_impl_leaf. cbn [Node.knows_datalog_fact]. exact Hd.
    - cbv [has_derived_datalog_fact] in Hd. cbv [mf_consistent_state] in Hmc.
      unfold start in Hd, Hmc. cbn [known_facts] in Hd, Hmc.
      destruct (is_input R) eqn:HER.
      + apply prog_impl_leaf. cbn [Node.knows_datalog_fact].
        destruct Hd as (num & Hin & Hexn). exists num. split; [| split].
        * rewrite expect_num_R_facts_eq, HER. exact Hin.
        * exact Hexn.
        * intros nfa Hm. exact (Hmc nfa Hm).
      + exfalso. remember p.(non_meta_rules) as nmrs eqn:E.
        destruct nmrs as [|r0 l0]; [ cbn [length] in Hlen; lia | ].
        destruct (Hd r0 (or_introl eq_refl)) as (num & Hin).
        exact (good_input_no_node_meta inputs R mf_args r0 num Hg Hin).
  Qed.

  Theorem prog_impl_iff_comp_step (inputs : list dfact) (f : fact) :
    0 < length p.(non_meta_rules) ->
    good_input_facts inputs ->
    (prog_impl rules_of (knows_datalog_fact inputs) f <->
     exists s', comp_step^* (start inputs) s' /\
                has_derived_datalog_fact s' f /\ mf_consistent_state s' f).
  Proof.
    intros Hlen Hg.
    pose proof (sane_start inputs Hg) as Hsane.
    pose proof (mfc_start inputs) as Hmfc.
    pose proof (mfok_start inputs) as Hmfok.
    pose proof (sc_start inputs Hlen Hg) as Hsc.
    split.
    - intros Hprog.
      assert (Hcompl : state_complete inputs (start inputs))
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

Arguments sane_state {rel exprvar fn aggregator T nmr_eqb sent_map} is_input p input_facts s.
