From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Classical_Prop.
From Stdlib Require Import Relations.Relation_Operators Relations.Operators_Properties.

From Datalog Require Import Map Tactics Fp List Dag Datalog.

From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List Datatypes.Option.

Import ListNotations.

Notation "R ^*" := (clos_refl_trans_1n _ R) (format "R ^*").
#[global] Hint Constructors clos_refl_trans_1n : core.

Section __.
  Context {rel var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T} `{query_sig : query_signature rel}.
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context {var_eqb : var -> var -> bool} {var_eqb_spec :  forall x0 y0 : var, BoolSpec (x0 = y0) (x0 <> y0) (var_eqb x0 y0)}.

  Local Notation clause := (clause rel var fn).
  Local Notation meta_clause := (meta_clause rel var fn).
  Local Notation fact := (fact rel T).
  Local Notation expr := (expr var fn).
  Local Notation rule := (rule rel var fn aggregator).
  Local Notation non_meta_rule := (non_meta_rule rel var fn aggregator).
  Local Notation dfact := (dfact rel T).
  Local Notation prog := (prog rel var fn aggregator).

  Implicit Types known_facts sent_facts waiting_facts input_facts inputs : list dfact.
  Implicit Types nf result : dfact.
  Implicit Types p : prog.
  Implicit Types r : non_meta_rule.
  Implicit Types mf_rel : rel.
  Implicit Types mf_args : list (option T).
  Implicit Types nf_args : list T.

  Record rule_state :=
    { known_facts : list dfact;
      waiting_facts : list dfact;
      sent_facts : list dfact }.

  Definition state :=
    list rule_state.

  Context (is_input : rel -> bool).
  Context (p : prog).

  Definition rules_of : list rule :=
    map (fun '(c, h) => meta_rule c h) p.(meta_rules) ++ map rule_of p.(non_meta_rules).

  Definition stepOne {T} (do_step : T -> T -> Prop) : list T -> list T -> Prop :=
    fun start finish =>
      exists l1 x y l2,
        start = l1 ++ x :: l2 /\
          finish = l1 ++ y :: l2 /\
          do_step x y.

  Definition stepWithLabel {T U} (do_step : U -> T -> T -> Prop) (labels : list U) : list T -> list T -> Prop :=
    fun start finish =>
      exists l1 n x y l2,
        combine labels start = l1 ++ (n, x) :: l2 /\
          finish = map snd l1 ++ y :: map snd l2 /\
          do_step n x y.

  Definition learn_fact_at_rule (s1 s2 : rule_state) : Prop :=
    exists l1 x l2,
      s2.(known_facts) = x :: s1.(known_facts) /\
        s1.(waiting_facts) = l1 ++ x :: l2 /\
        s2.(waiting_facts) = l1 ++ l2 /\
        s2.(sent_facts) = s1.(sent_facts).

  Definition expect_num_R_facts R mf_args known_facts num :=
    if is_input R then
      In (meta_dfact R mf_args None num) known_facts
    else
      exists expected_msgss,
        Forall2 (fun n expected_msgs => In (meta_dfact R mf_args (Some n) expected_msgs) known_facts) (seq O (length p.(non_meta_rules))) expected_msgss /\
          num = fold_left Nat.add expected_msgss O.

  Definition dfact_matches mf_rel mf_args nf :=
    exists nf_args,
      nf = normal_dfact mf_rel nf_args /\
        Forall2 matches mf_args nf_args.

  Definition knows_datalog_fact (dfacts : list dfact) (f : fact) :=
    match f with
    | normal_fact nf_rel nf_args =>
        In (normal_dfact nf_rel nf_args) dfacts
    | meta_fact mf_rel mf_args mf_set =>
        exists num,
        expect_num_R_facts mf_rel mf_args dfacts num /\
          Existsn (dfact_matches mf_rel mf_args) num dfacts /\
          (forall nf_args,
              Forall2 matches mf_args nf_args ->
              mf_set nf_args <-> In (normal_dfact mf_rel nf_args) dfacts)
    end.

  Definition can_deduce_normal_fact (r : non_meta_rule) (known_facts : list dfact) nf_rel nf_args :=
    exists hyps,
      non_meta_rule_impl (rule_of r) nf_rel nf_args hyps /\
        Forall (knows_datalog_fact known_facts) hyps.

  Definition can_deduce_meta_fact (mf_concls mf_hyps : list meta_clause) (r : non_meta_rule) (source : nat) (sent_facts : list dfact) (known_facts : list dfact) (result : dfact) (hyps : list fact) :=
    exists ctx mf_rel mf_args mf_cnt,
      result = meta_dfact mf_rel mf_args (Some source) mf_cnt /\
        Existsn (dfact_matches mf_rel mf_args) mf_cnt sent_facts /\
        Exists (fun c => interp_meta_clause ctx c (meta_fact mf_rel mf_args (fun _ => False))) mf_concls /\
        Forall2 (interp_meta_clause ctx) mf_hyps hyps /\
        (forall nf_args,
            can_deduce_normal_fact r known_facts mf_rel nf_args ->
            Forall2 matches mf_args nf_args ->
            In (normal_dfact mf_rel nf_args) known_facts).

  Definition meta_facts_correct_at_rule mrs n rs r :=
    forall R mf_args num,
      In (meta_dfact R mf_args (Some n) num) rs.(sent_facts) ->
      exists mf_concls mf_hyps hyps,
        In (mf_concls, mf_hyps) mrs /\
          can_deduce_meta_fact mf_concls mf_hyps r n rs.(sent_facts) rs.(known_facts) (meta_dfact R mf_args (Some n) num) hyps /\
          Forall (knows_datalog_fact rs.(known_facts)) hyps /\
          (forall mf_set, ~In (meta_fact R mf_args mf_set) hyps).

  Definition meta_facts_correct (s : state) :=
    Forall3 (fun r rs n =>
               meta_facts_correct_at_rule p.(meta_rules) n rs r)
            p.(non_meta_rules) s (seq 0 (length s)).

  Definition add_waiting_fact f (rs : rule_state) :=
    {| known_facts := rs.(known_facts);
      waiting_facts := f :: rs.(waiting_facts);
      sent_facts := rs.(sent_facts); |}.

  Definition send_fact f rs :=
    {| known_facts := rs.(known_facts);
      waiting_facts := rs.(waiting_facts);
      sent_facts := f :: rs.(sent_facts) |}.

  Inductive comp_step : state -> state -> Prop :=
  | learn_fact s1 s2 :
    stepOne learn_fact_at_rule s1 s2 ->
    comp_step s1 s2
  | fire_normal_rule nf_rel nf_args s1 s2 :
    stepWithLabel (fun '(r, n) rs rs' =>
                     can_deduce_normal_fact r rs.(known_facts) nf_rel nf_args /\
                       (forall mf_args num,
                           In (meta_dfact nf_rel mf_args (Some n) num) rs.(sent_facts) ->
                           Forall2 matches mf_args nf_args ->
                           False) /\
                       rs' = send_fact (normal_dfact nf_rel nf_args) rs)
      (combine p.(non_meta_rules) (seq O (length s1))) s1 s2 ->
    comp_step s1 (map (add_waiting_fact (normal_dfact nf_rel nf_args)) s2)
  | fire_meta_rule mf_concls mf_hyps hyps new_fact s1 s2 :
    In (mf_concls, mf_hyps) p.(meta_rules) ->
    stepWithLabel (fun '(r, n) rs rs' =>
                     can_deduce_meta_fact mf_concls mf_hyps r n rs.(sent_facts) rs.(known_facts) new_fact hyps /\
                       Forall (knows_datalog_fact rs.(known_facts)) hyps /\
                       rs' = send_fact new_fact rs)
      (combine p.(non_meta_rules) (seq O (length s1))) s1 s2 ->
    comp_step s1 (map (add_waiting_fact new_fact) s2).

  Definition is_input_fact (f : dfact) :=
    match f with
    | normal_dfact R _ => is_input R
    | meta_dfact R _ None _ => is_input R
    | meta_dfact _ _ (Some _) _ => false
    end.

  Definition inputs := list dfact.

  Inductive inp_step : state -> inputs -> state -> inputs -> Prop :=
  | Receive s1 inps1 new_fact :
    is_input_fact new_fact = true ->
    inp_step s1 inps1 (map (add_waiting_fact new_fact) s1) (new_fact :: inps1).

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

  Definition rule_has_dfact rs f :=
    In f rs.(known_facts) \/ In f rs.(waiting_facts).

  Definition knows_dfact (s : state) f :=
    Exists (fun rs => rule_has_dfact rs f) s.

  Definition nth_sat {T} (l : list T) n (P : T -> Prop) :=
    match nth_error l n with
    | Some x => P x
    | None => False
    end.

  Definition good_input_facts input_facts :=
    Forall (fun f => is_input_fact f = true) input_facts /\
      (forall R mf_args num,
          In (meta_dfact R mf_args None num) input_facts ->
          (forall num0, In (meta_dfact R mf_args None num0) input_facts -> num0 = num) /\
            exists num',
              num' <= num /\
                Existsn (dfact_matches R mf_args) num' input_facts).

  Definition sane_state (input_facts : list dfact) (s : state) :=
    length s = length p.(non_meta_rules) /\
    (forall R mf_args num,
        knows_dfact s (meta_dfact R mf_args None num) ->
        In (meta_dfact R mf_args None num) input_facts) /\
      (forall R mf_args n num,
          knows_dfact s (meta_dfact R mf_args (Some n) num) ->
          nth_sat s n (fun rs =>
                         Existsn (dfact_matches R mf_args) num rs.(sent_facts) /\
                         In (meta_dfact R mf_args (Some n) num) rs.(sent_facts))) /\
      (forall f,
          knows_dfact s f ->
          Forall (fun rs => rule_has_dfact rs f) s) /\
      (forall R mf_args,
        exists msgs_sents num_inp,
          Forall2 (fun rs msgs_sent =>
                     Existsn (dfact_matches R mf_args) msgs_sent rs.(sent_facts))
            s msgs_sents /\
            Existsn (dfact_matches R mf_args) num_inp input_facts /\
            Forall (fun rs_n =>
                      exists num_known num_wait,
                        Existsn (dfact_matches R mf_args) num_known rs_n.(known_facts) /\
                          Existsn (dfact_matches R mf_args) num_wait rs_n.(waiting_facts) /\
                          num_known + num_wait = num_inp + fold_left Nat.add msgs_sents O) s) /\
      (forall R,
          is_input R = true ->
          (forall mf_args, Forall (fun rs => Existsn (dfact_matches R mf_args) O rs.(sent_facts)) s) /\
            (forall mf_args n num, ~knows_dfact s (meta_dfact R mf_args (Some n) num))) /\
      (forall f, In f input_facts -> knows_dfact s f).

  Lemma learn_fact_at_rule_rule_has_dfact rs1 rs2 :
    learn_fact_at_rule rs1 rs2 ->
    forall f, rule_has_dfact rs1 f <-> rule_has_dfact rs2 f.
  Proof.
    cbv [learn_fact_at_rule rule_has_dfact]. intros H f. fwd.
    rewrite Hp0, Hp1, Hp2. simpl. repeat rewrite in_app_iff. simpl.
    intuition congruence.
  Qed.

  Lemma learn_fact_at_rule_sent rs1 rs2 :
    learn_fact_at_rule rs1 rs2 ->
    rs2.(sent_facts) = rs1.(sent_facts).
  Proof. cbv [learn_fact_at_rule]. intros H. fwd. assumption. Qed.

  Lemma exists_swap A (P : A -> Prop) l1 x y l2 :
    (P x -> P y) ->
    Exists P (l1 ++ x :: l2) -> Exists P (l1 ++ y :: l2).
  Proof.
    intros H Hex.
    apply Exists_app in Hex. apply Exists_app. destruct Hex as [Hex|Hex]; auto.
    right. apply Exists_cons in Hex. apply Exists_cons.
    destruct Hex as [Hx|Hl2]; auto.
  Qed.

  Lemma forall_swap A (P : A -> Prop) l1 x y l2 :
    (P x -> P y) ->
    Forall P (l1 ++ x :: l2) -> Forall P (l1 ++ y :: l2).
  Proof.
    intros H Hf.
    apply Forall_app in Hf. apply Forall_app. destruct Hf as [Hf1 Hf2]. split; auto.
    apply Forall_cons_iff in Hf2. apply Forall_cons_iff.
    destruct Hf2 as [Hx Hl2]. auto.
  Qed.

  Lemma nth_sat_swap A l1 (x y : A) l2 (P : A -> Prop) k :
    (P x -> P y) ->
    nth_sat (l1 ++ x :: l2) k P -> nth_sat (l1 ++ y :: l2) k P.
  Proof.
    intros H. cbv [nth_sat].
    destruct (Nat.lt_ge_cases k (length l1)) as [Hk|Hk].
    - rewrite ! nth_error_app1 by assumption. auto.
    - rewrite ! nth_error_app2 by assumption.
      destruct (k - length l1) eqn:E; simpl; auto.
  Qed.

  Lemma forall2_swap_l A B l1 (x y : A) l2 (ms : list B) (P : A -> B -> Prop) :
    (forall m, P x m -> P y m) ->
    Forall2 P (l1 ++ x :: l2) ms ->
    Forall2 P (l1 ++ y :: l2) ms.
  Proof.
    intros H Hf.
    apply Forall2_app_inv_l in Hf. fwd. invert_list_stuff.
    apply Forall2_app; [assumption|]. constructor; auto.
  Qed.

  Lemma learn_fact_at_rule_perm rs1 rs2 :
    learn_fact_at_rule rs1 rs2 ->
    Permutation (rs1.(known_facts) ++ rs1.(waiting_facts))
                (rs2.(known_facts) ++ rs2.(waiting_facts)).
  Proof.
    cbv [learn_fact_at_rule]. intros H. fwd.
    rewrite Hp0, Hp1, Hp2. simpl.
    eapply perm_trans.
    - apply Permutation_app_head. apply Permutation_sym. apply Permutation_middle.
    - apply Permutation_sym. apply Permutation_middle.
  Qed.

  Lemma learn_fact_at_rule_existsn_split (P : dfact -> Prop) rs1 rs2 :
    learn_fact_at_rule rs1 rs2 ->
    forall num_k num_w,
      Existsn P num_k rs1.(known_facts) ->
      Existsn P num_w rs1.(waiting_facts) ->
      exists num_k' num_w',
        Existsn P num_k' rs2.(known_facts) /\
        Existsn P num_w' rs2.(waiting_facts) /\
        num_k' + num_w' = num_k + num_w.
  Proof.
    intros H num_k num_w Hk Hw.
    pose proof (learn_fact_at_rule_perm _ _ H) as Hperm.
    pose proof (Existsn_app _ _ _ _ _ Hk Hw) as Hcat.
    eapply Existsn_perm in Hcat. 2: exact Hperm.
    apply Existsn_split in Hcat. fwd. eauto.
  Qed.

  Lemma nth_error_app_middle A (l1 : list A) x l2 n :
    nth_error (l1 ++ x :: l2) n =
    match Nat.compare n (length l1) with
    | Lt => nth_error l1 n
    | Eq => Some x
    | Gt => nth_error l2 (n - length l1 - 1)
    end.
  Proof.
    destruct (Nat.compare_spec n (length l1)) as [-> | Hlt | Hgt].
    - rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
    - rewrite nth_error_app1 by assumption. reflexivity.
    - rewrite nth_error_app2 by lia.
      destruct (n - length l1) eqn:E; [exfalso; lia|].
      simpl. f_equal. lia.
  Qed.

  Lemma nth_sat_app_middle A (l1 : list A) x l2 n P :
    nth_sat (l1 ++ x :: l2) n P =
    match Nat.compare n (length l1) with
    | Lt => nth_sat l1 n P
    | Eq => P x
    | Gt => nth_sat l2 (n - length l1 - 1) P
    end.
  Proof.
    cbv [nth_sat]. rewrite nth_error_app_middle.
    destruct (Nat.compare_spec n (length l1)) as [-> | Hlt | Hgt]; reflexivity.
  Qed.

  Lemma nth_sat_map A B (f : A -> B) l n (P : B -> Prop) :
    nth_sat (map f l) n P <-> nth_sat l n (fun x => P (f x)).
  Proof.
    cbv [nth_sat]. rewrite nth_error_map.
    destruct (nth_error l n); reflexivity.
  Qed.

  Lemma knows_dfact_add_waiting F s f :
    knows_dfact (map (add_waiting_fact F) s) f -> f = F \/ knows_dfact s f.
  Proof.
    cbv [knows_dfact rule_has_dfact]. intros HE. apply Exists_exists in HE.
    destruct HE as (rs' & Hin' & [Hk | Hw]).
    - apply in_map_iff in Hin'. destruct Hin' as (rs & Heq & Hin); subst rs'.
      cbv [add_waiting_fact] in Hk; simpl in Hk.
      right. apply Exists_exists. exists rs. auto.
    - apply in_map_iff in Hin'. destruct Hin' as (rs & Heq & Hin); subst rs'.
      cbv [add_waiting_fact] in Hw; simpl in Hw.
      destruct Hw as [<-|Hw]; auto.
      right. apply Exists_exists. exists rs. auto.
  Qed.

  Lemma knows_dfact_after_step F l1 x l2 f :
    knows_dfact (map (add_waiting_fact F) (l1 ++ send_fact F x :: l2)) f ->
    f = F \/ knows_dfact (l1 ++ x :: l2) f.
  Proof.
    intros HE. apply knows_dfact_add_waiting in HE.
    destruct HE as [|HE]; [auto|]. right.
    cbv [knows_dfact rule_has_dfact send_fact] in *.
    rewrite Exists_app in HE |- *. simpl in HE |- *.
    rewrite Exists_cons in HE |- *. intuition.
  Qed.

  Lemma rule_has_dfact_afw F rs f :
    rule_has_dfact rs f -> rule_has_dfact (add_waiting_fact F rs) f.
  Proof. cbv [rule_has_dfact add_waiting_fact]; simpl; intuition. Qed.

  Lemma rule_has_dfact_afw_F F rs :
    rule_has_dfact (add_waiting_fact F rs) F.
  Proof. cbv [rule_has_dfact add_waiting_fact]; simpl; auto. Qed.

  Lemma fold_left_add_from_0 (l : list nat) (n : nat) :
    fold_left Nat.add l n = fold_left Nat.add l 0 + n.
  Proof.
    revert n. induction l as [|a l IH]; intros n; simpl; [reflexivity|].
    rewrite IH, (IH a). lia.
  Qed.

  Lemma can_deduce_implies_not_input r kf nf_rel nf_args :
    good_non_meta_rule r ->
    can_deduce_normal_fact r kf nf_rel nf_args ->
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

  Lemma send_fact_rule_has_dfact F rs f :
    rule_has_dfact (send_fact F rs) f <-> rule_has_dfact rs f.
  Proof. cbv [send_fact rule_has_dfact]. simpl. reflexivity. Qed.

  Lemma knows_dfact_send_fact_in_middle F l1 x l2 f :
    knows_dfact (l1 ++ send_fact F x :: l2) f <-> knows_dfact (l1 ++ x :: l2) f.
  Proof.
    cbv [knows_dfact]. split; apply exists_swap; cbv [send_fact rule_has_dfact]; simpl; auto.
  Qed.

  Lemma knows_dfact_add_waiting_mono F s g :
    knows_dfact s g -> knows_dfact (map (add_waiting_fact F) s) g.
  Proof.
    cbv [knows_dfact]. intros HE. apply Exists_exists in HE. apply Exists_exists.
    destruct HE as (rs & Hin & Hd). exists (add_waiting_fact F rs).
    split; [apply in_map; exact Hin|].
    cbv [add_waiting_fact rule_has_dfact] in *. simpl. intuition.
  Qed.

  Lemma knows_dfact_after_step_bw F l1 x l2 f :
    f = F \/ knows_dfact (l1 ++ x :: l2) f ->
    knows_dfact (map (add_waiting_fact F) (l1 ++ send_fact F x :: l2)) f.
  Proof.
    intros [Heq|Hkd].
    - subst f. cbv [knows_dfact rule_has_dfact add_waiting_fact send_fact].
      rewrite map_app. simpl. apply Exists_app. right.
      apply Exists_cons_hd. simpl. right. left. reflexivity.
    - rewrite <- knows_dfact_send_fact_in_middle in Hkd.
      cbv [knows_dfact] in *.
      apply Exists_exists in Hkd. apply Exists_exists.
      destruct Hkd as (rs & Hin & Hd). exists (add_waiting_fact F rs).
      split.
      + apply in_map_iff. exists rs. split; [reflexivity|exact Hin].
      + cbv [add_waiting_fact rule_has_dfact] in *. simpl. intuition.
  Qed.

  Lemma step_preserves_sane inputs s1 s2 :
    good_input_facts inputs ->
    sane_state inputs s1 ->
    comp_step s1 s2 ->
    sane_state inputs s2.
  Proof.
    intros Hinp Hsane Hstep.
    destruct Hsane as (Hlen & Hmf_inp & Hmf_sent & Heverywhere & Hcount & Hinp_sane & Hinp_propagated).
    invert Hstep.
    - cbv [stepOne] in H. fwd.
      pose proof (learn_fact_at_rule_rule_has_dfact _ _ Hp2) as Hpres_rhd.
      pose proof (learn_fact_at_rule_sent _ _ Hp2) as Hpres_sent.
      assert (Hkd_bw : forall f, knows_dfact (l1 ++ y :: l2) f -> knows_dfact (l1 ++ x :: l2) f).
      { intros f. cbv [knows_dfact]. apply exists_swap. apply Hpres_rhd. }
      cbv [sane_state]. ssplit.
      + rewrite ! length_app in *. simpl in *. lia.
      + intros R mf_args num Hk. apply Hkd_bw in Hk. eapply Hmf_inp. eassumption.
      + intros R mf_args n num Hk. apply Hkd_bw in Hk.
        specialize (Hmf_sent _ _ _ _ Hk).
        eapply nth_sat_swap; [|exact Hmf_sent].
        intros. fwd. rewrite Hpres_sent. split; assumption.
      + intros f Hk. pose proof Hk as Hk0. apply Hkd_bw in Hk0.
        specialize (Heverywhere _ Hk0).
        eapply forall_swap; [|exact Heverywhere].
        cbv beta. apply Hpres_rhd.
      + intros R mf_args.
        specialize (Hcount R mf_args). fwd.
        exists msgs_sents, num_inp. ssplit.
        * eapply forall2_swap_l; [|exact Hcountp0].
          intros msg He. rewrite Hpres_sent. assumption.
        * assumption.
        * eapply forall_swap; [|exact Hcountp2].
          cbv beta. intros (num_k & num_w & Hk_x & Hw_x & Hsum_x).
          pose proof (learn_fact_at_rule_existsn_split _ _ _ Hp2 _ _ Hk_x Hw_x)
            as (num_k' & num_w' & Hk_y & Hw_y & Hsum_y).
          do 2 eexists. ssplit; eauto. lia.
      + intros R HR. specialize (Hinp_sane R HR). fwd.
        split.
        * intros mf_args. specialize (Hinp_sanep0 mf_args).
          eapply forall_swap; [|exact Hinp_sanep0].
          cbv beta. intros He. rewrite Hpres_sent. assumption.
        * intros mf_args n num Hk. apply Hkd_bw in Hk.
          exact (Hinp_sanep1 _ _ _ Hk).
      + intros f HIn. specialize (Hinp_propagated f HIn).
        cbv [knows_dfact] in *.
        eapply exists_swap; [|exact Hinp_propagated]. apply Hpres_rhd.
    - cbv [stepWithLabel] in H. fwd. destruct n as [r k].
      destruct Hp2 as (Hcan & Hnometa & Hyq). subst y.
      assert (Hlc : length (combine (non_meta_rules p) (seq 0 (length s1))) = length s1).
      { rewrite length_combine, length_seq. lia. }
      assert (Hs1_eq : s1 = map snd l1 ++ x :: map snd l2).
      { apply (f_equal (map snd)) in Hp0.
        rewrite map_combine_snd in Hp0 by assumption.
        rewrite map_app in Hp0. simpl in Hp0. exact Hp0. }
      assert (Hlen_lt : length l1 < length s1).
      { rewrite Hs1_eq, length_app, ! length_map. simpl. lia. }
      assert (Hk_eq : k = length l1).
      { assert (Hlen_seq : length (non_meta_rules p) = length (seq 0 (length s1))).
        { rewrite length_seq. lia. }
        pose proof Hp0 as Hp0a.
        apply (f_equal (map fst)) in Hp0a.
        rewrite map_app in Hp0a. simpl in Hp0a.
        rewrite map_combine_fst in Hp0a by assumption.
        apply (f_equal (map snd)) in Hp0a.
        rewrite map_app in Hp0a. simpl in Hp0a.
        rewrite map_combine_snd in Hp0a by assumption.
        pose proof (f_equal (fun ll => nth_error ll (length l1)) Hp0a) as HnE.
        cbv beta in HnE.
        rewrite nth_error_app_middle in HnE.
        rewrite ! length_map in HnE.
        rewrite Nat.compare_refl in HnE.
        rewrite nth_error_seq in HnE.
        assert (E : length l1 <? length s1 = true) by (apply Nat.ltb_lt; lia).
        rewrite E in HnE.
        injection HnE as ->. lia. }
      assert (Hin_r : In r p.(non_meta_rules)).
      { assert (Hin_outer : In (r, k, x) (combine (combine (non_meta_rules p) (seq 0 (length s1))) s1)).
        { rewrite Hp0. apply in_or_app. right. simpl. auto. }
        apply in_combine_l in Hin_outer.
        apply in_combine_l in Hin_outer. exact Hin_outer. }
      assert (Hnf_noninput : is_input nf_rel = false).
      { rewrite Forall_forall in Hp_input. apply Hp_input in Hin_r.
        eapply can_deduce_implies_not_input; eassumption. }
      rewrite Hs1_eq in Hmf_inp, Hmf_sent, Heverywhere, Hcount, Hinp_sane, Hlen, Hinp_propagated.
      cbv [sane_state]. ssplit.
      + rewrite length_map, length_app in *. cbn [length] in *.
        rewrite ! length_map in *. lia.
      + intros R mf_args num Hk.
        apply knows_dfact_after_step in Hk.
        destruct Hk as [Hk | Hk]; [discriminate|].
        eapply Hmf_inp; eassumption.
      + intros R mf_args n' num Hk.
        apply knows_dfact_after_step in Hk.
        destruct Hk as [Hk | Hk]; [discriminate|].
        specialize (Hmf_sent _ _ _ _ Hk).
        rewrite nth_sat_map. cbv beta.
        rewrite nth_sat_app_middle. rewrite length_map.
        rewrite nth_sat_app_middle in Hmf_sent. rewrite length_map in Hmf_sent.
        destruct (Nat.compare_spec n' (length l1)) as [Hl' | Hl' | Hl'].
        * subst n'.
          destruct Hmf_sent as (HE & HI).
          cbv [add_waiting_fact send_fact]; simpl.
          assert (Hnmatch : ~ dfact_matches R mf_args (normal_dfact nf_rel nf_args)).
          { intros (nf_args0 & Heqf & Hmatch).
            injection Heqf as H_rel H_args. subst R nf_args0.
            eapply Hnometa with (mf_args := mf_args) (num := num).
            - rewrite Hk_eq. exact HI.
            - exact Hmatch. }
          split.
          -- apply Existsn_no; assumption.
          -- right. exact HI.
        * cbv [add_waiting_fact]; simpl. exact Hmf_sent.
        * cbv [add_waiting_fact]; simpl. exact Hmf_sent.
      + intros f Hk.
        apply Forall_map.
        pose proof Hk as Hk0.
        apply knows_dfact_after_step in Hk0.
        destruct Hk0 as [Hk0 | Hk0].
        * subst f.
          apply Forall_forall. intros y _. apply rule_has_dfact_afw_F.
        * specialize (Heverywhere _ Hk0).
          apply Forall_app in Heverywhere. destruct Heverywhere as (HF1 & HF2).
          apply Forall_cons_iff in HF2. destruct HF2 as (Hxf & HF2).
          apply Forall_app. split.
          -- eapply Forall_impl; [|exact HF1]. intros. apply rule_has_dfact_afw; assumption.
          -- constructor.
             ++ apply rule_has_dfact_afw.
                cbv [rule_has_dfact send_fact]; simpl. exact Hxf.
             ++ eapply Forall_impl; [|exact HF2]. intros. apply rule_has_dfact_afw; assumption.
      + intros R mf_args.
        specialize (Hcount R mf_args). fwd.
        apply Forall2_app_inv_l in Hcountp0.
        destruct Hcountp0 as (ms_pre & ms_rest & Hms_pre & Hms_rest & ?). subst.
        inversion Hms_rest; subst.
        rename y into ms_x. rename l' into ms_post.
        rename H1 into Hms_x. rename H3 into Hms_post.
        apply Forall_app in Hcountp2. destruct Hcountp2 as (Hcountp2_pre & Hcountp2_rest).
        apply Forall_cons_iff in Hcountp2_rest.
        destruct Hcountp2_rest as (Hcountp2_x & Hcountp2_post).
        destruct (classic (dfact_matches R mf_args (normal_dfact nf_rel nf_args))) as [Hdf | Hdf].
        * exists (ms_pre ++ S ms_x :: ms_post), num_inp. ssplit.
          -- rewrite <- Forall2_map_l.
             apply Forall2_app; [|constructor].
             ++ eapply Forall2_impl; [|exact Hms_pre]. intros y m Hy.
                cbv [add_waiting_fact]; simpl. exact Hy.
             ++ cbv [add_waiting_fact send_fact]; simpl.
                apply Existsn_yes; assumption.
             ++ eapply Forall2_impl; [|exact Hms_post]. intros y m Hy.
                cbv [add_waiting_fact]; simpl. exact Hy.
          -- assumption.
          -- apply Forall_map.
             apply Forall_app; split.
             ++ eapply Forall_impl; [|exact Hcountp2_pre].
                intros y (num_k & num_w & Hk_y & Hw_y & Hsum).
                exists num_k, (S num_w). cbv [add_waiting_fact]; simpl. ssplit.
                ** exact Hk_y.
                ** apply Existsn_yes; assumption.
                ** rewrite ! fold_left_app in *. simpl in *.
                   rewrite (fold_left_add_from_0 ms_post _) in Hsum.
                   rewrite (fold_left_add_from_0 ms_post _).
                   lia.
             ++ constructor.
                ** destruct Hcountp2_x as (num_k & num_w & Hk_x & Hw_x & Hsum).
                   exists num_k, (S num_w). cbv [add_waiting_fact send_fact]; simpl. ssplit.
                   --- exact Hk_x.
                   --- apply Existsn_yes; assumption.
                   --- rewrite ! fold_left_app in *. simpl in *.
                       rewrite (fold_left_add_from_0 ms_post _) in Hsum.
                       rewrite (fold_left_add_from_0 ms_post _).
                       lia.
                ** eapply Forall_impl; [|exact Hcountp2_post].
                   intros y (num_k & num_w & Hk_y & Hw_y & Hsum).
                   exists num_k, (S num_w). cbv [add_waiting_fact]; simpl. ssplit.
                   --- exact Hk_y.
                   --- apply Existsn_yes; assumption.
                   --- rewrite ! fold_left_app in *. simpl in *.
                       rewrite (fold_left_add_from_0 ms_post _) in Hsum.
                       rewrite (fold_left_add_from_0 ms_post _).
                       lia.
        * exists (ms_pre ++ ms_x :: ms_post), num_inp. ssplit.
          -- rewrite <- Forall2_map_l.
             apply Forall2_app; [|constructor].
             ++ eapply Forall2_impl; [|exact Hms_pre]. intros y m Hy.
                cbv [add_waiting_fact]; simpl. exact Hy.
             ++ cbv [add_waiting_fact send_fact]; simpl. apply Existsn_no; assumption.
             ++ eapply Forall2_impl; [|exact Hms_post]. intros y m Hy.
                cbv [add_waiting_fact]; simpl. exact Hy.
          -- assumption.
          -- apply Forall_map.
             apply Forall_app; split.
             ++ eapply Forall_impl; [|exact Hcountp2_pre].
                intros y (num_k & num_w & Hk_y & Hw_y & Hsum).
                exists num_k, num_w. cbv [add_waiting_fact]; simpl. ssplit.
                ** exact Hk_y.
                ** apply Existsn_no; assumption.
                ** assumption.
             ++ constructor.
                ** destruct Hcountp2_x as (num_k & num_w & Hk_x & Hw_x & Hsum).
                   exists num_k, num_w. cbv [add_waiting_fact send_fact]; simpl. ssplit.
                   --- exact Hk_x.
                   --- apply Existsn_no; assumption.
                   --- assumption.
                ** eapply Forall_impl; [|exact Hcountp2_post].
                   intros y (num_k & num_w & Hk_y & Hw_y & Hsum).
                   exists num_k, num_w. cbv [add_waiting_fact]; simpl. ssplit.
                   --- exact Hk_y.
                   --- apply Existsn_no; assumption.
                   --- assumption.
      + intros R HR.
        specialize (Hinp_sane R HR). fwd.
        split.
        * intros mf_args. specialize (Hinp_sanep0 mf_args).
          apply Forall_map.
          eapply forall_swap with (x := x); cycle 1.
          -- eapply Forall_impl; [|exact Hinp_sanep0]. intros y Hy.
             cbv [add_waiting_fact]; simpl. exact Hy.
          -- cbv [add_waiting_fact send_fact]; simpl. intros Hx_zero.
             apply Existsn_no; [|exact Hx_zero].
             intros (nf_args0 & Heqf & Hmatch).
             inversion Heqf as [[H_rel H_args]]. subst.
             congruence.
        * intros mf_args n num Hk.
          apply knows_dfact_after_step in Hk.
          destruct Hk as [Hk | Hk]; [discriminate|].
          apply (Hinp_sanep1 _ _ _ Hk).
      + intros f HIn. specialize (Hinp_propagated f HIn).
        apply knows_dfact_after_step_bw. right. exact Hinp_propagated.
    - cbv [stepWithLabel] in H0. fwd. destruct n as [r k].
      destruct H0p2 as (Hcdmf & Hknow_hyps & Hyq). subst y.
      cbv [can_deduce_meta_fact] in Hcdmf.
      destruct Hcdmf as (ctx & mf_rel & mf_args_new & mf_cnt & Hnf_eq
                          & HsentExistsn & Hmc_concl & Hmc_hyps & Hclosure).
      assert (Hlc : length (combine (non_meta_rules p) (seq 0 (length s1))) = length s1).
      { rewrite length_combine, length_seq. lia. }
      assert (Hs1_eq : s1 = map snd l1 ++ x :: map snd l2).
      { apply (f_equal (map snd)) in H0p0.
        rewrite map_combine_snd in H0p0 by assumption.
        rewrite map_app in H0p0. simpl in H0p0. exact H0p0. }
      assert (Hlen_lt : length l1 < length s1).
      { rewrite Hs1_eq, length_app, ! length_map. simpl. lia. }
      assert (Hk_eq : k = length l1).
      { assert (Hlen_seq : length (non_meta_rules p) = length (seq 0 (length s1))).
        { rewrite length_seq. lia. }
        pose proof H0p0 as Hp0a.
        apply (f_equal (map fst)) in Hp0a.
        rewrite map_app in Hp0a. simpl in Hp0a.
        rewrite map_combine_fst in Hp0a by assumption.
        apply (f_equal (map snd)) in Hp0a.
        rewrite map_app in Hp0a. simpl in Hp0a.
        rewrite map_combine_snd in Hp0a by assumption.
        pose proof (f_equal (fun ll => nth_error ll (length l1)) Hp0a) as HnE.
        cbv beta in HnE.
        rewrite nth_error_app_middle in HnE.
        rewrite ! length_map in HnE.
        rewrite Nat.compare_refl in HnE.
        rewrite nth_error_seq in HnE.
        assert (E : length l1 <? length s1 = true) by (apply Nat.ltb_lt; lia).
        rewrite E in HnE.
        injection HnE as ->. lia. }
      assert (Hmf_rel_noninput : is_input mf_rel = false).
      { rewrite Forall_forall in Hp_meta_input.
        specialize (Hp_meta_input _ H). simpl in Hp_meta_input.
        rewrite Forall_forall in Hp_meta_input.
        apply Exists_exists in Hmc_concl.
        destruct Hmc_concl as (c & Hin_c & Hint).
        cbv [interp_meta_clause] in Hint.
        destruct Hint as (mfa & mfs & _ & Heq).
        injection Heq as -> _ _.
        apply (Hp_meta_input _ Hin_c). }
      subst new_fact.
      rewrite Hs1_eq in Hmf_inp, Hmf_sent, Heverywhere, Hcount, Hinp_sane, Hlen, Hinp_propagated.
      cbv [sane_state]. ssplit.
      + rewrite length_map, length_app in *. cbn [length] in *.
        rewrite ! length_map in *. lia.
      + intros R mf_args num Hk.
        apply knows_dfact_after_step in Hk.
        destruct Hk as [Hk | Hk]; [discriminate|].
        eapply Hmf_inp; eassumption.
      + intros R mf_args n' num Hk.
        apply knows_dfact_after_step in Hk.
        rewrite nth_sat_map. cbv beta.
        rewrite nth_sat_app_middle. rewrite length_map.
        destruct Hk as [Hk | Hk].
        * injection Hk as -> -> -> ->.
          rewrite <- Hk_eq. rewrite Nat.compare_refl.
          cbv [add_waiting_fact send_fact]; simpl. split.
          -- apply Existsn_no; [|exact HsentExistsn].
             intros (? & Heq & _). discriminate.
          -- left. reflexivity.
        * specialize (Hmf_sent _ _ _ _ Hk).
          rewrite nth_sat_app_middle in Hmf_sent. rewrite length_map in Hmf_sent.
          destruct (Nat.compare_spec n' (length l1)) as [Hl' | Hl' | Hl'].
          -- subst n'.
             destruct Hmf_sent as (HE & HI).
             cbv [add_waiting_fact send_fact]; simpl. split.
             ++ apply Existsn_no; [|exact HE].
                intros (? & Heq & _). discriminate.
             ++ right. exact HI.
          -- cbv [add_waiting_fact]; simpl. exact Hmf_sent.
          -- cbv [add_waiting_fact]; simpl. exact Hmf_sent.
      + intros f Hk.
        apply Forall_map.
        pose proof Hk as Hk0.
        apply knows_dfact_after_step in Hk0.
        destruct Hk0 as [Hk0 | Hk0].
        * subst f.
          apply Forall_forall. intros y _. apply rule_has_dfact_afw_F.
        * specialize (Heverywhere _ Hk0).
          apply Forall_app in Heverywhere. destruct Heverywhere as (HF1 & HF2).
          apply Forall_cons_iff in HF2. destruct HF2 as (Hxf & HF2).
          apply Forall_app. split.
          -- eapply Forall_impl; [|exact HF1]. intros. apply rule_has_dfact_afw; assumption.
          -- constructor.
             ++ apply rule_has_dfact_afw.
                cbv [rule_has_dfact send_fact]; simpl. exact Hxf.
             ++ eapply Forall_impl; [|exact HF2]. intros. apply rule_has_dfact_afw; assumption.
      + intros R mf_args.
        specialize (Hcount R mf_args). fwd.
        apply Forall2_app_inv_l in Hcountp0.
        destruct Hcountp0 as (ms_pre & ms_rest & Hms_pre & Hms_rest & ?). subst.
        inversion Hms_rest; subst.
        rename y into ms_x. rename l' into ms_post.
        rename H2 into Hms_x. rename H4 into Hms_post.
        apply Forall_app in Hcountp2. destruct Hcountp2 as (Hcountp2_pre & Hcountp2_rest).
        apply Forall_cons_iff in Hcountp2_rest.
        destruct Hcountp2_rest as (Hcountp2_x & Hcountp2_post).
        exists (ms_pre ++ ms_x :: ms_post), num_inp. ssplit.
        * rewrite <- Forall2_map_l.
          apply Forall2_app; [|constructor].
          -- eapply Forall2_impl; [|exact Hms_pre]. intros y m Hy.
             cbv [add_waiting_fact]; simpl. exact Hy.
          -- cbv [add_waiting_fact send_fact]; simpl.
             apply Existsn_no; [|exact Hms_x].
             intros (? & Heq & _). discriminate.
          -- eapply Forall2_impl; [|exact Hms_post]. intros y m Hy.
             cbv [add_waiting_fact]; simpl. exact Hy.
        * assumption.
        * apply Forall_map.
          apply Forall_app; split.
          -- eapply Forall_impl; [|eassumption].
             intros y (num_k & num_w & Hk_y & Hw_y & Hsum).
             exists num_k, num_w. cbv [add_waiting_fact]; simpl. ssplit.
             ++ exact Hk_y.
             ++ apply Existsn_no; [|exact Hw_y].
                intros (? & Heq & _). discriminate.
             ++ assumption.
          -- constructor.
             ++ destruct Hcountp2_x as (num_k & num_w & Hk_x & Hw_x & Hsum).
                exists num_k, num_w. cbv [add_waiting_fact send_fact]; simpl. ssplit.
                ** exact Hk_x.
                ** apply Existsn_no; [|exact Hw_x].
                   intros (? & Heq & _). discriminate.
                ** assumption.
             ++ eapply Forall_impl; [|exact Hcountp2_post].
                intros y (num_k & num_w & Hk_y & Hw_y & Hsum).
                exists num_k, num_w. cbv [add_waiting_fact]; simpl. ssplit.
                ** exact Hk_y.
                ** apply Existsn_no; [|exact Hw_y].
                   intros (? & Heq & _). discriminate.
                ** assumption.
      + intros R HR.
        specialize (Hinp_sane R HR). fwd.
        split.
        * intros mf_args. specialize (Hinp_sanep0 mf_args).
          apply Forall_map.
          eapply forall_swap with (x := x); cycle 1.
          -- eapply Forall_impl; [|exact Hinp_sanep0]. intros y Hy.
             cbv [add_waiting_fact]; simpl. exact Hy.
          -- cbv [add_waiting_fact send_fact]; simpl. intros Hx_zero.
             apply Existsn_no; [|exact Hx_zero].
             intros (? & Heq & _). discriminate.
        * intros mf_args n num Hk.
          apply knows_dfact_after_step in Hk.
          destruct Hk as [Hk | Hk].
          -- injection Hk as -> _ _ _. congruence.
          -- apply (Hinp_sanep1 _ _ _ Hk).
      + intros f HIn. specialize (Hinp_propagated f HIn).
        apply knows_dfact_after_step_bw. right. exact Hinp_propagated.
  Qed.

  Lemma fold_left_add_zero (l : list nat) :
    Forall (eq 0) l ->
    fold_left Nat.add l 0 = 0.
  Proof.
    induction 1; simpl; auto. subst. simpl. assumption.
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

  Lemma Forall2_nth_error_bwd {A B} (R : A -> B -> Prop) xs ys :
    length xs = length ys ->
    (forall n x y,
      nth_error xs n = Some x ->
      nth_error ys n = Some y ->
      R x y) ->
    Forall2 R xs ys.
  Proof.
    revert ys. induction xs as [|x xs IH]; intros [|y ys] Hlen H; simpl in *;
      try discriminate.
    - constructor.
    - constructor.
      + apply (H 0); reflexivity.
      + apply IH; [lia|]. intros n x' y' Hx Hy.
        apply (H (S n)); assumption.
  Qed.

  (* For the count argument to close (analog of SimpleDataflow's
     expect_num_R_facts_no_travellers using msgs_received = num), we need
     the local count of matching normal facts in known.  SimpleDataflow gets
     this for free because there is no waiting in that model.  Here we
     require it explicitly --- it matches the second conjunct of
     [knows_datalog_fact dfacts (meta_fact R mf_args _)]. *)
  Lemma expect_num_R_facts_no_waiting inputs s rs R mf_args nf_args num :
    good_input_facts inputs ->
    sane_state inputs s ->
    In rs s ->
    expect_num_R_facts R mf_args rs.(known_facts) num ->
    Existsn (dfact_matches R mf_args) num rs.(known_facts) ->
    In (normal_dfact R nf_args) rs.(waiting_facts) ->
    Forall2 matches mf_args nf_args ->
    False.
  Proof.
    intros Hinp Hsane Hin Hexp Hex_kn Hwait Hmatch.
    destruct Hsane as (Hlen & Hmf_inp & Hmf_sent & Heverywhere & Hcount & Hinp_sane & _).
    specialize (Hcount R mf_args). fwd.
    rewrite Forall_forall in Hcountp2.
    specialize (Hcountp2 _ Hin).
    destruct Hcountp2 as (num_known & num_wait & Hex_known & Hex_wait & Hsum).
    pose proof (Existsn_unique _ _ _ _ Hex_kn Hex_known) as Hnk_eq.
    subst num_known.
    cbv [expect_num_R_facts] in Hexp.
    destruct (is_input R) eqn:ER.
    - (* input: meta_dfact in rs.known --> in inputs.  num_inp <= num.
         All rules have sent_facts count = 0 for input R.  Per-rule sum
         then forces num_wait <= 0; In matching contradicts. *)
      assert (Hk : knows_dfact s (meta_dfact R mf_args None num)).
      { cbv [knows_dfact]. apply Exists_exists. exists rs. split; auto.
        cbv [rule_has_dfact]. left. exact Hexp. }
      specialize (Hmf_inp _ _ _ Hk).
      destruct Hinp as (_ & Hinp_cnt).
      specialize (Hinp_cnt _ _ _ Hmf_inp).
      destruct Hinp_cnt as (_ & num' & Hle & Hexists_inp).
      pose proof (Existsn_unique _ _ _ _ Hexists_inp Hcountp1) as Hni_eq.
      subst num'.
      specialize (Hinp_sane R ER). destruct Hinp_sane as (Hinp_sane_zero & _).
      specialize (Hinp_sane_zero mf_args).
      assert (Hms_zero : Forall (eq 0) msgs_sents).
      { clear -Hcountp0 Hinp_sane_zero.
        induction Hcountp0; constructor.
        - apply Forall_cons_iff in Hinp_sane_zero. destruct Hinp_sane_zero as (Hzero & _).
          symmetry. eapply Existsn_unique; eassumption.
        - apply IHHcountp0.
          apply Forall_cons_iff in Hinp_sane_zero. apply (proj2 Hinp_sane_zero). }
      rewrite (fold_left_add_zero _ Hms_zero) in Hsum.
      assert (num_wait = 0) by lia.
      subst num_wait.
      apply Existsn_0_Forall_not in Hex_wait.
      rewrite Forall_forall in Hex_wait.
      apply (Hex_wait _ Hwait).
      exists nf_args. split; auto.
    - (* non-input: each per-rule meta_dfact in rs.known is consistent with
         that rule's sent_facts count, so msgs_sents = expected_msgss
         pointwise; sum equals num.  num_inp = 0 (non-input means no
         matching normals in inputs).  Per-rule sum forces num_wait = 0. *)
      fwd.
      assert (Hni_zero : num_inp = 0).
      { destruct Hinp as (Hrel & _).
        assert (Hno : Existsn (dfact_matches R mf_args) 0 inputs).
        { apply Forall_not_Existsn_0.
          apply Forall_forall. intros f Hin_f Hdf.
          destruct Hdf as (nf_args0 & Heq & _). subst f.
          rewrite Forall_forall in Hrel. specialize (Hrel _ Hin_f).
          simpl in Hrel. congruence. }
        symmetry. eapply Existsn_unique; eassumption. }
      subst num_inp.
      assert (Hms_eq : msgs_sents = expected_msgss).
      { apply nth_error_ext. intros k.
        pose proof (Forall2_length Hcountp0) as Hlen_ms.
        pose proof (Forall2_length Hexpp0) as Hlen_es.
        rewrite length_seq in Hlen_es.
        destruct (Nat.lt_ge_cases k (length msgs_sents)) as [Hkk | Hkk].
        + destruct (nth_error msgs_sents k) as [ms|] eqn:Hms; [|apply nth_error_None in Hms; lia].
          destruct (nth_error expected_msgss k) as [es|] eqn:Hes; [|apply nth_error_None in Hes; lia].
          f_equal.
          destruct (nth_error s k) as [rs_k|] eqn:Hrs_k; [|apply nth_error_None in Hrs_k; lia].
          pose proof (Forall2_nth_error_fwd _ _ _ Hcountp0 _ _ _ Hrs_k Hms) as HE_ms.
          cbv beta in HE_ms.
          assert (Hseq_k : nth_error (seq 0 (length (non_meta_rules p))) k = Some k).
          { rewrite nth_error_seq.
            assert (Hltb : (k <? length (non_meta_rules p)) = true) by (apply Nat.ltb_lt; lia).
            rewrite Hltb. reflexivity. }
          pose proof (Forall2_nth_error_fwd _ _ _ Hexpp0 _ _ _ Hseq_k Hes) as HE_es_in.
          cbv beta in HE_es_in.
          assert (Hknows : knows_dfact s (meta_dfact R mf_args (Some k) es)).
          { cbv [knows_dfact]. apply Exists_exists. exists rs. split; auto.
            cbv [rule_has_dfact]. left. exact HE_es_in. }
          specialize (Hmf_sent _ _ _ _ Hknows).
          cbv [nth_sat] in Hmf_sent. rewrite Hrs_k in Hmf_sent.
          destruct Hmf_sent as (HE_es & _).
          eapply Existsn_unique; eassumption.
        + rewrite (proj2 (nth_error_None _ _)) by lia.
          rewrite (proj2 (nth_error_None _ _)) by lia.
          reflexivity. }
      subst expected_msgss.
      assert (num_wait = 0) by lia.
      subst num_wait.
      apply Existsn_0_Forall_not in Hex_wait.
      rewrite Forall_forall in Hex_wait.
      apply (Hex_wait _ Hwait).
      exists nf_args. split; auto.
  Qed.
  
  Lemma Forall3_nth_error_fwd {A B C} (R : A -> B -> C -> Prop) xs ys zs :
    Forall3 R xs ys zs ->
    forall n x y z,
      nth_error xs n = Some x ->
      nth_error ys n = Some y ->
      nth_error zs n = Some z ->
      R x y z.
  Proof.
    induction 1; intros [|n] x' y' z' Hx Hy Hz; simpl in *; try discriminate.
    - injection Hx as ->. injection Hy as ->. injection Hz as ->. assumption.
    - eapply IHForall3; eassumption.
  Qed.

  Lemma Forall3_nth_error_bwd {A B C} (R : A -> B -> C -> Prop) xs ys zs :
    length xs = length ys ->
    length ys = length zs ->
    (forall n x y z,
        nth_error xs n = Some x ->
        nth_error ys n = Some y ->
        nth_error zs n = Some z ->
        R x y z) ->
    Forall3 R xs ys zs.
  Proof.
    revert ys zs.
    induction xs as [|x xs IH]; intros [|y ys] [|z zs] Hl1 Hl2 H;
      simpl in *; try discriminate; try constructor.
    - apply (H 0); reflexivity.
    - apply IH; auto. intros n x' y' z' Hx Hy Hz. apply (H (S n)); auto.
  Qed.

  (* With sent-based meta_facts_correct, the only nontrivial known-growth
     issue is in the learn_fact case at the firing rule (where wf moves
     from waiting to known).  This helper lifts a witness across that
     known-growth, encapsulating the saturation arguments. *)
  Lemma can_deduce_meta_fact_learn_fact inputs s x wf mf_concls mf_hyps r n result hyps :
    good_input_facts inputs ->
    sane_state inputs s ->
    In x s ->
    In wf x.(waiting_facts) ->
    In (mf_concls, mf_hyps) p.(meta_rules) ->
    In r p.(non_meta_rules) ->
    can_deduce_meta_fact mf_concls mf_hyps r n x.(sent_facts) x.(known_facts) result hyps ->
    Forall (knows_datalog_fact x.(known_facts)) hyps ->
    can_deduce_meta_fact mf_concls mf_hyps r n x.(sent_facts) (wf :: x.(known_facts)) result hyps /\
    Forall (knows_datalog_fact (wf :: x.(known_facts))) hyps.
  Proof.
    intros Hinp Hsane Hxs_in Hwf_in_wait Hmr_in Hr_in Hcdm Hknown_hyps.
    cbv [can_deduce_meta_fact] in Hcdm |- *.
    destruct Hcdm as (ctx & mf_rel' & mf_args' & mf_cnt' & Hres & HEx & Hconcl & Hinterp & Hclo).
    split.
    { (* can_deduce_meta_fact at (wf :: x.known) *)
      exists ctx, mf_rel', mf_args', mf_cnt'.
      split; [exact Hres|]. split; [exact HEx|]. split; [exact Hconcl|]. split; [exact Hinterp|].
      (* closure at (wf :: x.known) *)
      intros nf_args0 Hded Hmatch.
      destruct Hded as (hyps_d & Himpl & Hkn_d_new).
      (* Build rule_impl for the meta-rule with a constructed set *)
      pose (S_constr := fun args'' => one_step_derives rules_of hyps mf_rel' args'').
      assert (Hri_meta : rule_impl (one_step_derives rules_of) (meta_rule mf_concls mf_hyps)
                          (meta_fact mf_rel' mf_args' S_constr) hyps).
      { eapply meta_rule_impl with (ctx := ctx).
        - eapply Exists_impl; [|exact Hconcl]. intros c (mf_args0 & mf_set0 & Hf2 & Heq).
          injection Heq as Hrel Hargs _. subst.
          exists mf_args0, S_constr. split; [exact Hf2|]. reflexivity.
        - exact Hinterp.
        - intros args'' _. subst S_constr. simpl. reflexivity. }
      (* Build rule_impl for r *)
      assert (Hri_normal : rule_impl (one_step_derives rules_of) (rule_of r)
                            (normal_fact mf_rel' nf_args0) hyps_d).
      { apply simple_rule_impl. exact Himpl. }
      (* Apply meta_rules_valid *)
      assert (HFPS : Forall (fact_potentially_supported hyps) hyps_d).
      { eapply Hmeta_rules with (mr := meta_rule mf_concls mf_hyps)
                                 (nr := rule_of r); try eassumption.
        - cbv [rules_of]. apply in_app_iff. left.
          apply in_map_iff. exists (mf_concls, mf_hyps). split; [reflexivity|]. exact Hmr_in.
        - cbv [rules_of]. apply in_app_iff. right.
          apply in_map_iff. exists r. split; [reflexivity|]. exact Hr_in. }
      (* Now transfer Hkn_d_new (at NEW) to Hkn_d_old (at OLD) *)
      assert (Hkn_d_old : Forall (knows_datalog_fact x.(known_facts)) hyps_d).
      { rewrite Forall_forall in Hkn_d_new, HFPS, Hknown_hyps |- *.
        intros h Hh_in. specialize (Hkn_d_new _ Hh_in). specialize (HFPS _ Hh_in).
        destruct h as [R_h nf_args_h | R_h mf_args_h mf_set_h].
        - (* normal_fact h: use saturation to rule out h = wf *)
          cbv [fact_potentially_supported] in HFPS.
          destruct HFPS as (mf_args_h' & mf_set_h' & Hin_mhyp & Hmatch_h).
          specialize (Hknown_hyps _ Hin_mhyp).
          simpl in Hkn_d_new, Hknown_hyps |- *.
          destruct Hkn_d_new as [Hwf_is | Hkn_old]; [|exact Hkn_old].
          exfalso. destruct Hknown_hyps as (num_h & Hexp_h & Hex_h & _).
          eapply expect_num_R_facts_no_waiting; try eassumption.
          rewrite <- Hwf_is. exact Hwf_in_wait.
        - (* meta_fact h: use mhyps's knows_datalog_fact via Hknown_hyps *)
          cbv [fact_potentially_supported] in HFPS.
          destruct HFPS as (mf_set_h' & Hin_mhyp).
          specialize (Hknown_hyps _ Hin_mhyp).
          simpl in Hkn_d_new, Hknown_hyps |- *.
          destruct Hkn_d_new as (num & Hexp_new & Hex_new & Hsetcorr_new).
          destruct Hknown_hyps as (num_old & Hexp_old & Hex_old & _).
          exists num_old. split; [exact Hexp_old|]. split; [exact Hex_old|].
          intros nf_args1 Hmatch1.
          specialize (Hsetcorr_new _ Hmatch1).
          split.
          + intros Hs. apply Hsetcorr_new in Hs. simpl in Hs.
            destruct Hs as [Hwf_eq | Hold_in]; [|exact Hold_in].
            exfalso. eapply expect_num_R_facts_no_waiting; try eassumption.
            rewrite Hwf_eq in Hwf_in_wait. exact Hwf_in_wait.
          + intros Hin. apply Hsetcorr_new. apply in_cons. exact Hin. }
      (* Apply Hclo to get In ... at OLD *)
      assert (Hded_old : can_deduce_normal_fact r x.(known_facts) mf_rel' nf_args0).
      { cbv [can_deduce_normal_fact]. exists hyps_d. split; assumption. }
      specialize (Hclo _ Hded_old Hmatch).
      apply in_cons. exact Hclo. }
    { (* Forall (knows_datalog_fact (wf :: known)) hyps *)
      eapply Forall_impl; [|exact Hknown_hyps].
      intros h Hold. destruct h as [R_h nf_args_h | R_h mf_args_h mf_set_h].
      + simpl in Hold |- *. apply in_cons. exact Hold.
      + simpl in Hold |- *.
        destruct Hold as (num_h & Hexp_h & Hex_h & Hsetcorr_h).
        exists num_h. split; [|split].
        * cbv [expect_num_R_facts] in Hexp_h |- *.
          destruct (is_input R_h) eqn:Hin_R.
          -- right. exact Hexp_h.
          -- destruct Hexp_h as (expected_msgss & Hf2 & Hsum).
             exists expected_msgss. split; [|exact Hsum].
             eapply Forall2_impl_strong; [|exact Hf2].
             intros n_pos exp_n Hin_old _ _. apply in_cons. exact Hin_old.
        * apply Existsn_no; [|exact Hex_h].
          intros [nf_args_w [Hwf_eq Hmatch_w]].
          eapply expect_num_R_facts_no_waiting; try eassumption.
          rewrite Hwf_eq in Hwf_in_wait. exact Hwf_in_wait.
        * intros nf_args0 Hmatch.
          specialize (Hsetcorr_h _ Hmatch).
          split.
          -- intros Hset. apply in_cons. apply Hsetcorr_h. exact Hset.
          -- intros Hin. simpl in Hin. destruct Hin as [Hwf_eq | Hin_old].
             ++ exfalso. eapply expect_num_R_facts_no_waiting; try eassumption.
                rewrite Hwf_eq in Hwf_in_wait. exact Hwf_in_wait.
             ++ apply Hsetcorr_h. exact Hin_old. }
  Qed.

  Lemma step_preserves_mfs_correct inputs s s' :
    good_input_facts inputs ->
    sane_state inputs s ->
    meta_facts_correct s ->
    comp_step s s' ->
    meta_facts_correct s'.
  Proof.
    intros Hinp Hsane Hmfc Hstep.
    pose proof Hsane as Hsane'.
    destruct Hsane as (Hlen & Hmf_inp & Hmf_sent & Heverywhere & Hcount & Hinp_sane & _).
    invert Hstep.
    - (* learn_fact *)
      cbv [stepOne learn_fact_at_rule] in H.
      destruct H as (l1 & x & y & l2 & Hseq & Hs'eq & Hlfr).
      destruct Hlfr as (lw1 & wf & lw2 & Hyknown & Hxwait & Hywait & Hysent).
      assert (Hlen_lt : length l1 < length s).
      { rewrite Hseq, length_app. simpl. lia. }
      cbv [meta_facts_correct] in Hmfc |- *.
      apply Forall3_nth_error_bwd.
      + rewrite Hs'eq, ! length_app. simpl. rewrite Hseq, length_app in Hlen. simpl in Hlen. lia.
      + rewrite Hs'eq, length_seq, length_app. reflexivity.
      + intros n r rs k_seq Hk_r Hk_rs Hk_k.
        rewrite nth_error_seq in Hk_k.
        rewrite Hs'eq in Hk_k. rewrite length_app in Hk_k. simpl in Hk_k.
        destruct (n <? _) eqn:Hltb in Hk_k; [|discriminate].
        injection Hk_k as <-. apply Nat.ltb_lt in Hltb.
        assert (Hold_get : forall n0 r0 rs0,
                   nth_error (non_meta_rules p) n0 = Some r0 ->
                   nth_error s n0 = Some rs0 ->
                   meta_facts_correct_at_rule (meta_rules p) n0 rs0 r0).
        { intros n0 r0 rs0 Hr0 Hrs0.
          eapply (Forall3_nth_error_fwd _ _ _ _ Hmfc); try eassumption.
          rewrite nth_error_seq.
          assert (Hltb' : n0 <? length s = true).
          { apply Nat.ltb_lt. apply nth_error_Some_bound_index in Hrs0. assumption. }
          rewrite Hltb'. reflexivity. }
        rewrite Hs'eq, nth_error_app_middle in Hk_rs.
        destruct (Nat.compare_spec n (length l1)) as [Heq | Hlt | Hgt].
        * (* n = length l1: rule where learn_fact happened *)
          subst n.
          replace ((length l1 ?= length l1)) with Eq in Hk_rs by (symmetry; apply Nat.compare_refl).
          injection Hk_rs as <-.
          assert (Hxs : nth_error s (length l1) = Some x).
          { rewrite Hseq, nth_error_app2 by lia.
            rewrite Nat.sub_diag. reflexivity. }
          specialize (Hold_get _ _ _ Hk_r Hxs).
          cbv [meta_facts_correct_at_rule] in Hold_get |- *.
          intros R mf_args num HIn.
          (* HIn is in sent_facts y = sent_facts x (unchanged by learn_fact) *)
          rewrite Hysent in HIn.
          specialize (Hold_get _ _ _ HIn).
          fwd. exists mf_concls, mf_hyps, hyps. split; [assumption|].
          rewrite Hyknown, Hysent.
          assert (Hboth : can_deduce_meta_fact mf_concls mf_hyps r (length l1)
                            x.(sent_facts) (wf :: x.(known_facts))
                            (meta_dfact R mf_args (Some (length l1)) num) hyps /\
                          Forall (knows_datalog_fact (wf :: x.(known_facts))) hyps).
          { eapply can_deduce_meta_fact_learn_fact; try eassumption.
            { eapply nth_error_In; eassumption. }
            { rewrite Hxwait. apply in_app_iff. right. left. reflexivity. }
            { eapply nth_error_In; eassumption. } }
          destruct Hboth as (Hcan_new & Hknown_new).
          split; [exact Hcan_new|]. split; [exact Hknown_new|]. assumption.
        * (* n < length l1 *)
          replace ((n ?= length l1)) with Lt in Hk_rs by (symmetry; apply Nat.compare_lt_iff; lia).
          assert (Hsn : nth_error s n = Some rs).
          { rewrite Hseq, nth_error_app1 by lia. assumption. }
          specialize (Hold_get _ _ _ Hk_r Hsn). exact Hold_get.
        * (* n > length l1 *)
          replace ((n ?= length l1)) with Gt in Hk_rs by (symmetry; apply Nat.compare_gt_iff; lia).
          assert (Hsn : nth_error s n = Some rs).
          { rewrite Hseq, nth_error_app2 by lia.
            assert (Hoff : n - length l1 = S (n - length l1 - 1)) by lia.
            rewrite Hoff. simpl. assumption. }
          specialize (Hold_get _ _ _ Hk_r Hsn). exact Hold_get.
    - (* fire_normal_rule *)
      cbv [stepWithLabel] in H. fwd. destruct n as [r_fire k_fire].
      destruct Hp2 as (Hcan & Hnometa & Hyq). subst y.
      assert (Hlc : length (combine (non_meta_rules p) (seq 0 (length s))) = length s).
      { rewrite length_combine, length_seq. lia. }
      assert (Hs_eq : s = map snd l1 ++ x :: map snd l2).
      { apply (f_equal (map snd)) in Hp0.
        rewrite map_app in Hp0. simpl in Hp0.
        rewrite map_combine_snd in Hp0 by exact Hlc.
        exact Hp0. }
      assert (Hlen_lt : length l1 < length s).
      { rewrite Hs_eq, length_app, ! length_map. simpl. lia. }
      assert (Hk_eq : k_fire = length l1).
      { assert (Hlen_seq : length (non_meta_rules p) = length (seq 0 (length s))).
        { rewrite length_seq. lia. }
        pose proof Hp0 as Hp0a.
        apply (f_equal (map fst)) in Hp0a.
        rewrite map_app in Hp0a. simpl in Hp0a.
        rewrite map_combine_fst in Hp0a by exact Hlc.
        apply (f_equal (map snd)) in Hp0a.
        rewrite map_app in Hp0a. simpl in Hp0a.
        rewrite map_combine_snd in Hp0a by exact Hlen_seq.
        pose proof (f_equal (fun ll => nth_error ll (length l1)) Hp0a) as HnE.
        cbv beta in HnE.
        rewrite nth_error_app_middle in HnE.
        rewrite ! length_map in HnE.
        rewrite Nat.compare_refl in HnE.
        rewrite nth_error_seq in HnE.
        assert (E : length l1 <? length s = true) by (apply Nat.ltb_lt; lia).
        rewrite E in HnE.
        injection HnE as ->. lia. }
      cbv [meta_facts_correct] in Hmfc |- *.
      apply Forall3_nth_error_bwd.
      + rewrite Hs_eq, length_app, ! length_map in Hlen. simpl in Hlen.
        rewrite ! length_map in Hlen.
        rewrite length_map, length_app, length_map. simpl. rewrite length_map. lia.
      + rewrite length_map, length_seq, length_app, ! length_map. reflexivity.
      + intros n r rs k_seq Hk_r Hk_rs Hk_k.
        rewrite nth_error_seq in Hk_k.
        destruct (n <? _) eqn:Hltb in Hk_k; [|discriminate].
        injection Hk_k as <-. apply Nat.ltb_lt in Hltb.
        rewrite nth_error_map in Hk_rs.
        destruct (nth_error (map snd l1 ++ send_fact (normal_dfact nf_rel nf_args) x :: map snd l2) n)
          as [rs_inner|] eqn:Hk_rsi; [|discriminate].
        simpl in Hk_rs. injection Hk_rs as <-.
        (* Get old meta_facts_correct_at_rule from Hmfc *)
        assert (Hold_get : forall n0 r0 rs0,
                   nth_error (non_meta_rules p) n0 = Some r0 ->
                   nth_error s n0 = Some rs0 ->
                   meta_facts_correct_at_rule (meta_rules p) n0 rs0 r0).
        { intros n0 r0 rs0 Hr0 Hrs0.
          eapply (Forall3_nth_error_fwd _ _ _ _ Hmfc); try eassumption.
          rewrite nth_error_seq.
          assert (Hltb' : n0 <? length s = true).
          { apply Nat.ltb_lt. apply nth_error_Some_bound_index in Hrs0. assumption. }
          rewrite Hltb'. reflexivity. }
        rewrite nth_error_app_middle, length_map in Hk_rsi.
        destruct (Nat.compare_spec n (length l1)) as [Heq | Hlt | Hgt].
        * (* n = length l1: firing rule *)
          subst n.
          replace ((length l1 ?= length l1)) with Eq in Hk_rsi by (symmetry; apply Nat.compare_refl).
          injection Hk_rsi as <-.
          assert (Hxs : nth_error s (length l1) = Some x).
          { rewrite Hs_eq, nth_error_app2 by (rewrite length_map; lia).
            rewrite length_map, Nat.sub_diag. reflexivity. }
          specialize (Hold_get _ _ _ Hk_r Hxs).
          cbv [meta_facts_correct_at_rule] in Hold_get |- *.
          intros R mf_args num HIn. simpl in HIn.
          destruct HIn as [Heq_F | HIn_old]; [discriminate|].
          specialize (Hold_get _ _ _ HIn_old).
          fwd. exists mf_concls, mf_hyps, hyps. split; [assumption|].
          cbv [can_deduce_meta_fact] in Hold_getp1 |- *.
          destruct Hold_getp1 as (ctx & mf_rel' & mf_args' & mf_cnt' & Hres & HEx & Hconcl & Hinterp & Hclo).
          injection Hres as Heq1 Heq2 Heq3.
          subst mf_rel' mf_args' mf_cnt'.
          split; [|split].
          { exists ctx, R, mf_args, num. split; [reflexivity|].
            split.
            { (* Existsn count over (F :: x.sent) — need to show F doesn't match *)
              simpl.
              assert (Hnomatch : ~ dfact_matches R mf_args (normal_dfact nf_rel nf_args)).
              { intros [nf_args2 [Heq Hmatch]]. injection Heq as -> ->.
                eapply Hnometa; [|eassumption].
                rewrite Hk_eq. exact HIn_old. }
              apply Existsn_no; assumption. }
            split; [exact Hconcl|]. split; [exact Hinterp|]. exact Hclo. }
          { assumption. }
          { assumption. }
        * (* n < length l1: unchanged rule *)
          replace ((n ?= length l1)) with Lt in Hk_rsi by (symmetry; apply Nat.compare_lt_iff; lia).
          rewrite nth_error_map in Hk_rsi.
          destruct (nth_error l1 n) as [pair_n|] eqn:Hl1n; [|discriminate].
          simpl in Hk_rsi. injection Hk_rsi as Hri.
          assert (Hsn : nth_error s n = Some rs_inner).
          { rewrite Hs_eq, nth_error_app1 by (rewrite length_map; lia).
            rewrite nth_error_map, Hl1n. simpl. f_equal. assumption. }
          specialize (Hold_get _ _ _ Hk_r Hsn). exact Hold_get.
        * (* n > length l1: unchanged rule *)
          replace ((n ?= length l1)) with Gt in Hk_rsi by (symmetry; apply Nat.compare_gt_iff; lia).
          rewrite nth_error_map in Hk_rsi.
          destruct (nth_error l2 (n - length l1 - 1)) as [pair_n|] eqn:Hl2n; [|discriminate].
          simpl in Hk_rsi. injection Hk_rsi as Hri.
          assert (Hsn : nth_error s n = Some rs_inner).
          { rewrite Hs_eq, nth_error_app2 by (rewrite length_map; lia).
            rewrite length_map.
            assert (Hoff : n - length l1 = S (n - length l1 - 1)) by lia.
            rewrite Hoff. simpl. rewrite nth_error_map, Hl2n. simpl. f_equal. assumption. }
          specialize (Hold_get _ _ _ Hk_r Hsn). exact Hold_get.
    - (* fire_meta_rule *)
      rename H into Hmr_in.
      cbv [stepWithLabel] in H0. fwd. destruct n as [r_fire k_fire].
      destruct H0p2 as (Hcan & Hknown_h & Hyq). subst y.
      assert (Hnf_meta : exists mf_rel0 mf_args0 mf_cnt0, new_fact = meta_dfact mf_rel0 mf_args0 (Some k_fire) mf_cnt0).
      { cbv [can_deduce_meta_fact] in Hcan. destruct Hcan as (_ & ?r & ?a & ?c & ? & _). eauto. }
      destruct Hnf_meta as (new_mfr & new_mfa & new_mfc & Hnf_eq).
      assert (Hlc : length (combine (non_meta_rules p) (seq 0 (length s))) = length s).
      { rewrite length_combine, length_seq. lia. }
      assert (Hs_eq : s = map snd l1 ++ x :: map snd l2).
      { apply (f_equal (map snd)) in H0p0.
        rewrite map_app in H0p0. simpl in H0p0.
        rewrite map_combine_snd in H0p0 by exact Hlc.
        exact H0p0. }
      assert (Hlen_lt : length l1 < length s).
      { rewrite Hs_eq, length_app, ! length_map. simpl. lia. }
      assert (Hk_eq : k_fire = length l1).
      { assert (Hlen_seq : length (non_meta_rules p) = length (seq 0 (length s))).
        { rewrite length_seq. lia. }
        pose proof H0p0 as Hp0a.
        apply (f_equal (map fst)) in Hp0a.
        rewrite map_app in Hp0a. simpl in Hp0a.
        rewrite map_combine_fst in Hp0a by exact Hlc.
        apply (f_equal (map snd)) in Hp0a.
        rewrite map_app in Hp0a. simpl in Hp0a.
        rewrite map_combine_snd in Hp0a by exact Hlen_seq.
        pose proof (f_equal (fun ll => nth_error ll (length l1)) Hp0a) as HnE.
        cbv beta in HnE.
        rewrite nth_error_app_middle in HnE.
        rewrite ! length_map in HnE.
        rewrite Nat.compare_refl in HnE.
        rewrite nth_error_seq in HnE.
        assert (E : length l1 <? length s = true) by (apply Nat.ltb_lt; lia).
        rewrite E in HnE.
        injection HnE as ->. lia. }
      cbv [meta_facts_correct] in Hmfc |- *.
      apply Forall3_nth_error_bwd.
      + rewrite Hs_eq, length_app, ! length_map in Hlen. simpl in Hlen.
        rewrite ! length_map in Hlen.
        rewrite length_map, length_app, length_map. simpl. rewrite length_map. lia.
      + rewrite length_map, length_seq, length_app, ! length_map. reflexivity.
      + intros n r rs k_seq Hk_r Hk_rs Hk_k.
        rewrite nth_error_seq in Hk_k.
        destruct (n <? _) eqn:Hltb in Hk_k; [|discriminate].
        injection Hk_k as <-. apply Nat.ltb_lt in Hltb.
        rewrite nth_error_map in Hk_rs.
        destruct (nth_error (map snd l1 ++ send_fact new_fact x :: map snd l2) n)
          as [rs_inner|] eqn:Hk_rsi; [|discriminate].
        simpl in Hk_rs. injection Hk_rs as <-.
        assert (Hold_get : forall n0 r0 rs0,
                   nth_error (non_meta_rules p) n0 = Some r0 ->
                   nth_error s n0 = Some rs0 ->
                   meta_facts_correct_at_rule (meta_rules p) n0 rs0 r0).
        { intros n0 r0 rs0 Hr0 Hrs0.
          eapply (Forall3_nth_error_fwd _ _ _ _ Hmfc); try eassumption.
          rewrite nth_error_seq.
          assert (Hltb' : n0 <? length s = true).
          { apply Nat.ltb_lt. apply nth_error_Some_bound_index in Hrs0. assumption. }
          rewrite Hltb'. reflexivity. }
        rewrite nth_error_app_middle, length_map in Hk_rsi.
        destruct (Nat.compare_spec n (length l1)) as [Heq | Hlt | Hgt].
        * (* n = length l1: firing rule *)
          subst n.
          replace ((length l1 ?= length l1)) with Eq in Hk_rsi by (symmetry; apply Nat.compare_refl).
          injection Hk_rsi as <-.
          assert (Hxs : nth_error s (length l1) = Some x).
          { rewrite Hs_eq, nth_error_app2 by (rewrite length_map; lia).
            rewrite length_map, Nat.sub_diag. reflexivity. }
          specialize (Hold_get _ _ _ Hk_r Hxs).
          cbv [meta_facts_correct_at_rule] in Hold_get |- *.
          intros R mf_args num HIn. simpl in HIn.
          destruct HIn as [Heq_nf | HIn_old].
          { (* HIn picks new_fact = meta_dfact R mf_args (Some (length l1)) num *)
            assert (Hr_eq : r = r_fire).
            { assert (Hlen_seq : length (non_meta_rules p) = length (seq 0 (length s))).
              { rewrite length_seq. lia. }
              pose proof H0p0 as Hp0a.
              apply (f_equal (map fst)) in Hp0a.
              rewrite map_app in Hp0a. simpl in Hp0a.
              rewrite map_combine_fst in Hp0a by exact Hlc.
              apply (f_equal (map fst)) in Hp0a.
              rewrite map_app in Hp0a. simpl in Hp0a.
              rewrite map_combine_fst in Hp0a by exact Hlen_seq.
              pose proof (f_equal (fun ll => nth_error ll (length l1)) Hp0a) as HnE.
              cbv beta in HnE.
              rewrite nth_error_app_middle in HnE.
              rewrite ! length_map in HnE.
              rewrite Nat.compare_refl in HnE.
              rewrite HnE in Hk_r. injection Hk_r as ->. reflexivity. }
            subst r.
            cbv [can_deduce_meta_fact] in Hcan |- *.
            destruct Hcan as (ctx & mf_rel' & mf_args' & mf_cnt' & Hres & HEx & Hconcl & Hinterp & Hclo).
            pose proof (eq_trans (eq_sym Heq_nf) Hres) as Hcombined.
            injection Hcombined as Heq_R Heq_args Hkeq_lk Heq_num.
            subst mf_rel' mf_args' mf_cnt'.
            (* R is non-input: by good_meta_rule_inputs applied to mf_concls *)
            assert (HNI_R : is_input R = false).
            { rewrite Forall_forall in Hp_meta_input.
              specialize (Hp_meta_input _ Hmr_in). simpl in Hp_meta_input.
              rewrite Forall_forall in Hp_meta_input.
              apply Exists_exists in Hconcl. destruct Hconcl as (c_concl & Hin_c & Hint_c).
              specialize (Hp_meta_input _ Hin_c).
              cbv [interp_meta_clause] in Hint_c.
              destruct Hint_c as (mfa_v & mfs_v & _ & Heqv).
              injection Heqv as Hrel _ _. rewrite <- Hrel in Hp_meta_input. exact Hp_meta_input. }
            (* Decide: does the firing's hyps contain a self-referential meta-fact? *)
            destruct (classic (exists mfs', In (meta_fact R mf_args mfs') hyps))
              as [Hself | Hnoself].
            - (* SELF-REF: extract OLD witness with no-self-ref hyps_old *)
              destruct Hself as (mfs' & Hin_hyp).
              rewrite Forall_forall in Hknown_h.
              pose proof (Hknown_h _ Hin_hyp) as Hkdf_self.
              simpl in Hkdf_self.
              destruct Hkdf_self as (num_self & Hexp_self & _ & _).
              cbv [expect_num_R_facts] in Hexp_self. rewrite HNI_R in Hexp_self.
              destruct Hexp_self as (expected_msgss & Hf2 & _).
              pose proof (Forall2_length Hf2) as Hlen_msgs. rewrite length_seq in Hlen_msgs.
              assert (Hlen_lt2 : length l1 < length p.(non_meta_rules)).
              { rewrite Hs_eq, length_app, ! length_map in Hlen.
                simpl in Hlen. lia. }
              assert (Hk_seq2 : nth_error (seq 0 (length p.(non_meta_rules))) (length l1) = Some (length l1)).
              { rewrite nth_error_seq.
                assert (E : length l1 <? length p.(non_meta_rules) = true)
                  by (apply Nat.ltb_lt; lia).
                rewrite E. reflexivity. }
              assert (Hk_msg : exists m, nth_error expected_msgss (length l1) = Some m).
              { destruct (nth_error expected_msgss (length l1)) eqn:Em.
                - eexists. reflexivity.
                - apply nth_error_None in Em. lia. }
              destruct Hk_msg as (num_old & Hmsg).
              pose proof (Forall2_nth_error_fwd _ _ _ Hf2 (length l1) _ _ Hk_seq2 Hmsg)
                as Hin_x_known.
              (* Lift to x.sent via Hmf_sent — already in scope *)
              assert (Hknows_old : knows_dfact s
                (meta_dfact R mf_args (Some (length l1)) num_old)).
              { cbv [knows_dfact]. apply Exists_exists. exists x. split.
                - rewrite Hs_eq. apply in_or_app. right. apply in_eq.
                - left. exact Hin_x_known. }
              specialize (Hmf_sent _ _ _ _ Hknows_old).
              cbv [nth_sat] in Hmf_sent.
              assert (Hnth_x : nth_error s (length l1) = Some x).
              { rewrite Hs_eq, nth_error_app2 by (rewrite length_map; lia).
                rewrite length_map, Nat.sub_diag. reflexivity. }
              rewrite Hnth_x in Hmf_sent.
              destruct Hmf_sent as (_ & Hin_x_sent).
              (* Apply OLD Hold_get *)
              specialize (Hold_get R mf_args num_old Hin_x_sent).
              destruct Hold_get as (mfc_old & mfh_old & hyps_old & Hin_mr_old & Hcan_old & Hknown_old & Hnoself_old).
              exists mfc_old, mfh_old, hyps_old.
              split; [exact Hin_mr_old|].
              cbv [can_deduce_meta_fact] in Hcan_old |- *.
              destruct Hcan_old as (ctx_old & mro & mao & mco & Hres_old & HEx_old & Hconcl_old & Hinterp_old & Hclo_old).
              injection Hres_old as Hr_o Ha_o _. subst mro mao.
              split; [|split].
              + (* can_deduce_meta_fact: reuse OLD's structure, fresh mf_cnt = num *)
                exists ctx_old, R, mf_args, num. split; [reflexivity|].
                split.
                { simpl. rewrite Heq_nf. apply Existsn_no; [|exact HEx].
                  intros [nf_args2 [Heq _]]. discriminate. }
                split; [exact Hconcl_old|]. split; [exact Hinterp_old|]. exact Hclo_old.
              + exact Hknown_old.
              + exact Hnoself_old.
            - (* NO SELF-REF: use firing's hyps directly *)
              exists mf_concls, mf_hyps, hyps. split; [exact Hmr_in|].
              split; [|split].
              { exists ctx, R, mf_args, num. split; [reflexivity|].
                split.
                { simpl. rewrite Heq_nf. apply Existsn_no; [|assumption].
                  intros [nf_args2 [Heq Hmatch]]. discriminate. }
                split; [exact Hconcl|]. split; [exact Hinterp|]. exact Hclo. }
              { exact Hknown_h. }
              { intros mfs Hin'. apply Hnoself. exists mfs. exact Hin'. } }
          { (* HIn picks an old (Some length l1) meta-fact in x.sent *)
            specialize (Hold_get _ _ _ HIn_old).
            fwd. exists mf_concls0, mf_hyps0, hyps0. split; [exact Hold_getp0|].
            cbv [can_deduce_meta_fact] in Hold_getp1 |- *.
            destruct Hold_getp1 as (ctx & mf_rel' & mf_args' & mf_cnt' & Hres & HEx & Hconcl & Hinterp & Hclo).
            injection Hres as Heq1 Heq2 Heq3.
            subst mf_rel' mf_args' mf_cnt'.
            split; [|split].
            { exists ctx, R, mf_args, num. split; [reflexivity|].
              split.
              { simpl. rewrite Hnf_eq. apply Existsn_no; [|assumption].
                intros [nf_args2 [Heq Hmatch]]. discriminate. }
              split; [exact Hconcl|]. split; [exact Hinterp|]. exact Hclo. }
            { exact Hold_getp2. }
            { exact Hold_getp3. } }
        * (* n < length l1 *)
          replace ((n ?= length l1)) with Lt in Hk_rsi by (symmetry; apply Nat.compare_lt_iff; lia).
          rewrite nth_error_map in Hk_rsi.
          destruct (nth_error l1 n) as [pair_n|] eqn:Hl1n; [|discriminate].
          simpl in Hk_rsi. injection Hk_rsi as Hri.
          assert (Hsn : nth_error s n = Some rs_inner).
          { rewrite Hs_eq, nth_error_app1 by (rewrite length_map; lia).
            rewrite nth_error_map, Hl1n. simpl. f_equal. assumption. }
          specialize (Hold_get _ _ _ Hk_r Hsn). exact Hold_get.
        * (* n > length l1 *)
          replace ((n ?= length l1)) with Gt in Hk_rsi by (symmetry; apply Nat.compare_gt_iff; lia).
          rewrite nth_error_map in Hk_rsi.
          destruct (nth_error l2 (n - length l1 - 1)) as [pair_n|] eqn:Hl2n; [|discriminate].
          simpl in Hk_rsi. injection Hk_rsi as Hri.
          assert (Hsn : nth_error s n = Some rs_inner).
          { rewrite Hs_eq, nth_error_app2 by (rewrite length_map; lia).
            rewrite length_map.
            assert (Hoff : n - length l1 = S (n - length l1 - 1)) by lia.
            rewrite Hoff. simpl. rewrite nth_error_map, Hl2n. simpl. f_equal. assumption. }
          specialize (Hold_get _ _ _ Hk_r Hsn). exact Hold_get.
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
    | normal_fact R args => knows_dfact s (normal_dfact R args)
    | meta_fact R mf_args mf_set =>
        if is_input R then
          exists num, knows_dfact s (meta_dfact R mf_args None num)
        else
          forall k, k < length p.(non_meta_rules) ->
            exists num,
              knows_dfact s (meta_dfact R mf_args (Some k) num)
    end.

  Definition mf_consistent_state (s : state) (f : fact) :=
    match f with
    | normal_fact _ _ => True
    | meta_fact R mf_args mf_set =>
        forall nf_args,
          Forall2 matches mf_args nf_args ->
          mf_set nf_args <-> knows_dfact s (normal_dfact R nf_args)
    end.

  Definition state_correct (inputs : list dfact) (s : state) :=
    forall f,
      has_derived_datalog_fact s f /\ mf_consistent_state s f ->
      prog_impl rules_of (knows_datalog_fact inputs) f.

  (* Lift a per-rule [knows_datalog_fact rs.known h] to [has_derived_datalog_fact s h]
     for any rs in s.  For normal facts this is just "exists rs with the dfact".  For
     meta facts the input branch uses the [expect_num_R_facts] count directly; the
     non-input branch extracts the per-source-rule count witness from the Forall2. *)
  Lemma knows_datalog_fact_local_lift_has_derived inputs s rs h :
    good_input_facts inputs ->
    sane_state inputs s ->
    In rs s ->
    knows_datalog_fact rs.(known_facts) h ->
    has_derived_datalog_fact s h.
  Proof.
    intros _ Hsane Hin Hkdf.
    destruct h as [R0 args0 | R0 mf_args0 mf_set0]; simpl in Hkdf |- *.
    - cbv [knows_dfact]. apply Exists_exists. exists rs. split; [exact Hin|].
      left. exact Hkdf.
    - destruct Hkdf as (num & Hsat & _ & _).
      cbv [expect_num_R_facts] in Hsat.
      destruct (is_input R0) eqn:HER0.
      + exists num. cbv [knows_dfact]. apply Exists_exists.
        exists rs. split; [exact Hin|]. left. exact Hsat.
      + intros k Hk. destruct Hsat as (msgss & Hf2 & _).
        pose proof (Forall2_length Hf2) as Hlen_msgs. rewrite length_seq in Hlen_msgs.
        assert (Hk_seq : nth_error (seq 0 (length p.(non_meta_rules))) k = Some k).
        { rewrite nth_error_seq.
          assert (E : k <? length p.(non_meta_rules) = true) by (apply Nat.ltb_lt; exact Hk).
          rewrite E. reflexivity. }
        assert (Hk_msg : exists m, nth_error msgss k = Some m).
        { destruct (nth_error msgss k) eqn:E; [eauto|].
          apply nth_error_None in E. lia. }
        destruct Hk_msg as (m & Hkm).
        pose proof (Forall2_nth_error_fwd _ _ _ Hf2 k k m Hk_seq Hkm) as Hin_m.
        exists m. cbv [knows_dfact]. apply Exists_exists. exists rs.
        split; [exact Hin|]. left. exact Hin_m.
  Qed.

  Lemma knows_datalog_fact_local_lift_mf_consistent inputs s rs h :
    good_input_facts inputs ->
    sane_state inputs s ->
    In rs s ->
    knows_datalog_fact rs.(known_facts) h ->
    mf_consistent_state s h.
  Proof.
    intros Hinp Hsane Hin Hkdf.
    destruct h as [R0 args0 | R0 mf_args0 mf_set0]; simpl; [exact I|].
    intros nf_args Hmatch.
    destruct Hkdf as (num & Hsat & Hexn & Hbic).
    specialize (Hbic _ Hmatch). rewrite Hbic. split.
    - intros Hin_k. cbv [knows_dfact]. apply Exists_exists. exists rs.
      split; [exact Hin|]. left. exact Hin_k.
    - intros Hkd.
      pose proof Hsane as (_ & _ & _ & Heverywhere & _ & _).
      pose proof (Heverywhere _ Hkd) as Hev. rewrite Forall_forall in Hev.
      specialize (Hev _ Hin). cbv [rule_has_dfact] in Hev.
      destruct Hev as [Hin_k | Hin_w]; [exact Hin_k|].
      exfalso. eapply expect_num_R_facts_no_waiting; eassumption.
  Qed.

  Lemma learn_fact_preserves_knows_dfact s s' f :
    stepOne learn_fact_at_rule s s' ->
    knows_dfact s f <-> knows_dfact s' f.
  Proof.
    intros (l1 & x & y & l2 & Hs & Hs' & Hlfr).
    pose proof (learn_fact_at_rule_rule_has_dfact _ _ Hlfr f) as Hpres.
    subst. cbv [knows_dfact]. split; apply exists_swap; apply Hpres.
  Qed.

  Lemma learn_fact_preserves_has_derived_datalog_fact s s' f :
    stepOne learn_fact_at_rule s s' ->
    has_derived_datalog_fact s f <-> has_derived_datalog_fact s' f.
  Proof.
    intros Hstep. cbv [has_derived_datalog_fact].
    destruct f as [R args | R mf_args mf_set]; [apply learn_fact_preserves_knows_dfact; assumption|].
    destruct (is_input R).
    - split; intros (num & Hk); exists num;
        apply (learn_fact_preserves_knows_dfact _ _ _ Hstep); assumption.
    - split; intros H k Hk; specialize (H k Hk);
        destruct H as (num & Hk_d); exists num;
        apply (learn_fact_preserves_knows_dfact _ _ _ Hstep); assumption.
  Qed.

  Lemma learn_fact_preserves_mf_consistent_state s s' f :
    stepOne learn_fact_at_rule s s' ->
    mf_consistent_state s f <-> mf_consistent_state s' f.
  Proof.
    intros Hstep. cbv [mf_consistent_state].
    destruct f as [|R mf_args mf_set]; [reflexivity|].
    split; intros H nf_args Hmatch; specialize (H nf_args Hmatch); rewrite H.
    - apply learn_fact_preserves_knows_dfact. assumption.
    - symmetry. apply learn_fact_preserves_knows_dfact. assumption.
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
        cbv [expect_num_R_facts] in Hexp.
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
          pose proof (Forall2_length Hf2_msgs) as Hlen_msgs.
          rewrite length_seq in Hlen_msgs.
          assert (H0_seq : nth_error (seq 0 (length p.(non_meta_rules))) 0 = Some 0).
          { rewrite nth_error_seq.
            assert (E : 0 <? length p.(non_meta_rules) = true)
              by (apply Nat.ltb_lt; exact Hlt).
            rewrite E. reflexivity. }
          assert (H0_msg : exists m, nth_error msgss 0 = Some m).
          { destruct (nth_error msgss 0) eqn:Em; [eauto|].
            apply nth_error_None in Em. lia. }
          destruct H0_msg as (m0 & Hm0).
          pose proof (Forall2_nth_error_fwd _ _ _ Hf2_msgs 0 0 m0 H0_seq Hm0)
            as Hin_m0.
          destruct Hinp as (Hinp_all & _). rewrite Forall_forall in Hinp_all.
          specialize (Hinp_all _ Hin_m0). simpl in Hinp_all. congruence.
    - cbv [doesnt_lie consistent]. intros mfr0 mfa0 mfs0 Hin nf_args0 Hmatch_nf.
      simpl in Hin. destruct Hin as (num0 & _ & _ & Hbic).
      simpl. apply Hbic. exact Hmatch_nf.
  Qed.

  Lemma use_meta_facts_correct (R : rel) (mf_args : list (option T))
    (inputs : list dfact) (s : state) :
    good_input_facts inputs ->
    sane_state inputs s ->
    meta_facts_correct s ->
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
      knows_dfact s (normal_dfact R nf_args).
  Proof.
    intros Hinp Hsane Hmf HER HRs HR nf_args Hmatch Hprog.
    invert Hprog.
    - (* Q-leaf: contradicts is_input R = false *)
      simpl in H.
      destruct Hinp as (Hinp_all & _). rewrite Forall_forall in Hinp_all.
      specialize (Hinp_all _ H). simpl in Hinp_all. congruence.
    - (* rule_step: rule r in rules_of derives normal_fact R nf_args from hyps *)
      rename H into Hrule_exists. rename H0 into Hhyps. rename l into hyps.
      apply Exists_exists in Hrule_exists.
      destruct Hrule_exists as (r & Hin_r & Hrule_impl).
      invert Hrule_impl.
      (* After invert, we have a non_meta_rule_impl hypothesis (named by Coq) *)
      match goal with H : non_meta_rule_impl _ _ _ _ |- _ => rename H into Hnmri end.
      (* Find k such that r = rule_of r_k *)
      unfold rules_of in Hin_r. apply in_app_or in Hin_r.
      destruct Hin_r as [Hin_meta_r | Hin_nonmeta_r].
      { (* r is a meta_rule, but non_meta_rule_impl r requires r = normal_rule or agg_rule *)
        apply in_map_iff in Hin_meta_r. destruct Hin_meta_r as ((c & h) & Heq_r & _).
        subst r. invert Hnmri. }
      apply in_map_iff in Hin_nonmeta_r.
      destruct Hin_nonmeta_r as (r_k & Heq_r & Hin_rk).
      subst r.
      pose proof Hin_rk as Hin_rk_save.
      apply In_nth_error in Hin_rk. destruct Hin_rk as (k & Hnth_k).
      rename Hin_rk_save into Hin_rk.
      apply nth_error_Some_bound_index in Hnth_k as Hk_lt.
      (* Extract meta-fact knowledge for index k *)
      simpl in HR. rewrite HER in HR.
      specialize (HR _ Hk_lt). destruct HR as (num_k & Hkknows).
      pose proof Hsane as (Hlen & Hmf_inp & Hmf_sent & Heverywhere & Hcount & Hinp_sane & _).
      pose proof (Hmf_sent _ _ _ _ Hkknows) as Hsent_k.
      cbv [nth_sat] in Hsent_k.
      destruct (nth_error s k) as [rs_k|] eqn:Hnth_s; [|contradiction].
      destruct Hsent_k as (Hexn_k & Hin_k_sent).
      (* By meta_facts_correct, can_deduce_meta_fact witness at index k *)
      cbv [meta_facts_correct] in Hmf.
      assert (Hk_seq : nth_error (seq 0 (length s)) k = Some k).
      { rewrite nth_error_seq.
        assert (E : k <? length s = true) by (apply Nat.ltb_lt; lia).
        rewrite E. reflexivity. }
      assert (Hmf_k : meta_facts_correct_at_rule p.(meta_rules) k rs_k r_k).
      { eapply (Forall3_nth_error_fwd _ _ _ _ Hmf); eassumption. }
      cbv [meta_facts_correct_at_rule] in Hmf_k.
      specialize (Hmf_k _ _ _ Hin_k_sent).
      destruct Hmf_k as (mf_concls & mf_hyps & hyps_d & Hin_mr & Hcan & Hkdf_h & Hnoselfref_h).
      cbv [can_deduce_meta_fact] in Hcan.
      destruct Hcan as (ctx & mf_rel_c & mf_args_c & mf_cnt_c
                       & Heq_F & Hexn_F & Hconcl & Hf2_h & Hsound_can).
      injection Heq_F as Hr_eq Ha_eq Hc_eq.
      subst mf_rel_c mf_args_c mf_cnt_c.
      (* Build can_deduce_normal_fact: hyps are in rs_k.known *)
      assert (Hcan_nf : can_deduce_normal_fact r_k rs_k.(known_facts) R nf_args).
      { cbv [can_deduce_normal_fact]. exists hyps. split; [exact Hnmri|].
        (* Build prog_impl ... (meta_fact R mf_args S_constr) for use with
           meta_rules_valid to get fact_potentially_supported. *)
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
        (* For each hyp h, fact_potentially_supported hyps_d h.  Lift to
           knows_datalog_fact rs_k.known h via the meta-fact in hyps_d. *)
        rewrite Forall_forall. intros h Hh.
        rewrite Forall_forall in Hpot, Hkdf_h, Hhyps.
        pose proof (Hpot _ Hh) as Hpot_h.
        pose proof (Hhyps _ Hh) as Hprog_h.
        assert (Hgood_inputs_Q : good_inputs rules_of (knows_datalog_fact inputs)).
        { apply good_inputs_knows_datalog_fact_inputs; [exact Hinp|]. lia. }
        pose proof (valid_impl_honest _ Hmeta_rules _ Hgood_inputs_Q) as Hhonest.
        cbv [doesnt_lie] in Hhonest.
        assert (Hin_rs_k : In rs_k s) by (eapply nth_error_In; eassumption).
        (* Now handle h based on its shape *)
        destruct h as [R' args' | R' mf_args' mf_set'_h].
        + (* normal hyp *)
          cbv [fact_potentially_supported] in Hpot_h.
          destruct Hpot_h as (mf_args' & mf_set'_m & Hin_m & Hmatch_m).
          pose proof (Hkdf_h _ Hin_m) as Hkd_m.
          destruct (classic ((R, mf_args) = (R', mf_args'))) as [Heq | Hne].
          * (* SELF-RECURSIVE: ruled out by Hnoselfref_h *)
            exfalso. injection Heq as -> ->.
            apply (Hnoselfref_h mf_set'_m). exact Hin_m.
          * (* non-self-recursive case *)
            pose proof (knows_datalog_fact_local_lift_has_derived _ _ _ _ Hinp Hsane Hin_rs_k Hkd_m) as Hhd_m.
            pose proof (knows_datalog_fact_local_lift_mf_consistent _ _ _ _ Hinp Hsane Hin_rs_k Hkd_m) as Hmc_m.
            pose proof (HRs _ _ _ Hne (conj Hhd_m Hmc_m)) as Hprog_m.
            pose proof (Hhonest _ _ _ Hprog_m) as Hcon_m.
            cbv [consistent] in Hcon_m.
            specialize (Hcon_m _ Hmatch_m).
            apply Hcon_m in Hprog_h.
            simpl in Hkd_m. destruct Hkd_m as (num_m & _ & _ & Hbic_m).
            specialize (Hbic_m _ Hmatch_m).
            simpl. apply Hbic_m. exact Hprog_h.
        + (* meta hyp *)
          cbv [fact_potentially_supported] in Hpot_h.
          destruct Hpot_h as (mf_set'_m & Hin_m).
          pose proof (Hkdf_h _ Hin_m) as Hkd_m.
          destruct (classic ((R, mf_args) = (R', mf_args'))) as [Heq | Hne].
          * (* SELF-RECURSIVE: ruled out by Hnoselfref_h *)
            exfalso. injection Heq as -> ->.
            apply (Hnoselfref_h mf_set'_m). exact Hin_m.
          * (* non-self-recursive *)
            pose proof (knows_datalog_fact_local_lift_has_derived _ _ _ _ Hinp Hsane Hin_rs_k Hkd_m) as Hhd_m.
            pose proof (knows_datalog_fact_local_lift_mf_consistent _ _ _ _ Hinp Hsane Hin_rs_k Hkd_m) as Hmc_m.
            pose proof (HRs _ _ _ Hne (conj Hhd_m Hmc_m)) as Hprog_m.
            pose proof (Hhonest _ _ _ Hprog_m) as Hcon_m.
            pose proof (Hhonest _ _ _ Hprog_h) as Hcon_h.
            cbv [consistent] in Hcon_m, Hcon_h.
            (* Both consistent: mf_set'_h and mf_set'_m agree with prog_impl_normal *)
            simpl in Hkd_m |- *.
            destruct Hkd_m as (num_m & Hexp_m & Hexn_m & Hbic_m).
            exists num_m. split; [exact Hexp_m|]. split; [exact Hexn_m|].
            intros nf_args0 Hmatch_nf.
            specialize (Hbic_m _ Hmatch_nf).
            specialize (Hcon_m _ Hmatch_nf).
            specialize (Hcon_h _ Hmatch_nf).
            rewrite Hcon_h, <- Hcon_m. exact Hbic_m. }
      (* Apply soundness clause *)
      specialize (Hsound_can _ Hcan_nf Hmatch).
      cbv [knows_dfact]. apply Exists_exists. exists rs_k. split.
      + apply nth_error_In with k. exact Hnth_s.
      + left. exact Hsound_can.
  Qed.

  Lemma comp_step_sound inputs s s' :
    good_input_facts inputs ->
    sane_state inputs s ->
    meta_facts_correct s ->
    state_correct inputs s ->
    comp_step s s' ->
    state_correct inputs s'.
  Proof.
    intros Hinp Hsane Hmfc Hsound Hstep f (Hf1 & Hf2).
    invert Hstep.
    - (* learn_fact: waiting -> known at some rule.  Nothing new known. *)
      apply Hsound. split.
      + apply (learn_fact_preserves_has_derived_datalog_fact _ _ _ H); assumption.
      + apply (learn_fact_preserves_mf_consistent_state _ _ _ H); assumption.
    - (* fire_normal_rule: new normal fact F = normal_dfact nf_rel nf_args added to
         waiting at all rules; one rule additionally has F in its sent_facts. *)
      rename H into HstepL.
      set (F := normal_dfact nf_rel nf_args) in *.
      cbv [stepWithLabel] in HstepL.
      destruct HstepL as (l1 & label_fire & x & y & l2 & Hcomb & Hs2_eq & Hstepfire).
      destruct label_fire as (r_fire & k_fire).
      destruct Hstepfire as (Hded & Hno_sent & Hy_eq). subst y.
      assert (Hlen_s : length s = length p.(non_meta_rules))
        by (destruct Hsane as (H0&_); exact H0).
      assert (Hlc : length (combine (non_meta_rules p) (seq 0 (length s))) = length s).
      { rewrite length_combine, length_seq. lia. }
      assert (Hs_eq : s = map snd l1 ++ x :: map snd l2).
      { apply (f_equal (map snd)) in Hcomb.
        rewrite map_combine_snd in Hcomb by assumption.
        rewrite map_app in Hcomb. simpl in Hcomb. exact Hcomb. }
      (* knows_dfact s' g <-> g = F \/ knows_dfact s g *)
      assert (Hkd_iff : forall g,
                 knows_dfact (map (add_waiting_fact F) s2) g <-> g = F \/ knows_dfact s g).
      { intros g. rewrite Hs2_eq, Hs_eq. split.
        - apply knows_dfact_after_step.
        - apply knows_dfact_after_step_bw. }
      (* knows_dfact s' (meta_dfact ...) iff knows_dfact s (meta_dfact ...) since F is normal *)
      assert (Hkd_meta : forall R0 mf_args0 opt num,
                 knows_dfact (map (add_waiting_fact F) s2) (meta_dfact R0 mf_args0 opt num) <->
                 knows_dfact s (meta_dfact R0 mf_args0 opt num)).
      { intros. rewrite Hkd_iff. split; [intros [Heq|Hkd]|tauto].
        - subst F. discriminate.
        - assumption. }
      destruct f as [R args | R mf_args mf_set].
      + (* f = normal_fact R args *)
        simpl in Hf1. apply Hkd_iff in Hf1. destruct Hf1 as [Heq|Hf1].
        * (* args is the newly fired fact's args *)
          subst F. injection Heq as -> ->.
          (* Use the firing rule to derive prog_impl ... (normal_fact nf_rel nf_args) *)
          assert (Hin_r : In r_fire p.(non_meta_rules)).
          { assert (Hin_out : In (r_fire, k_fire, x)
                             (combine (combine (non_meta_rules p) (seq 0 (length s))) s)).
            { rewrite Hcomb. apply in_or_app. right. simpl. auto. }
            apply in_combine_l in Hin_out. apply in_combine_l in Hin_out. exact Hin_out. }
          destruct Hded as (hyps & Hnmri & Hkdf_hyps).
          eapply prog_impl_step.
          -- apply Exists_exists. exists (rule_of r_fire). split.
             ++ unfold rules_of. apply in_or_app. right. apply in_map. exact Hin_r.
             ++ apply simple_rule_impl. exact Hnmri.
          -- (* Forall (prog_impl rules_of (knows_datalog_fact inputs)) hyps *)
             rewrite Forall_forall in Hkdf_hyps |- *. intros h Hin_h.
             specialize (Hkdf_hyps _ Hin_h).
             destruct h as [R' args' | R' mf_args' mf_set'].
             ++ (* normal hyp: lift via helper *)
                apply Hsound. split.
                ** eapply knows_datalog_fact_local_lift_has_derived; try eassumption.
                   rewrite Hs_eq. apply in_or_app. right. apply in_eq.
                ** eapply knows_datalog_fact_local_lift_mf_consistent; try eassumption.
                   rewrite Hs_eq. apply in_or_app. right. apply in_eq.
             ++ (* meta hyp: lift via helper *)
                apply Hsound. split.
                ** eapply knows_datalog_fact_local_lift_has_derived; try eassumption.
                   rewrite Hs_eq. apply in_or_app. right. apply in_eq.
                ** eapply knows_datalog_fact_local_lift_mf_consistent; try eassumption.
                   rewrite Hs_eq. apply in_or_app. right. apply in_eq.
        * (* old normal fact; apply Hsound on s *)
          apply Hsound. simpl. split; [exact Hf1|exact I].
      + (* f = meta_fact R mf_args mf_set.  Lift Hf1 from s' to s via Hkd_meta.
           For Hf2: when R != nf_rel, F = normal_dfact nf_rel ... can't equal
           normal_dfact R nf_args, so knows_dfact unchanged; lift directly.
           When R = nf_rel, the new fact may force mf_set nf_args_fire = true
           even though knows_dfact s (normal nf_rel nf_args_fire) might be false.
           That sub-case is admitted below. *)
        simpl in Hf1, Hf2.
        assert (Hf1_s : has_derived_datalog_fact s (meta_fact R mf_args mf_set)).
        { simpl. destruct (is_input R) eqn:HER.
          - destruct Hf1 as (num & Hk). exists num. apply Hkd_meta in Hk. exact Hk.
          - intros k Hk. specialize (Hf1 k Hk). destruct Hf1 as (num & Hknk).
            exists num. apply Hkd_meta in Hknk. exact Hknk. }
        destruct (classic (R = nf_rel)) as [HReq | HRneq].
        * (* R = nf_rel: Hf2 says mf_set nf_args <-> (nf_args = nf_args_fire) OR
             knows_dfact s (normal nf_rel nf_args).  Lift to mf_consistent_state s f
             succeeds EXCEPT when nf_args_fire matches mf_args AND
             ~knows_dfact s (normal nf_rel nf_args_fire) — case (iii) below.  In
             that sub-case mf_consistent_state s f is genuinely violated and
             Hsound is unusable; the derivation must come from the firing rule. *)
          subst R.
          assert (Hf2_s : mf_consistent_state s (meta_fact nf_rel mf_args mf_set)).
          { simpl. intros nf_args0 Hmatch0. specialize (Hf2 _ Hmatch0).
            destruct (classic (nf_args0 = nf_args)) as [-> | HNe].
            - (* nf_args0 = nf_args (the newly fired fact's args).  Need
                 mf_set nf_args <-> knows_dfact s (normal nf_rel nf_args). *)
              destruct (classic (knows_dfact s (normal_dfact nf_rel nf_args)))
                as [Hk | Hnk].
              + (* case (ii) knows_dfact s = true: Hf2 RHS reduces to true *)
                split; intros _; [exact Hk|].
                rewrite Hf2, Hkd_iff. right. exact Hk.
              + (* case (iii): knows_dfact s = false.  In fact this case is
                   IMPOSSIBLE: has_derived_datalog_fact s f (which holds via
                   Hf1_s, but we don't have it here in the consistent assert)
                   would force a (Some k_fire) meta_dfact in s for (nf_rel,
                   mf_args), and by Hmf_sent it'd be in x.sent_facts, which
                   contradicts the fire_normal_rule precondition Hno_sent.
                   We derive False directly from Hf1_s. *)
                exfalso.
                assert (Hin_r : In r_fire (non_meta_rules p)).
                { assert (Hin_out : In (r_fire, k_fire, x)
                    (combine (combine (non_meta_rules p) (seq 0 (length s))) s)).
                  { rewrite Hcomb. apply in_or_app. right. simpl. auto. }
                  apply in_combine_l in Hin_out.
                  apply in_combine_l in Hin_out. exact Hin_out. }
                assert (Hgood_r : good_non_meta_rule r_fire).
                { rewrite Forall_forall in Hp_input. apply Hp_input. exact Hin_r. }
                assert (HNI : is_input nf_rel = false).
                { eapply can_deduce_implies_not_input; eassumption. }
                assert (Hk_eq : k_fire = length l1).
                { assert (Hlen_seq : length (non_meta_rules p) = length (seq 0 (length s))).
                  { rewrite length_seq. lia. }
                  pose proof Hcomb as Hp0a.
                  apply (f_equal (map fst)) in Hp0a.
                  rewrite map_app in Hp0a. simpl in Hp0a.
                  rewrite map_combine_fst in Hp0a by assumption.
                  apply (f_equal (map snd)) in Hp0a.
                  rewrite map_app in Hp0a. simpl in Hp0a.
                  rewrite map_combine_snd in Hp0a by assumption.
                  pose proof (f_equal (fun ll => nth_error ll (length l1)) Hp0a) as HnE.
                  cbv beta in HnE.
                  rewrite nth_error_app_middle in HnE.
                  rewrite ! length_map in HnE.
                  rewrite Nat.compare_refl in HnE.
                  rewrite nth_error_seq in HnE.
                  assert (E : length l1 <? length s = true).
                  { apply Nat.ltb_lt.
                    rewrite Hs_eq, length_app, ! length_map. simpl. lia. }
                  rewrite E in HnE.
                  injection HnE as ->. lia. }
                cbv [has_derived_datalog_fact] in Hf1_s.
                rewrite HNI in Hf1_s.
                assert (Hk_lt : k_fire < length p.(non_meta_rules)).
                { rewrite Hk_eq. rewrite <- Hlen_s.
                  rewrite Hs_eq, length_app, ! length_map. simpl. lia. }
                specialize (Hf1_s _ Hk_lt). destruct Hf1_s as (num & Hknows).
                pose proof Hsane as (_ & _ & Hmf_sent & _ & _ & _).
                specialize (Hmf_sent _ _ _ _ Hknows).
                cbv [nth_sat] in Hmf_sent.
                assert (Hnth : nth_error s k_fire = Some x).
                { rewrite Hs_eq, Hk_eq.
                  rewrite nth_error_app2 by (rewrite length_map; lia).
                  rewrite length_map, Nat.sub_diag. reflexivity. }
                rewrite Hnth in Hmf_sent.
                destruct Hmf_sent as (_ & Hin_x).
                eapply Hno_sent; [exact Hin_x | exact Hmatch0].
            - (* case (i) nf_args0 != nf_args: lift Hf2 directly *)
              rewrite Hf2, Hkd_iff. split.
              + intros [Heq | Hk]; [|exact Hk].
                subst F. injection Heq as Heq2. contradiction.
              + intros Hk. right. exact Hk. }
          apply Hsound. split; assumption.
        * (* R != nf_rel: knows_dfact unchanged for (normal R _); lift Hf2 *)
          assert (Hf2_s : mf_consistent_state s (meta_fact R mf_args mf_set)).
          { simpl. intros args0 Hmatch. specialize (Hf2 _ Hmatch).
            rewrite Hf2, Hkd_iff. split.
            - intros [Heq | Hk]; [|exact Hk].
              subst F. injection Heq as Heq1 _. contradiction.
            - intros Hk. right. exact Hk. }
          apply Hsound. split; assumption.
    - (* fire_meta_rule: new meta_fact new_fact added to waiting at all rules;
         one rule additionally has new_fact in its sent_facts. *)
      rename H into Hin_mr.
      rename H0 into HstepL.
      pose proof HstepL as HstepL_save.
      cbv [stepWithLabel] in HstepL.
      destruct HstepL as (l1 & label_fire & x & y & l2 & Hcomb & Hs2_eq & Hstepfire).
      destruct label_fire as (r_fire & k_fire).
      destruct Hstepfire as (Hcan & Hknown_h_fire & Hy_eq). subst y.
      set (F := new_fact) in *.
      assert (Hlen_s : length s = length p.(non_meta_rules))
        by (destruct Hsane as (H0&_); exact H0).
      assert (Hlc : length (combine (non_meta_rules p) (seq 0 (length s))) = length s).
      { rewrite length_combine, length_seq. lia. }
      assert (Hs_eq : s = map snd l1 ++ x :: map snd l2).
      { apply (f_equal (map snd)) in Hcomb.
        rewrite map_combine_snd in Hcomb by assumption.
        rewrite map_app in Hcomb. simpl in Hcomb. exact Hcomb. }
      assert (Hkd_iff : forall g,
                 knows_dfact (map (add_waiting_fact F) s2) g <-> g = F \/ knows_dfact s g).
      { intros g. rewrite Hs2_eq, Hs_eq. split.
        - apply knows_dfact_after_step.
        - apply knows_dfact_after_step_bw. }
      (* F is a meta_dfact (from can_deduce_meta_fact), so knows_dfact s'
         (normal _ _) = knows_dfact s (normal _ _). *)
      assert (HF_meta : exists mf_rel mf_args mf_cnt,
                 F = meta_dfact mf_rel mf_args (Some k_fire) mf_cnt).
      { cbv [can_deduce_meta_fact] in Hcan.
        destruct Hcan as (ctx & mf_rel & mf_args & mf_cnt & Heq & _).
        exists mf_rel, mf_args, mf_cnt. subst F. exact Heq. }
      assert (Hkd_normal : forall R0 args0,
                 knows_dfact (map (add_waiting_fact F) s2) (normal_dfact R0 args0) <->
                 knows_dfact s (normal_dfact R0 args0)).
      { intros. rewrite Hkd_iff. split; [intros [Heq|Hkd]|tauto].
        - destruct HF_meta as (? & ? & ? & ->). discriminate.
        - assumption. }
      destruct f as [R args | R mf_args mf_set].
      + (* f = normal_fact R args: new fact is meta, so Hf1 lifts directly *)
        simpl in Hf1. apply Hkd_normal in Hf1.
        apply Hsound. simpl. split; [exact Hf1|exact I].
      + (* f = meta_fact R mf_args mf_set *)
        simpl in Hf1, Hf2.
        assert (Hf2_s : mf_consistent_state s (meta_fact R mf_args mf_set)).
        { simpl. intros args0 Hmatch. specialize (Hf2 _ Hmatch).
          rewrite Hf2. exact (Hkd_normal R args0). }
        destruct (is_input R) eqn:HER.
        * (* is_input R: F = meta_dfact ... (Some k_fire) can't equal (None _).
             Lift Hf1 and apply Hsound. *)
          destruct Hf1 as (num & Hk).
          rewrite Hkd_iff in Hk.
          destruct Hk as [Heq | Hk_s].
          -- destruct HF_meta as (? & ? & ? & HFeq). rewrite HFeq in Heq. discriminate.
          -- apply Hsound. simpl. split; [|exact Hf2_s].
             simpl. rewrite HER. exists num. exact Hk_s.
        * (* not is_input R.  Case-split on whether F matches the target meta-fact:
             - Case B (F doesn't match): F = meta_dfact mf_rel0 mf_args0 ..., and
               (R, mf_args) != (mf_rel0, mf_args0), so for every k the new fact
               doesn't match meta_dfact R mf_args (Some k) num.  Hf1 lifts to s.
             - Case A (F matches): R = mf_rel0 and mf_args = mf_args0.  Then F is
               the witness for k = k_fire, and s may have no other witness.
               Requires deriving prog_impl ... f via the firing meta-rule. *)
          destruct HF_meta as (mf_rel0 & mf_args0 & mf_cnt0 & HFeq).
          destruct (classic (R = mf_rel0 /\ mf_args = mf_args0)) as [[HReq HMeq] | HNeq].
          -- (* Case A: R = mf_rel0, mf_args = mf_args0.  Further split on whether
                s has a pre-existing witness for k = k_fire:
                  A.1: lift Hf1 to s entirely, apply Hsound.
                  A.2: F is the only witness, must derive via meta_rule_impl
                       + bridge (~100 lines, needs use_meta_facts_correct analog). *)
             subst R mf_args.
             destruct (classic (exists num0,
                          knows_dfact s (meta_dfact mf_rel0 mf_args0 (Some k_fire) num0)))
                as [HA1 | HA2].
             { (* A.1: lift Hf1 to s for all k *)
               assert (Hf1_s : has_derived_datalog_fact s
                                 (meta_fact mf_rel0 mf_args0 mf_set)).
               { simpl. rewrite HER. intros k Hk.
                 destruct (classic (k = k_fire)) as [-> | Hk_ne]; [exact HA1|].
                 specialize (Hf1 k Hk). destruct Hf1 as (num & Hk_s').
                 rewrite Hkd_iff in Hk_s'.
                 destruct Hk_s' as [Heq | Hk_s]; [|exists num; exact Hk_s].
                 exfalso. rewrite HFeq in Heq.
                 injection Heq as Heq_k _. apply Hk_ne. assumption. }
               apply Hsound. split; assumption. }
             (* A.2 below: no pre-existing witness *)
             cbv [can_deduce_meta_fact] in Hcan.
             destruct Hcan as (ctx & mf_rel_c & mf_args_c & mf_cnt_c
                              & Heq_F & Hexn_F & Hexists_concl & Hf2_h & Hsound_can).
             pose proof Hknown_h_fire as Hkdf_h.
             rewrite HFeq in Heq_F. injection Heq_F as Hr_eq Ha_eq Hc_eq.
             subst mf_rel_c mf_args_c mf_cnt_c.
             pose (S_constr := fun args'' => one_step_derives rules_of hyps mf_rel0 args'').
             assert (Hprog_constr :
                       prog_impl rules_of (knows_datalog_fact inputs)
                         (meta_fact mf_rel0 mf_args0 S_constr)).
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
                   * intros args'' Hmatch_args''. subst S_constr. reflexivity.
               - rewrite Forall_forall in Hkdf_h |- *. intros h Hin_h.
                 specialize (Hkdf_h _ Hin_h).
                 apply Hsound. split.
                 + eapply knows_datalog_fact_local_lift_has_derived; try eassumption.
                   rewrite Hs_eq. apply in_or_app. right. apply in_eq.
                 + eapply knows_datalog_fact_local_lift_mf_consistent; try eassumption.
                   rewrite Hs_eq. apply in_or_app. right. apply in_eq. }
             eapply prog_impl_mf_ext'; [exact Hprog_constr | | ].
             ++ (* iff: S_constr nf_args <-> mf_set nf_args, via use_meta_facts_correct *)
                intros nf_args1 Hmatch1.
                (* Direction setup: use Hhonest to convert S_constr to prog_impl_normal *)
                pose proof Hsane as Hsane'.
                assert (Hstep_comp : comp_step s (map (add_waiting_fact F) s2)).
                { subst F. econstructor; eassumption. }
                assert (Hsane_s' : sane_state inputs (map (add_waiting_fact F) s2)).
                { eapply step_preserves_sane; eassumption. }
                assert (Hmfc_s' : meta_facts_correct (map (add_waiting_fact F) s2)).
                { eapply step_preserves_mfs_correct; [exact Hinp|exact Hsane|exact Hmfc|exact Hstep_comp]. }
                (* HRs for use_meta_facts_correct: state_correct restricted to s'-side *)
                assert (HRs_umfc :
                  forall mf_rel' mf_args' mf_set',
                    (mf_rel0, mf_args0) <> (mf_rel', mf_args') ->
                    has_derived_datalog_fact (map (add_waiting_fact F) s2)
                      (meta_fact mf_rel' mf_args' mf_set') /\
                    mf_consistent_state (map (add_waiting_fact F) s2)
                      (meta_fact mf_rel' mf_args' mf_set') ->
                    prog_impl rules_of (knows_datalog_fact inputs)
                      (meta_fact mf_rel' mf_args' mf_set')).
                { intros mfr' mfa' mfs' Hne (Hhd' & Hmc').
                  (* Lift Hhd' and Hmc' from s' to s *)
                  apply Hsound. split.
                  - (* has_derived_datalog_fact s (meta_fact mfr' mfa' mfs') *)
                    simpl. destruct (is_input mfr') eqn:HERmfr'.
                    + simpl in Hhd'. rewrite HERmfr' in Hhd'.
                      destruct Hhd' as (num & Hk). exists num.
                      rewrite Hkd_iff in Hk. destruct Hk as [Heq | Hk_s]; [|exact Hk_s].
                      exfalso. rewrite HFeq in Heq. discriminate.
                    + simpl in Hhd'. rewrite HERmfr' in Hhd'.
                      intros k Hk. specialize (Hhd' k Hk).
                      destruct Hhd' as (num & Hknk).
                      rewrite Hkd_iff in Hknk.
                      destruct Hknk as [Heq | Hk_s]; [|exists num; exact Hk_s].
                      rewrite HFeq in Heq. injection Heq as -> -> _ _.
                      exfalso. apply Hne. reflexivity.
                  - (* mf_consistent_state s f' *)
                    simpl. intros nf_args2 Hmatch2.
                    simpl in Hmc'. specialize (Hmc' _ Hmatch2).
                    rewrite Hmc'. apply Hkd_normal. }
                assert (Hf1_True : has_derived_datalog_fact (map (add_waiting_fact F) s2)
                                     (meta_fact mf_rel0 mf_args0 (fun _ => True))).
                { simpl. rewrite HER. exact Hf1. }
                pose proof (use_meta_facts_correct mf_rel0 mf_args0 inputs
                              (map (add_waiting_fact F) s2)
                              Hinp Hsane_s' Hmfc_s' HER HRs_umfc
                              Hf1_True nf_args1 Hmatch1) as Humfc.
                assert (Hlen_pos_p : 0 < length p.(non_meta_rules)).
                { rewrite <- Hlen_s, Hs_eq, length_app, ! length_map. simpl. lia. }
                assert (Hgood_inputs_Q : good_inputs rules_of (knows_datalog_fact inputs))
                  by (apply good_inputs_knows_datalog_fact_inputs; assumption).
                pose proof (valid_impl_honest _ Hmeta_rules _ Hgood_inputs_Q) as Hhonest.
                cbv [doesnt_lie] in Hhonest.
                (* Humfc : prog_impl ... (normal_fact mf_rel0 nf_args1) ->
                           knows_dfact s' (normal_dfact mf_rel0 nf_args1) *)
                pose proof (Hhonest _ _ _ Hprog_constr) as Hcon_constr.
                cbv [consistent] in Hcon_constr.
                specialize (Hcon_constr _ Hmatch1).
                rewrite Hcon_constr.
                (* Goal: prog_impl ... (normal_fact mf_rel0 nf_args1) <-> mf_set nf_args1 *)
                split.
                ** (* prog_impl -> mf_set *)
                   intros Hprog. apply Humfc in Hprog.
                   apply (proj2 (Hf2 _ Hmatch1)). exact Hprog.
                ** (* mf_set -> prog_impl *)
                   intros Hms.
                   apply (proj1 (Hf2 _ Hmatch1)) in Hms.
                   apply Hkd_normal in Hms.
                   apply Hsound. simpl. split; [exact Hms|exact I].
             ++ (* ~Q (meta_fact mf_rel0 mf_args0 S_constr): inputs has no
                   (Some k) meta-facts (by good_input_facts), so expect_num_R_facts
                   fails for non-input mf_rel0. *)
                intros HQ. simpl in HQ. destruct HQ as (num & Hexp & _ & _).
                cbv [expect_num_R_facts] in Hexp. rewrite HER in Hexp.
                destruct Hexp as (msgss & Hf2_msgs & _).
                pose proof (Forall2_length Hf2_msgs) as Hlen_msgs.
                rewrite length_seq in Hlen_msgs.
                assert (Hlen_pos : 0 < length p.(non_meta_rules)).
                { rewrite <- Hlen_s. rewrite Hs_eq, length_app. simpl. lia. }
                assert (H0_seq : nth_error (seq 0 (length p.(non_meta_rules))) 0 = Some 0).
                { rewrite nth_error_seq.
                  assert (E : 0 <? length p.(non_meta_rules) = true)
                    by (apply Nat.ltb_lt; exact Hlen_pos).
                  rewrite E. reflexivity. }
                assert (H0_msg : exists m, nth_error msgss 0 = Some m).
                { destruct (nth_error msgss 0) eqn:E; [eauto|].
                  apply nth_error_None in E. lia. }
                destruct H0_msg as (m & H0m).
                pose proof (Forall2_nth_error_fwd _ _ _ Hf2_msgs 0 0 m H0_seq H0m)
                  as Hin_m.
                destruct Hinp as (Hinp_all & _). rewrite Forall_forall in Hinp_all.
                specialize (Hinp_all _ Hin_m). simpl in Hinp_all. congruence.
          -- (* Case B: lift Hf1 to s entirely *)
             assert (Hf1_s : has_derived_datalog_fact s (meta_fact R mf_args mf_set)).
             { simpl. rewrite HER. intros k Hk. specialize (Hf1 k Hk).
               destruct Hf1 as (num & Hk_s'). rewrite Hkd_iff in Hk_s'.
               destruct Hk_s' as [Heq | Hk_s]; [|exists num; exact Hk_s].
               exfalso. rewrite HFeq in Heq. injection Heq as -> -> _ _.
               apply HNeq. split; reflexivity. }
             apply Hsound. split; assumption.
  Qed.

  (* ===== Monotonicity helpers for completeness ===== *)

  Lemma afw_known F rs :
    (add_waiting_fact F rs).(known_facts) = rs.(known_facts).
  Proof. cbv [add_waiting_fact]. simpl. reflexivity. Qed.

  Lemma send_fact_known F rs :
    (send_fact F rs).(known_facts) = rs.(known_facts).
  Proof. cbv [send_fact]. simpl. reflexivity. Qed.

  Lemma comp_step_known_facts_incl inputs s s' :
    sane_state inputs s ->
    comp_step s s' ->
    Forall2 (fun rs rs' => incl rs.(known_facts) rs'.(known_facts)) s s'.
  Proof.
    intros Hsane Hstep.
    destruct Hsane as (Hlen & _).
    invert Hstep.
    - (* learn_fact *)
      cbv [stepOne] in H. fwd.
      cbv [learn_fact_at_rule] in Hp2.
      destruct Hp2 as (lw1 & wf & lw2 & Hykn & Hxwait & Hywait & Hysent).
      apply Forall2_app; [|constructor].
      + clear. induction l1; constructor; auto. apply incl_refl.
      + rewrite Hykn. apply incl_tl. apply incl_refl.
      + clear. induction l2; constructor; auto. apply incl_refl.
    - (* fire_normal_rule *)
      cbv [stepWithLabel] in H. fwd. destruct n as [r k].
      destruct Hp2 as (_ & _ & Hys). subst y.
      assert (Hlc : length (combine (non_meta_rules p) (seq 0 (length s))) = length s).
      { rewrite length_combine, length_seq. lia. }
      assert (Hs_eq : s = map snd l1 ++ x :: map snd l2).
      { apply (f_equal (map snd)) in Hp0.
        rewrite map_combine_snd in Hp0 by assumption.
        rewrite map_app in Hp0. simpl in Hp0. exact Hp0. }
      rewrite Hs_eq. rewrite map_app. simpl.
      apply Forall2_app; [|constructor].
      + clear. induction (map snd l1); constructor; auto.
        rewrite afw_known. apply incl_refl.
      + rewrite afw_known, send_fact_known. apply incl_refl.
      + clear. induction (map snd l2); constructor; auto.
        rewrite afw_known. apply incl_refl.
    - (* fire_meta_rule *)
      cbv [stepWithLabel] in H0. fwd. destruct n as [r k].
      destruct H0p2 as (_ & _ & Hys). subst y.
      assert (Hlc : length (combine (non_meta_rules p) (seq 0 (length s))) = length s).
      { rewrite length_combine, length_seq. lia. }
      assert (Hs_eq : s = map snd l1 ++ x :: map snd l2).
      { apply (f_equal (map snd)) in H0p0.
        rewrite map_combine_snd in H0p0 by assumption.
        rewrite map_app in H0p0. simpl in H0p0. exact H0p0. }
      rewrite Hs_eq. rewrite map_app. simpl.
      apply Forall2_app; [|constructor].
      + clear. induction (map snd l1); constructor; auto.
        rewrite afw_known. apply incl_refl.
      + rewrite afw_known, send_fact_known. apply incl_refl.
      + clear. induction (map snd l2); constructor; auto.
        rewrite afw_known. apply incl_refl.
  Qed.

  Lemma comp_steps_known_facts_incl inputs s s' :
    good_input_facts inputs ->
    sane_state inputs s ->
    comp_step^* s s' ->
    Forall2 (fun rs rs' => incl rs.(known_facts) rs'.(known_facts)) s s'.
  Proof.
    intros Hinp Hsane Hsteps. revert Hsane. induction Hsteps; intros Hsane.
    - clear. induction x; constructor; auto. apply incl_refl.
    - assert (Hsane_y : sane_state inputs y) by eauto using step_preserves_sane.
      specialize (IHHsteps Hsane_y).
      pose proof (comp_step_known_facts_incl _ _ _ Hsane H) as Hstep_incl.
      clear -Hstep_incl IHHsteps.
      revert z IHHsteps. induction Hstep_incl; intros z Hyz.
      + inversion Hyz; subst. constructor.
      + inversion Hyz; subst. constructor.
        * eapply incl_tran; eassumption.
        * apply IHHstep_incl. assumption.
  Qed.

  Lemma comp_step_preserves_known_at s s' j rs :
    Forall2 (fun rs0 rs0' => incl rs0.(known_facts) rs0'.(known_facts)) s s' ->
    nth_error s j = Some rs ->
    exists rs', nth_error s' j = Some rs' /\ incl rs.(known_facts) rs'.(known_facts).
  Proof.
    intros HF2 Hnth. revert j rs Hnth.
    induction HF2; intros j rs Hnth.
    - destruct j; discriminate.
    - destruct j; simpl in *.
      + injection Hnth as <-. eauto.
      + apply IHHF2. assumption.
  Qed.

  Lemma step_preserves_knows_dfact_with_sane inputs s s' f :
    sane_state inputs s ->
    comp_step s s' -> knows_dfact s f -> knows_dfact s' f.
  Proof.
    intros Hsane Hstep Hk. destruct Hsane as (Hlen & _).
    invert Hstep.
    - apply (proj1 (learn_fact_preserves_knows_dfact _ _ _ H)). exact Hk.
    - cbv [stepWithLabel] in H. fwd. destruct n as [r k].
      destruct Hp2 as (_ & _ & Hys). subst y.
      assert (Hlc : length (combine (non_meta_rules p) (seq 0 (length s))) = length s).
      { rewrite length_combine, length_seq. lia. }
      assert (Hs_eq : s = map snd l1 ++ x :: map snd l2).
      { apply (f_equal (map snd)) in Hp0.
        rewrite map_combine_snd in Hp0 by assumption.
        rewrite map_app in Hp0. simpl in Hp0. exact Hp0. }
      rewrite Hs_eq in Hk.
      apply knows_dfact_after_step_bw. right. exact Hk.
    - cbv [stepWithLabel] in H0. fwd. destruct n as [r k].
      destruct H0p2 as (_ & _ & Hys). subst y.
      assert (Hlc : length (combine (non_meta_rules p) (seq 0 (length s))) = length s).
      { rewrite length_combine, length_seq. lia. }
      assert (Hs_eq : s = map snd l1 ++ x :: map snd l2).
      { apply (f_equal (map snd)) in H0p0.
        rewrite map_combine_snd in H0p0 by assumption.
        rewrite map_app in H0p0. simpl in H0p0. exact H0p0. }
      rewrite Hs_eq in Hk.
      apply knows_dfact_after_step_bw. right. exact Hk.
  Qed.

  Lemma steps_preserves_knows_dfact inputs s s' f :
    good_input_facts inputs ->
    sane_state inputs s ->
    comp_step^* s s' -> knows_dfact s f -> knows_dfact s' f.
  Proof.
    intros Hinp Hsane Hsteps. revert Hsane.
    induction Hsteps; intros Hsane Hk; [exact Hk|].
    apply IHHsteps.
    - eapply step_preserves_sane; eassumption.
    - eapply step_preserves_knows_dfact_with_sane; eassumption.
  Qed.

  Lemma step_preserves_has_derived inputs s s' f :
    sane_state inputs s ->
    comp_step s s' ->
    has_derived_datalog_fact s f -> has_derived_datalog_fact s' f.
  Proof.
    intros Hsane Hstep Hd. cbv [has_derived_datalog_fact] in *.
    destruct f as [R args | R mf_args mf_set].
    - eapply step_preserves_knows_dfact_with_sane; eassumption.
    - destruct (is_input R).
      + destruct Hd as (num & Hk). exists num.
        eapply step_preserves_knows_dfact_with_sane; eassumption.
      + intros k Hk_lt. specialize (Hd k Hk_lt). destruct Hd as (num & Hk).
        exists num. eapply step_preserves_knows_dfact_with_sane; eassumption.
  Qed.

  Lemma steps_preserves_has_derived inputs s s' f :
    good_input_facts inputs ->
    sane_state inputs s ->
    comp_step^* s s' ->
    has_derived_datalog_fact s f -> has_derived_datalog_fact s' f.
  Proof.
    intros Hinp Hsane Hsteps. revert Hsane.
    induction Hsteps; intros Hsane Hd; [exact Hd|].
    apply IHHsteps.
    - eapply step_preserves_sane; eassumption.
    - eapply step_preserves_has_derived; eassumption.
  Qed.

  Lemma steps_preserves_length inputs s s' :
    good_input_facts inputs ->
    sane_state inputs s ->
    comp_step^* s s' ->
    length s = length s'.
  Proof.
    intros Hinp Hsane Hsteps.
    pose proof (comp_steps_known_facts_incl _ _ _ Hinp Hsane Hsteps) as HF2.
    apply Forall2_length in HF2. exact HF2.
  Qed.

  (* ===== Single-step path from waiting to known ===== *)

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

  Lemma learn_fact_path inputs s k f :
    sane_state inputs s ->
    knows_dfact s f ->
    k < length s ->
    exists s' rs',
      comp_step^* s s' /\
        nth_error s' k = Some rs' /\
        In f rs'.(known_facts) /\
        (forall g, knows_dfact s' g <-> knows_dfact s g).
  Proof.
    intros Hsane Hk Hlt.
    pose proof Hsane as Hsane'.
    destruct Hsane as (_ & _ & _ & Heverywhere & _ & _ & _).
    specialize (Heverywhere _ Hk).
    rewrite Forall_forall in Heverywhere.
    (* Get rs at position k *)
    destruct (nth_error s k) as [rs|] eqn:Hnth; [|apply nth_error_None in Hnth; lia].
    pose proof Hnth as Hnth_save.
    apply nth_error_split in Hnth.
    destruct Hnth as (l1 & l2 & Hs_eq & Hl1).
    pose proof (Heverywhere rs) as Hrhd.
    specialize' Hrhd. { rewrite Hs_eq. apply in_or_app. right. left. reflexivity. }
    cbv [rule_has_dfact] in Hrhd.
    destruct Hrhd as [Hin_k | Hin_w].
    - (* f already in rs.known: 0 steps *)
      exists s, rs. ssplit; [apply rt1n_refl | exact Hnth_save | exact Hin_k |].
      intros g. reflexivity.
    - (* f in rs.waiting: 1 learn_fact step *)
      apply in_split in Hin_w. destruct Hin_w as (lw1 & lw2 & Hwait_eq).
      pose (rs' := {| known_facts := f :: rs.(known_facts);
                      waiting_facts := lw1 ++ lw2;
                      sent_facts := rs.(sent_facts) |}).
      assert (Hstep_one : stepOne learn_fact_at_rule s (l1 ++ rs' :: l2)).
      { cbv [stepOne]. exists l1, rs, rs', l2. ssplit; auto.
        cbv [learn_fact_at_rule]. exists lw1, f, lw2. ssplit; auto. }
      exists (l1 ++ rs' :: l2), rs'.
      ssplit.
      + eapply Relation_Operators.rt1n_trans; [|apply rt1n_refl].
        apply learn_fact. exact Hstep_one.
      + rewrite nth_error_app2 by lia.
        rewrite Hl1, Nat.sub_diag. reflexivity.
      + simpl. left. reflexivity.
      + intros g. symmetry. apply learn_fact_preserves_knows_dfact. exact Hstep_one.
  Qed.

  Lemma steps_preserves_known_at inputs s s' j rs :
    good_input_facts inputs ->
    sane_state inputs s ->
    comp_step^* s s' ->
    nth_error s j = Some rs ->
    exists rs', nth_error s' j = Some rs' /\ incl rs.(known_facts) rs'.(known_facts).
  Proof.
    intros Hinp Hsane Hsteps Hnth.
    pose proof (comp_steps_known_facts_incl _ _ _ Hinp Hsane Hsteps) as HF2.
    eapply comp_step_preserves_known_at; eassumption.
  Qed.

  Lemma flush_waiting_to_known inputs s k hyps :
    good_input_facts inputs ->
    sane_state inputs s ->
    Forall (knows_dfact s) hyps ->
    k < length s ->
    exists s' rs',
      comp_step^* s s' /\
        nth_error s' k = Some rs' /\
        Forall (fun h => In h rs'.(known_facts)) hyps /\
        (forall g, knows_dfact s' g <-> knows_dfact s g).
  Proof.
    intros Hinp Hsane Hkn Hk.
    induction Hkn as [|h hs Hh Hhs IH].
    - destruct (nth_error s k) as [rs|] eqn:Hnth; [|apply nth_error_None in Hnth; lia].
      exists s, rs. ssplit; [apply rt1n_refl | exact Hnth | constructor |].
      intros g. reflexivity.
    - destruct IH as (s' & rs_k & Hsteps & Hnth_k & Hin_hs & Hiff_s').
      assert (Hsane' : sane_state inputs s') by eauto using steps_preserves_sane.
      assert (Hk' : k < length s').
      { erewrite <- steps_preserves_length; eassumption. }
      assert (Hh' : knows_dfact s' h).
      { rewrite Hiff_s'. exact Hh. }
      pose proof (learn_fact_path inputs s' k h Hsane' Hh' Hk') as Hpath.
      destruct Hpath as (s'' & rs_k'' & Hsteps' & Hnth_k'' & Hin_h & Hiff_s'').
      exists s'', rs_k''. ssplit.
      + eapply crt1n_trans_compose; eassumption.
      + exact Hnth_k''.
      + constructor; [exact Hin_h|].
        pose proof (steps_preserves_known_at _ _ _ _ _ Hinp Hsane' Hsteps' Hnth_k) as Hincl.
        destruct Hincl as (rs_k_incl & Hnth_eq & Hincl).
        rewrite Hnth_eq in Hnth_k''. injection Hnth_k'' as ->.
        eapply Forall_impl; [|exact Hin_hs].
        cbv beta. intros h0 Hin_h0. apply Hincl. exact Hin_h0.
      + intros g. rewrite Hiff_s'', Hiff_s'. reflexivity.
  Qed.

  Lemma comp_steps_sound inputs s s' :
    good_input_facts inputs ->
    sane_state inputs s ->
    meta_facts_correct s ->
    state_correct inputs s ->
    comp_step^* s s' ->
    state_correct inputs s'.
  Proof.
    intros Hinp Hsane Hmfc Hsound Hsteps. revert Hsane Hmfc Hsound.
    induction Hsteps; intros; auto.
    apply IHHsteps.
    - eapply step_preserves_sane; eassumption.
    - eapply step_preserves_mfs_correct; eassumption.
    - eapply comp_step_sound; eassumption.
  Qed.

  Lemma compose_completion inputs s hyps :
    good_input_facts inputs ->
    sane_state inputs s ->
    meta_facts_correct s ->
    state_correct inputs s ->
    Forall (fun h =>
      forall s0,
        sane_state inputs s0 ->
        meta_facts_correct s0 ->
        state_correct inputs s0 ->
        exists s', comp_step^* s0 s' /\ has_derived_datalog_fact s' h) hyps ->
    exists s',
      comp_step^* s s' /\
      Forall (has_derived_datalog_fact s') hyps.
  Proof.
    intros Hinp Hsane Hmfc Hsound HF.
    revert s Hsane Hmfc Hsound.
    induction HF as [|h hs Hh Hhs IH]; intros s Hsane Hmfc Hsound.
    - exists s. split; [apply rt1n_refl|]. constructor.
    - specialize (IH s Hsane Hmfc Hsound).
      destruct IH as (s_mid & Hsteps_mid & Hderived_hs).
      assert (Hsane_mid : sane_state inputs s_mid) by eauto using steps_preserves_sane.
      assert (Hmfc_mid : meta_facts_correct s_mid) by eauto using steps_preserves_mfs_correct.
      assert (Hsound_mid : state_correct inputs s_mid) by eauto using comp_steps_sound.
      destruct (Hh s_mid Hsane_mid Hmfc_mid Hsound_mid) as (s' & Hsteps' & Hh_derived).
      exists s'. ssplit.
      + eapply crt1n_trans_compose; eassumption.
      + constructor; [exact Hh_derived|].
        eapply Forall_impl; [|exact Hderived_hs].
        cbv beta. intros h0. eapply steps_preserves_has_derived; eauto.
  Qed.

  (* Lift a knows_datalog_fact inputs claim into a has_derived_datalog_fact claim
     in any state s satisfying our standard conditions. This is the analog of
     SimpleDataflow's fact_in_inputs_knows_datalog_fact, made direct here by the
     new "inputs propagated" conjunct of sane_state. *)
  Lemma knows_datalog_fact_inputs_has_derived inputs s f :
    good_input_facts inputs ->
    sane_state inputs s ->
    knows_datalog_fact inputs f ->
    has_derived_datalog_fact s f.
  Proof.
    intros Hinp Hsane Hkdf.
    pose proof Hsane as Hsane'.
    destruct Hsane as (_ & _ & _ & _ & _ & _ & Hinp_prop).
    destruct f as [R args | R mf_args mf_set]; cbv [has_derived_datalog_fact] in *.
    - (* normal_fact *)
      apply Hinp_prop. exact Hkdf.
    - (* meta_fact *)
      simpl in Hkdf. destruct Hkdf as (num & Hexp & _ & _).
      cbv [expect_num_R_facts] in Hexp.
      destruct (is_input R) eqn:HER.
      + exists num. apply Hinp_prop. exact Hexp.
      + intros k Hk.
        destruct Hexp as (msgss & Hf2 & Hnum_eq).
        pose proof (Forall2_length Hf2) as Hlen_eq.
        rewrite length_seq in Hlen_eq.
        assert (Hk_seq : nth_error (seq 0 (length p.(non_meta_rules))) k = Some k).
        { rewrite nth_error_seq.
          assert (E : k <? length p.(non_meta_rules) = true) by (apply Nat.ltb_lt; lia).
          rewrite E. reflexivity. }
        assert (Hk_msgs : exists m, nth_error msgss k = Some m).
        { destruct (nth_error msgss k) eqn:Em; [eauto|].
          apply nth_error_None in Em. lia. }
        destruct Hk_msgs as (mk & Hmk).
        pose proof (Forall2_nth_error_fwd _ _ _ Hf2 k k mk Hk_seq Hmk) as Hin_mk.
        exists mk. apply Hinp_prop. exact Hin_mk.
  Qed.

  (* Extract a list of per-source meta_dfacts from has_derived's forall-exists form.
     Each (Some k_src) meta_dfact has its own count num_k; we collect them into a list. *)
  Lemma extract_per_source_meta_dfacts s mf_rel mf_args n :
    (forall k_src, k_src < n -> exists num, knows_dfact s (meta_dfact mf_rel mf_args (Some k_src) num)) ->
    exists nums : list nat,
      length nums = n /\
      Forall2 (fun k_src num => knows_dfact s (meta_dfact mf_rel mf_args (Some k_src) num))
              (seq 0 n) nums.
  Proof.
    induction n; intros H.
    - exists []. split; [reflexivity|]. constructor.
    - specialize (IHn ltac:(intros k_src Hk; apply H; lia)) as (nums & Hlen & HF2).
      destruct (H n ltac:(lia)) as (num & Hnum).
      exists (nums ++ [num]). split.
      + rewrite length_app. simpl. lia.
      + rewrite seq_S.
        apply Forall2_app; [exact HF2|].
        constructor; [exact Hnum|constructor].
  Qed.

  (* Analog of SimpleDataflow's node_can_receive_meta_facts: given that the
     meta-fact count info for (mf_rel, mf_args) is knowable in s (input case:
     a single meta_dfact with None source; non-input case: per-source counts),
     reach a state where expect_num_R_facts holds locally at rule k's known.
     Also preserves knows_dfact iff (since the trace is learn_fact only). *)
  Lemma flush_meta_count_for_rule inputs s k mf_rel mf_args :
    good_input_facts inputs ->
    sane_state inputs s ->
    k < length s ->
    (if is_input mf_rel then
       exists num, knows_dfact s (meta_dfact mf_rel mf_args None num)
     else
       forall k_src, k_src < length p.(non_meta_rules) ->
         exists num, knows_dfact s (meta_dfact mf_rel mf_args (Some k_src) num)) ->
    exists s' rs' num,
      comp_step^* s s' /\
        nth_error s' k = Some rs' /\
        expect_num_R_facts mf_rel mf_args rs'.(known_facts) num /\
        (forall g, knows_dfact s' g <-> knows_dfact s g).
  Proof.
    intros Hinp Hsane Hk Hknow.
    destruct (is_input mf_rel) eqn:Hinp_rel.
    - (* Input case: single meta_dfact with None *)
      destruct Hknow as (num & Hknows_m).
      pose proof (flush_waiting_to_known inputs s k
                    [meta_dfact mf_rel mf_args None num]
                    Hinp Hsane
                    ltac:(constructor; [exact Hknows_m|constructor])
                    Hk) as (s' & rs_k & Hsteps & Hnth & Hin_dfs & Hiff).
      exists s', rs_k, num. ssplit; auto.
      + cbv [expect_num_R_facts]. rewrite Hinp_rel.
        apply Forall_cons_iff in Hin_dfs. apply Hin_dfs.
    - (* Non-input case: per-source counts *)
      pose proof (extract_per_source_meta_dfacts s mf_rel mf_args (length p.(non_meta_rules)) Hknow)
        as (nums & Hlen_nums & HF2_nums).
      pose (meta_dfs := map (fun '(k_src, num) => meta_dfact mf_rel mf_args (Some k_src) num)
                            (combine (seq 0 (length p.(non_meta_rules))) nums)).
      assert (Hnth_combine_split : forall {A B} (l1 : list A) (l2 : list B) i a b,
                nth_error (combine l1 l2) i = Some (a, b) ->
                nth_error l1 i = Some a /\ nth_error l2 i = Some b).
      { clear. intros A B l1. induction l1 as [|x xs IH]; intros l2 i a b;
          destruct l2 as [|y ys]; destruct i; simpl; try discriminate.
        - intros [= -> ->]. split; reflexivity.
        - intros H. apply (IH _ _ _ _ H). }
      assert (Hkn_meta_dfs : Forall (knows_dfact s) meta_dfs).
      { unfold meta_dfs.
        apply Forall_forall. intros df Hin.
        apply in_map_iff in Hin. destruct Hin as ((k_src, num) & Heq & Hin_pair). subst df.
        apply In_nth_error in Hin_pair. destruct Hin_pair as (i & Hnth_c).
        destruct (Hnth_combine_split nat nat _ _ _ _ _ Hnth_c) as (Hi_seq & Hi_nums).
        pose proof (Forall2_nth_error_fwd _ _ _ HF2_nums i k_src num Hi_seq Hi_nums)
          as Hknows. exact Hknows. }
      pose proof (flush_waiting_to_known inputs s k meta_dfs Hinp Hsane Hkn_meta_dfs Hk)
        as (s' & rs_k & Hsteps & Hnth & Hin_dfs & Hiff).
      exists s', rs_k, (fold_left Nat.add nums 0). ssplit; auto.
      cbv [expect_num_R_facts]. rewrite Hinp_rel.
      exists nums. split; [|reflexivity].
      apply Forall2_nth_error_bwd; [rewrite length_seq; lia|].
      intros i k_src num Hi_seq Hi_nums.
      rewrite Forall_forall in Hin_dfs.
      apply Hin_dfs.
      unfold meta_dfs. apply in_map_iff.
      exists (k_src, num). split; [reflexivity|].
      apply nth_error_In with (n := i).
      (* combine at position i should give (k_src, num) *)
      assert (Hcomb_nth : nth_error (combine (seq 0 (length p.(non_meta_rules))) nums) i =
                          Some (k_src, num)).
      { (* nth_error_combine inversion (the reverse direction) *)
        clear -Hi_seq Hi_nums.
        revert nums i Hi_seq Hi_nums.
        generalize (seq 0 (length p.(non_meta_rules))) as l1.
        induction l1 as [|a l1' IH]; intros [|b nums'] i Hi_seq Hi_nums;
          destruct i; simpl in *; try discriminate.
        - injection Hi_seq as ->. injection Hi_nums as ->. reflexivity.
        - apply IH; assumption. }
      exact Hcomb_nth.
  Qed.

  (* Drain all matching items from rule k's waiting via repeated learn_fact.
     Preserves knows_dfact iff. *)
  Lemma flush_one_matching_from_waiting inputs s k mf_rel mf_args n rs :
    good_input_facts inputs ->
    sane_state inputs s ->
    k < length s ->
    nth_error s k = Some rs ->
    Existsn (dfact_matches mf_rel mf_args) (S n) rs.(waiting_facts) ->
    exists s' rs',
      comp_step s s' /\
        nth_error s' k = Some rs' /\
        Existsn (dfact_matches mf_rel mf_args) n rs'.(waiting_facts) /\
        (forall g, knows_dfact s' g <-> knows_dfact s g).
  Proof.
    intros Hinp Hsane Hk Hnth Hex.
    apply Existsn_S in Hex.
    destruct Hex as (lw1 & wf & lw2 & Hwait_eq & Hwf_match & Hex_rest).
    apply nth_error_split in Hnth.
    destruct Hnth as (l1 & l2 & Hs_eq & Hl1_len).
    pose (rs' := {| known_facts := wf :: rs.(known_facts);
                    waiting_facts := lw1 ++ lw2;
                    sent_facts := rs.(sent_facts) |}).
    assert (Hstep_one : stepOne learn_fact_at_rule s (l1 ++ rs' :: l2)).
    { cbv [stepOne]. exists l1, rs, rs', l2. ssplit; auto.
      cbv [learn_fact_at_rule]. exists lw1, wf, lw2. ssplit; auto. }
    exists (l1 ++ rs' :: l2), rs'. ssplit.
    - apply learn_fact. exact Hstep_one.
    - rewrite nth_error_app2 by lia.
      rewrite Hl1_len, Nat.sub_diag. reflexivity.
    - unfold rs'. simpl. exact Hex_rest.
    - intros g. symmetry. apply learn_fact_preserves_knows_dfact. exact Hstep_one.
  Qed.

  Lemma flush_all_matching_from_waiting_aux inputs mf_rel mf_args num_wait :
    forall s k,
      good_input_facts inputs ->
      sane_state inputs s ->
      k < length s ->
      (exists rs, nth_error s k = Some rs /\
                  Existsn (dfact_matches mf_rel mf_args) num_wait rs.(waiting_facts)) ->
      exists s' rs',
        comp_step^* s s' /\
          nth_error s' k = Some rs' /\
          Existsn (dfact_matches mf_rel mf_args) 0 rs'.(waiting_facts) /\
          (forall g, knows_dfact s' g <-> knows_dfact s g).
  Proof.
    induction num_wait as [|nw IH]; intros s k Hinp Hsane Hk (rs & Hnth & Hex_w).
    - exists s, rs. ssplit; [apply rt1n_refl|exact Hnth|exact Hex_w|].
      intros g. reflexivity.
    - pose proof (flush_one_matching_from_waiting inputs s k mf_rel mf_args nw rs
                    Hinp Hsane Hk Hnth Hex_w)
        as (s_next & rs_next & Hstep1 & Hnth_next & Hex_w_next & Hiff1).
      assert (Hsane_next : sane_state inputs s_next) by eauto using step_preserves_sane.
      assert (Hk_next : k < length s_next).
      { pose proof (comp_step_known_facts_incl _ _ _ Hsane Hstep1) as HF2.
        apply Forall2_length in HF2. lia. }
      specialize (IH s_next k Hinp Hsane_next Hk_next).
      specialize' IH. { exists rs_next. split; assumption. }
      destruct IH as (s' & rs' & Hsteps' & Hnth' & Hex_0 & Hiff_rest).
      exists s', rs'. ssplit; auto.
      + eapply Relation_Operators.rt1n_trans; eassumption.
      + intros g. rewrite Hiff_rest, Hiff1. reflexivity.
  Qed.

  Lemma flush_all_matching_from_waiting inputs s k mf_rel mf_args :
    good_input_facts inputs ->
    sane_state inputs s ->
    k < length s ->
    exists s' rs',
      comp_step^* s s' /\
        nth_error s' k = Some rs' /\
        Existsn (dfact_matches mf_rel mf_args) 0 rs'.(waiting_facts) /\
        (forall g, knows_dfact s' g <-> knows_dfact s g).
  Proof.
    intros Hinp Hsane Hk.
    pose proof Hsane as (_ & _ & _ & _ & Hcount & _ & _).
    pose proof (Hcount mf_rel mf_args) as (msgs_sents & num_inp & _ & _ & Hcount_rs).
    destruct (nth_error s k) as [rs_k|] eqn:Hnth; [|apply nth_error_None in Hnth; lia].
    rewrite Forall_forall in Hcount_rs.
    pose proof (Hcount_rs rs_k (nth_error_In _ _ Hnth)) as Hex_at_k.
    destruct Hex_at_k as (_ & num_wait & _ & Hex_w & _).
    eapply flush_all_matching_from_waiting_aux; eauto.
  Qed.

  (* If a prog_impl-derivable meta_fact has input rel, it must come from Q-leaf
     (no meta-rule can produce input meta-facts by good_meta_rule_inputs). *)
  Lemma prog_impl_input_meta_implies_Q_leaf_early inputs mf_rel mf_args mf_set :
    is_input mf_rel = true ->
    prog_impl rules_of (knows_datalog_fact inputs) (meta_fact mf_rel mf_args mf_set) ->
    knows_datalog_fact inputs (meta_fact mf_rel mf_args mf_set).
  Proof.
    intros HER Himpl. invert Himpl.
    - (* Q-leaf *) exact H.
    - (* rule-step: contradict via Hp_meta_input *)
      exfalso. apply Exists_exists in H. destruct H as (r & Hin_r & Hri).
      cbv [rules_of] in Hin_r. apply in_app_or in Hin_r.
      destruct Hin_r as [Hin_meta | Hin_nm].
      + apply in_map_iff in Hin_meta. destruct Hin_meta as ((c, h) & Heq & Hin_mr).
        subst r. invert Hri.
        rewrite Forall_forall in Hp_meta_input.
        specialize (Hp_meta_input _ Hin_mr). simpl in Hp_meta_input.
        rewrite Forall_forall in Hp_meta_input.
        match goal with H : Exists _ _ |- _ => apply Exists_exists in H;
                          destruct H as (c0 & Hin_c0 & Hint_c) end.
        cbv [interp_meta_clause] in Hint_c.
        destruct Hint_c as (mfa & mfs & _ & Heq_c).
        injection Heq_c as -> _ _.
        pose proof (Hp_meta_input _ Hin_c0). congruence.
      + apply in_map_iff in Hin_nm. destruct Hin_nm as (nmr & Heq_r & _).
        subst r. destruct nmr; simpl in Hri; inversion Hri.
  Qed.

  (* For a meta_fact h satisfying has_derived + mf_consistent_state at s, flush
     the necessary meta_dfacts and matching normal_dfacts so that
     knows_datalog_fact rs_k.known h holds at the resulting state.
     Generalizes the agg case's per-hyp logic. *)
  Lemma flush_one_meta_hyp inputs s k mf_rel mf_args mf_set :
    good_input_facts inputs ->
    sane_state inputs s ->
    meta_facts_correct s ->
    state_correct inputs s ->
    k < length s ->
    has_derived_datalog_fact s (meta_fact mf_rel mf_args mf_set) ->
    mf_consistent_state s (meta_fact mf_rel mf_args mf_set) ->
    prog_impl rules_of (knows_datalog_fact inputs) (meta_fact mf_rel mf_args mf_set) ->
    0 < length p.(non_meta_rules) ->
    exists s' rs',
      comp_step^* s s' /\
        nth_error s' k = Some rs' /\
        knows_datalog_fact rs'.(known_facts) (meta_fact mf_rel mf_args mf_set) /\
        (forall g, knows_dfact s' g <-> knows_dfact s g).
  Proof.
    intros Hinp Hsane Hmfc Hsound Hk Hd Hc Hpi Hlen_pos.
    pose proof Hsane as Hsane_save.
    (* Extract the meta-count info from has_derived *)
    assert (Hknow_meta_info :
              if is_input mf_rel then
                exists num, knows_dfact s (meta_dfact mf_rel mf_args None num)
              else
                forall k_src, k_src < length p.(non_meta_rules) ->
                  exists num, knows_dfact s (meta_dfact mf_rel mf_args (Some k_src) num)).
    { cbv [has_derived_datalog_fact] in Hd.
      destruct (is_input mf_rel); exact Hd. }
    (* Apply flush_meta_count_for_rule *)
    pose proof (flush_meta_count_for_rule inputs s k mf_rel mf_args Hinp Hsane Hk Hknow_meta_info)
      as (s_int & rs_k_int & num_meta & Hsteps_int & Hnth_int & Hexp_int & Hiff_int).
    assert (Hsane_int : sane_state inputs s_int) by eauto using steps_preserves_sane.
    assert (Hk_int : k < length s_int).
    { erewrite <- steps_preserves_length; eauto. }
    (* Drain matching from rs_k_int.waiting *)
    pose proof (flush_all_matching_from_waiting inputs s_int k mf_rel mf_args
                  Hinp Hsane_int Hk_int)
      as (s' & rs_k & Hsteps_drain & Hnth_k & Hex_w_0 & Hiff_drain).
    assert (Hsane' : sane_state inputs s') by eauto using steps_preserves_sane.
    assert (Hmfc' : meta_facts_correct s') by eauto using steps_preserves_mfs_correct.
    (* Compose traces and iff *)
    assert (Hsteps_total : comp_step^* s s') by (eapply crt1n_trans_compose; eassumption).
    assert (Hsound' : state_correct inputs s') by eauto using comp_steps_sound.
    assert (Hiff_total : forall g, knows_dfact s' g <-> knows_dfact s g).
    { intros g. rewrite Hiff_drain, Hiff_int. reflexivity. }
    (* Get expect_num_R_facts at rs_k's known (via incl from rs_k_int) *)
    pose proof (steps_preserves_known_at _ _ _ _ _ Hinp Hsane_int Hsteps_drain Hnth_int)
      as (rs_k' & Hnth_eq & Hincl).
    rewrite Hnth_eq in Hnth_k. injection Hnth_k as ->.
    exists s', rs_k. ssplit; try assumption.
    cbv [knows_datalog_fact]. exists num_meta. ssplit.
    - (* expect_num_R_facts: extend from rs_k_int via Hincl *)
      cbv [expect_num_R_facts] in *.
      destruct (is_input mf_rel) eqn:Hinp_rel.
      + apply Hincl. exact Hexp_int.
      + destruct Hexp_int as (msgs & Hf2 & Heq).
        exists msgs. split; [|exact Heq].
        eapply Forall2_impl_strong; [|exact Hf2].
        intros n exp Hexp Hn_in Hexp_in.
        apply Hincl. exact Hexp.
    - (* Existsn count = num_meta via Hcount + drain *)
      destruct Hsane' as (_ & Hmf_inp' & Hmf_sent' & _ & Hcount' & Hinp_sane' & _).
      pose proof (Hcount' mf_rel mf_args) as Hcount_R.
      destruct Hcount_R as (msgs_sents & num_inp_actual & Hf2_msgs & Hex_inp_actual & Hforall_kn).
      rewrite Forall_forall in Hforall_kn.
      specialize (Hforall_kn rs_k (nth_error_In _ _ Hnth_eq)).
      destruct Hforall_kn as (num_known & num_wait & Hex_kn & Hex_w & Hsum).
      pose proof (Existsn_unique _ _ _ _ Hex_w Hex_w_0) as Hnw_eq.
      subst num_wait. rewrite Nat.add_0_r in Hsum.
      destruct (is_input mf_rel) eqn:Hinp_rel.
      + (* input case: num_meta = num_inp_actual via Q-leaf + uniqueness *)
        (* sum_sent = 0 for input rel *)
        pose proof (Hinp_sane' mf_rel Hinp_rel) as (Hinp_zero & _).
        specialize (Hinp_zero mf_args).
        assert (Hsum_msgs_zero : fold_left Nat.add msgs_sents 0 = 0).
        { clear -Hinp_zero Hf2_msgs.
          revert msgs_sents Hf2_msgs Hinp_zero.
          induction s' as [|rs s'' IH]; intros [|m ms] Hf2 Hi.
          - reflexivity.
          - inversion Hf2.
          - inversion Hf2.
          - inversion Hf2 as [|? ? ? ? Hex' Hf2_rest]; subst.
            apply Forall_cons_iff in Hi. destruct Hi as (Hrs_zero & Hi_rest).
            pose proof (Existsn_unique _ _ _ _ Hex' Hrs_zero) as Heq. subst m.
            simpl. apply IH; assumption. }
        rewrite Hsum_msgs_zero in Hsum. rewrite Nat.add_0_r in Hsum. subst num_known.
        (* num_inp_actual = num_meta: prog_impl_input_meta_implies_Q_leaf *)
        pose proof (prog_impl_input_meta_implies_Q_leaf_early inputs mf_rel mf_args mf_set
                      Hinp_rel Hpi) as HQ.
        cbv [knows_datalog_fact] in HQ.
        destruct HQ as (num_q & Hexp_q & Hex_q & _).
        cbv [expect_num_R_facts] in Hexp_q. rewrite Hinp_rel in Hexp_q.
        (* From has_derived (input case): knows_dfact s (meta_dfact mf_rel mf_args None num_meta).
           By Hmf_inp at s, In ... inputs. *)
        cbv [has_derived_datalog_fact] in Hd. rewrite Hinp_rel in Hd.
        destruct Hd as (num_d & Hknows_d).
        (* num_d = num_meta (both extracted from same Hknow_meta_info source) *)
        (* But that's not directly evident. Let me use Hmf_inp at s' instead. *)
        (* By Hexp_int we have meta_dfact at rs_k_int.known with num_meta.
           After flush, still in rs_k.known by Hincl. So knows_dfact s' (...) with num_meta. *)
        assert (Hknows_meta_s' : knows_dfact s' (meta_dfact mf_rel mf_args None num_meta)).
        { cbv [knows_dfact]. apply Exists_exists. exists rs_k.
          split; [apply nth_error_In in Hnth_eq; exact Hnth_eq|].
          left.
          cbv [expect_num_R_facts] in Hexp_int. rewrite Hinp_rel in Hexp_int.
          apply Hincl. exact Hexp_int. }
        pose proof (Hmf_inp' _ _ _ Hknows_meta_s') as Hmf_inp_meta.
        (* good_input_facts uniqueness: num_q = num_meta *)
        destruct Hinp as (_ & Hinp_unique).
        pose proof (Hinp_unique mf_rel mf_args num_q Hexp_q) as (Hunq & _).
        specialize (Hunq num_meta Hmf_inp_meta). subst num_q.
        (* Existsn_unique: num_meta = num_inp_actual *)
        pose proof (Existsn_unique _ _ _ _ Hex_q Hex_inp_actual) as Hex_unq.
        subst num_inp_actual. exact Hex_kn.
      + (* non-input case: num_meta = sum_sent *)
        (* num_inp_actual = 0 for non-input rel *)
        assert (Hinp_zero : num_inp_actual = 0).
        { destruct Hinp as (Hinp_all & _). rewrite Forall_forall in Hinp_all.
          clear -Hex_inp_actual Hinp_all Hinp_rel.
          revert num_inp_actual Hex_inp_actual.
          induction inputs as [|f rest IH]; intros num_inp_actual Hex.
          - inversion Hex; reflexivity.
          - inversion Hex as [|? ? ? Hnot Hex_rest|? ? ? Hyes Hex_rest]; subst.
            + apply IH; auto.
              intros f' Hf'. apply Hinp_all. right. exact Hf'.
            + exfalso.
              destruct Hyes as (nf_args & Heq & _). subst f.
              specialize (Hinp_all _ (or_introl eq_refl)).
              simpl in Hinp_all. congruence. }
        subst num_inp_actual. simpl in Hsum.
        (* num_known = sum_sent. Need sum_sent = num_meta. *)
        (* num_meta = fold_left Nat.add nums 0 from flush_meta_count_for_rule's structure.
           We need to extract nums and compare to msgs_sents. *)
        (* Actually flush_meta_count_for_rule's signature has num as existential; in non-input
           case it returns fold_left of internal nums. Let me extract via Hexp_int. *)
        cbv [expect_num_R_facts] in Hexp_int. rewrite Hinp_rel in Hexp_int.
        destruct Hexp_int as (nums_int & HF2_int & Hnum_meta_eq).
        (* HF2_int: Forall2 ... rs_k_int.known each (Some n) nums_int[n].
           Show msgs_sents = nums_int via knows_dfact transitivity. *)
        assert (Hmsgs_eq : Forall2 eq msgs_sents nums_int).
        { eapply Forall2_nth_error_bwd.
          { pose proof (Forall2_length Hf2_msgs) as Hl_ms.
            apply Forall2_length in HF2_int. rewrite length_seq in HF2_int.
            pose proof (steps_preserves_length _ _ _ Hinp Hsane_save Hsteps_total) as Hlen_s'.
            pose proof Hsane_save as (Hlen_s_o & _). lia. }
          intros i ms_i num_i Hi_ms Hi_num.
          (* num_i = In (meta_dfact ... (Some i) num_i) rs_k_int.known via HF2_int *)
          pose proof (Forall2_length HF2_int) as Hlen_int.
          rewrite length_seq in Hlen_int.
          assert (Hi_lt_n : i < length p.(non_meta_rules)).
          { apply nth_error_Some_bound_index in Hi_num. lia. }
          assert (Hi_seq : nth_error (seq 0 (length p.(non_meta_rules))) i = Some i).
          { rewrite nth_error_seq.
            assert (E : i <? length p.(non_meta_rules) = true) by (apply Nat.ltb_lt; lia).
            rewrite E. reflexivity. }
          pose proof (Forall2_nth_error_fwd _ _ _ HF2_int i i num_i Hi_seq Hi_num) as Hin_meta_int.
          (* In meta_dfact ... rs_k_int.known. Lift to s' via Hincl. *)
          apply Hincl in Hin_meta_int.
          (* knows_dfact s' (meta_dfact ... (Some i) num_i) *)
          assert (Hknows_s' : knows_dfact s' (meta_dfact mf_rel mf_args (Some i) num_i)).
          { cbv [knows_dfact]. apply Exists_exists. exists rs_k.
            split; [apply nth_error_In in Hnth_eq; exact Hnth_eq|]. left. exact Hin_meta_int. }
          specialize (Hmf_sent' _ _ _ _ Hknows_s').
          cbv [nth_sat] in Hmf_sent'.
          pose proof (Forall2_length Hf2_msgs) as Hf2_len.
          assert (Hi_s' : exists rs_i, nth_error s' i = Some rs_i).
          { destruct (nth_error s' i) eqn:E; [eauto|].
            apply nth_error_None in E.
            apply nth_error_Some_bound_index in Hi_ms. lia. }
          destruct Hi_s' as (rs_i & Hnth_s'_i).
          rewrite Hnth_s'_i in Hmf_sent'.
          destruct Hmf_sent' as (Hex_num_i & _).
          pose proof (Forall2_nth_error_fwd _ _ _ Hf2_msgs i rs_i ms_i Hnth_s'_i Hi_ms)
            as Hex_ms_i.
          pose proof (Existsn_unique _ _ _ _ Hex_ms_i Hex_num_i) as Heq. exact Heq. }
        assert (Hsents_eq : fold_left Nat.add msgs_sents 0 = fold_left Nat.add nums_int 0).
        { assert (Heq : msgs_sents = nums_int).
          { clear -Hmsgs_eq. induction Hmsgs_eq; subst; reflexivity. }
          subst. reflexivity. }
        rewrite Hsents_eq in Hsum.
        rewrite <- Hnum_meta_eq in Hsum.
        rewrite <- Hsum. exact Hex_kn.
    - (* Bicondition *)
      intros nf_args Hmatch.
      cbv [mf_consistent_state] in Hc. specialize (Hc nf_args Hmatch).
      split.
      + intros HS_set.
        (* S_set → knows_dfact s → knows_dfact s' → In rs_k.known? Hmm not quite *)
        (* We need: matching knows_dfact s for normal_dfact mf_rel nf_args → In rs_k.known *)
        (* From Heverywhere at s' (preserved): knows_dfact s' f → Forall rule_has_dfact rs in s'.
           Then rule_has_dfact rs_k = In rs_k.known ∪ In rs_k.waiting.
           For matching: by Hex_w_0, In rs_k.waiting is False.
           So In rs_k.known. *)
        apply Hc in HS_set.
        rewrite <- Hiff_total in HS_set.
        (* By Heverywhere at s' *)
        destruct Hsane' as (_ & _ & _ & Hev' & _).
        specialize (Hev' _ HS_set).
        rewrite Forall_forall in Hev'.
        pose proof (Hev' _ (nth_error_In _ _ Hnth_eq)) as Hrhd.
        cbv [rule_has_dfact] in Hrhd.
        destruct Hrhd as [Hin_k | Hin_w]; [exact Hin_k|].
        (* In rs_k.waiting: but Hex_w_0 says no matching there *)
        exfalso.
        assert (Hmatch_df : dfact_matches mf_rel mf_args (normal_dfact mf_rel nf_args)).
        { cbv [dfact_matches]. exists nf_args. split; [reflexivity|exact Hmatch]. }
        apply in_split in Hin_w. destruct Hin_w as (lw1 & lw2 & Heq_w).
        rewrite Heq_w in Hex_w_0.
        apply Existsn_split in Hex_w_0.
        destruct Hex_w_0 as (n1 & n2 & Hsum_n & _ & Hex_cons).
        assert (n2 = 0) by lia. subst n2.
        inversion Hex_cons; subst.
        all: try contradiction.
        all: try lia.
      + intros Hin_kn.
        apply Hc.
        rewrite <- Hiff_total.
        cbv [knows_dfact]. apply Exists_exists.
        exists rs_k. split; [apply nth_error_In in Hnth_eq; exact Hnth_eq|].
        left. exact Hin_kn.
  Admitted.

  (* If a prog_impl-derivable meta_fact has input rel, it must come from Q-leaf
     (no meta-rule can produce input meta-facts by good_meta_rule_inputs). *)
  Lemma prog_impl_input_meta_implies_Q_leaf inputs mf_rel mf_args mf_set :
    is_input mf_rel = true ->
    prog_impl rules_of (knows_datalog_fact inputs) (meta_fact mf_rel mf_args mf_set) ->
    knows_datalog_fact inputs (meta_fact mf_rel mf_args mf_set).
  Proof.
    intros HER Himpl. invert Himpl.
    - (* Q-leaf *) exact H.
    - (* rule-step: contradict via Hp_meta_input *)
      exfalso. apply Exists_exists in H. destruct H as (r & Hin_r & Hri).
      cbv [rules_of] in Hin_r. apply in_app_or in Hin_r.
      destruct Hin_r as [Hin_meta | Hin_nm].
      + apply in_map_iff in Hin_meta. destruct Hin_meta as ((c, h) & Heq & Hin_mr).
        subst r. invert Hri.
        rewrite Forall_forall in Hp_meta_input.
        specialize (Hp_meta_input _ Hin_mr). simpl in Hp_meta_input.
        rewrite Forall_forall in Hp_meta_input.
        match goal with H : Exists _ _ |- _ => apply Exists_exists in H;
                          destruct H as (c0 & Hin_c0 & Hint_c) end.
        cbv [interp_meta_clause] in Hint_c.
        destruct Hint_c as (mfa & mfs & _ & Heq_c).
        injection Heq_c as -> _ _.
        pose proof (Hp_meta_input _ Hin_c0). congruence.
      + apply in_map_iff in Hin_nm. destruct Hin_nm as (nmr & Heq_r & _).
        subst r. destruct nmr; simpl in Hri; inversion Hri.
  Qed.

  (* Flush all meta_fact hyps to rule k's known via iterated flush_one_meta_hyp. *)
  Lemma flush_all_meta_hyps inputs s k hyps_facts :
    good_input_facts inputs ->
    sane_state inputs s ->
    meta_facts_correct s ->
    state_correct inputs s ->
    k < length s ->
    0 < length p.(non_meta_rules) ->
    Forall (has_derived_datalog_fact s) hyps_facts ->
    Forall (mf_consistent_state s) hyps_facts ->
    Forall (prog_impl rules_of (knows_datalog_fact inputs)) hyps_facts ->
    Forall (fun h => exists R mf_args mf_set, h = meta_fact R mf_args mf_set) hyps_facts ->
    exists s' rs',
      comp_step^* s s' /\
        nth_error s' k = Some rs' /\
        Forall (knows_datalog_fact rs'.(known_facts)) hyps_facts /\
        (forall g, knows_dfact s' g <-> knows_dfact s g).
  Proof.
    intros Hinp Hsane Hmfc Hsound Hk Hlen_pos Hd Hc Hpi Hshape.
    revert s Hsane Hmfc Hsound Hk Hd Hc Hpi.
    induction hyps_facts as [|h hs IH]; intros s Hsane Hmfc Hsound Hk Hd Hc Hpi.
    - destruct (nth_error s k) as [rs_k|] eqn:Hnth; [|apply nth_error_None in Hnth; lia].
      exists s, rs_k. ssplit.
      + apply rt1n_refl.
      + exact Hnth.
      + constructor.
      + intros g. reflexivity.
    - apply Forall_cons_iff in Hd. destruct Hd as (Hd_h & Hd_hs).
      apply Forall_cons_iff in Hc. destruct Hc as (Hc_h & Hc_hs).
      apply Forall_cons_iff in Hpi. destruct Hpi as (Hpi_h & Hpi_hs).
      apply Forall_cons_iff in Hshape. destruct Hshape as (Hshape_h & Hshape_hs).
      destruct Hshape_h as (R_h & mf_args_h & mf_set_h & ->).
      (* Flush h first *)
      pose proof (flush_one_meta_hyp inputs s k R_h mf_args_h mf_set_h
                    Hinp Hsane Hmfc Hsound Hk Hd_h Hc_h Hpi_h Hlen_pos)
        as (s1 & rs_k1 & Hsteps1 & Hnth_k1 & Hknow_h & Hiff1).
      assert (Hsane1 : sane_state inputs s1) by eauto using steps_preserves_sane.
      assert (Hmfc1 : meta_facts_correct s1) by eauto using steps_preserves_mfs_correct.
      assert (Hsound1 : state_correct inputs s1) by eauto using comp_steps_sound.
      assert (Hk1 : k < length s1).
      { erewrite <- steps_preserves_length; eauto. }
      (* Update Hd_hs, Hc_hs, Hpi_hs to s1 via iff and preservation *)
      assert (Hd_hs_s1 : Forall (has_derived_datalog_fact s1) hs).
      { eapply Forall_impl; [|exact Hd_hs].
        intros h0 Hd0.
        eapply steps_preserves_has_derived;
          [exact Hinp | exact Hsane | exact Hsteps1 | exact Hd0]. }
      assert (Hc_hs_s1 : Forall (mf_consistent_state s1) hs).
      { eapply Forall_impl; [|exact Hc_hs]. intros h0.
        cbv [mf_consistent_state]. destruct h0; auto.
        intros Hbi nf_args Hmatch. rewrite Hiff1. apply Hbi. exact Hmatch. }
      (* Recurse on hs *)
      specialize (IH Hshape_hs s1 Hsane1 Hmfc1 Hsound1 Hk1 Hd_hs_s1 Hc_hs_s1 Hpi_hs).
      destruct IH as (s' & rs_k' & Hsteps' & Hnth_k' & Hknow_hs & Hiff').
      exists s', rs_k'. ssplit; try assumption.
      + eapply crt1n_trans_compose; eassumption.
      + constructor.
        * (* knows_datalog_fact rs_k'.known h — need to extend from rs_k1.known *)
          pose proof (steps_preserves_known_at _ _ _ _ _ Hinp Hsane1 Hsteps' Hnth_k1)
            as (rs_k1' & Hnth_eq & Hincl).
          rewrite Hnth_eq in Hnth_k'. injection Hnth_k' as ->.
          (* Need: knows_datalog_fact rs_k'.known (meta_fact R_h mf_args_h mf_set_h) *)
          (* From knows_datalog_fact rs_k1.known (Hknow_h), lift via Hincl and Hiff. *)
          cbv [knows_datalog_fact] in Hknow_h |- *.
          destruct Hknow_h as (num_h & Hexp_h & Hex_h & Hbi_h).
          exists num_h. ssplit.
          -- (* expect_num_R_facts *)
             cbv [expect_num_R_facts] in *.
             destruct (is_input R_h).
             ++ apply Hincl. exact Hexp_h.
             ++ destruct Hexp_h as (msgs & Hf2 & Heq).
                exists msgs. split; [|exact Heq].
                eapply Forall2_impl_strong; [|exact Hf2].
                intros n exp Hexp_in _ _. apply Hincl. exact Hexp_in.
          -- (* Existsn count: subtle — Existsn = num_h might not be preserved after
                more flushing. The right approach is to re-establish knows_datalog_fact
                for h at the FINAL state (rs_k') using Hcount + drain + preserved
                invariants, rather than lifting from rs_k1. *)
             admit.
          -- (* Bicondition: similarly requires final-state reasoning *)
             admit.
        * (* Forall (knows_datalog_fact rs_k'.known) hs — already from IH *)
          exact Hknow_hs.
      + intros g. rewrite Hiff', Hiff1. reflexivity.
  Admitted.

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
    pose (S0 := fun args' => knows_dfact s (normal_dfact R args')).
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

  (* Per-rule completeness: given a rule r in rules_of, hyps derived in s, and
     mf_consistent_state for meta-fact hyps, we can step to a state where the
     conclusion of r is derived.

     ROADMAP for the three admits below:

     Normal-rule subcase (simple_rule_impl + normal_rule_impl):
       1. From the Forall2 (interp_clause ctx) Hyps, each hyp = normal_fact R' args'.
          Extract list dfs = map (fun (normal_fact R' args') => normal_dfact R' args').
       2. From Hderived: Forall (knows_dfact s) dfs.
       3. Flush via flush_waiting_to_known at index k: get s1 with rs_k.known
          containing all dfs.
       4. Case split on whether rs_k.sent contains a (meta_dfact R mf_args (Some k) num)
          with mf_args matching args:
            (a) If YES: use meta_facts_correct_at_rule + can_deduce_meta_fact's
                forcing clause to conclude (normal_dfact R args) is already in
                rs_k.known. Done with 0 additional steps.
            (b) If NO: apply fire_normal_rule, get s2 = map (afw F) (... send_fact F :: ...).
                The new state has (normal_dfact R args) in every rule's waiting.
                Therefore knows_dfact s2 (normal_dfact R args), i.e., has_derived s2 f.

     Agg-rule subcase (simple_rule_impl + agg_rule_impl):
       Similar to normal-rule but hyps = meta_fact :: list of normal_facts.
       The meta_fact hyp needs flushing of multiple meta_dfacts (one per k).
       Uses mf_consistent_state to establish the aggregation's source set.

     Meta-rule subcase (meta_rule_impl):
       ru = meta_rule mf_concls mf_hyps. Conclusion = meta_fact R args S.
       Pick a source-index k. Flush all interpreted meta-clause hyps into rule k's
       known. Apply fire_meta_rule. The new meta_dfact (Some k) is in rs_k.sent,
       and via the count infrastructure (Hcount) plus the fired num matching,
       has_derived holds at all rules.

     Each subcase also needs the no-self-reference clause for fire_meta_rule, derived
     from meta_facts_correct_at_rule (same pattern as step_preserves_mfs_correct). *)
  Lemma good_layout_complete_rule inputs s (ru : rule) f hyps :
    good_input_facts inputs ->
    sane_state inputs s ->
    meta_facts_correct s ->
    state_correct inputs s ->
    In ru rules_of ->
    rule_impl (one_step_derives rules_of) ru f hyps ->
    Forall (has_derived_datalog_fact s) hyps ->
    Forall (mf_consistent_state s) hyps ->
    exists s',
      comp_step^* s s' /\
        has_derived_datalog_fact s' f.
  Proof.
    intros Hinp Hsane Hmfc Hsound Hin_r Himpl Hderived Hcons.
    invert Himpl.
    - (* simple_rule_impl: ru = non-meta rule, conclusion = normal_fact R args *)
      rename H into Hnmri.
      (* Hnmri : non_meta_rule_impl ru R args hyps *)
      (* Find the corresponding non_meta_rule nmr in p.(non_meta_rules) *)
      assert (Hin_nmr : exists nmr, In nmr p.(non_meta_rules) /\ rule_of nmr = ru).
      { cbv [rules_of] in Hin_r. apply in_app_or in Hin_r.
        destruct Hin_r as [Hin_meta | Hin_nm].
        - exfalso. apply in_map_iff in Hin_meta.
          destruct Hin_meta as ((c, h) & Heq & _). subst ru. invert Hnmri.
        - apply in_map_iff in Hin_nm.
          destruct Hin_nm as (nmr & Heq & Hin_nmr). exists nmr. auto. }
      destruct Hin_nmr as (nmr & Hin_nmr & Hnmr_eq).
      (* Get the index k of nmr *)
      pose proof Hin_nmr as Hin_nmr_save.
      apply In_nth_error in Hin_nmr. destruct Hin_nmr as (k & Hk_nmr).
      apply nth_error_Some_bound_index in Hk_nmr as Hk_lt.
      pose proof Hsane as Hsane_save.
      destruct Hsane as (Hlen_s & _).
      assert (Hk_lt_s : k < length s) by lia.
      (* Case analysis on nmr's constructor *)
      destruct nmr as [rcs rhs | cr ag hr]; simpl in Hnmr_eq; subst ru.
      + (* nmr = nmr_normal rcs rhs, so ru = normal_rule rcs rhs *)
        set (nmr := nmr_normal rcs rhs) in *.
        rename R into R_concl, args into args_concl.
        inversion Hnmri; subst.
        rename ctx into ctx0.
        match goal with
        | H : Exists _ _ |- _ => rename H into Hexists_concl
        end.
        match goal with
        | H : Forall2 _ _ _ |- _ => rename H into Hforall2_hyps
        end.
        (* All hyps : list fact, each of form normal_fact *)
        assert (Hhyps_normal : Forall (fun h => exists R' args', h = normal_fact R' args') hyps).
        { apply Forall_forall. intros f Hin.
          apply In_nth_error in Hin. destruct Hin as (i & Hnth).
          destruct (nth_error rhs i) as [c|] eqn:Hnth_c.
          - pose proof (Forall2_nth_error_fwd _ _ _ Hforall2_hyps _ _ _ Hnth_c Hnth) as Hinterp.
            cbv [interp_clause] in Hinterp. destruct Hinterp as (nf_args & _ & Heq). eauto.
          - exfalso.
            apply nth_error_None in Hnth_c.
            apply nth_error_Some_bound_index in Hnth.
            apply Forall2_length in Hforall2_hyps. lia. }
        (* Build dfacts list: each hyp's normal_dfact form *)
        (* We use Forall2 to relate hyps to dfacts cleanly *)
        assert (Hdfs_ex : exists dfs,
                  Forall2 (fun h df => exists R' args',
                              h = normal_fact R' args' /\ df = normal_dfact R' args') hyps dfs).
        { clear -Hhyps_normal.
          induction Hhyps_normal as [|h hs Hh Hhs IH].
          - exists nil. constructor.
          - destruct Hh as (R' & args' & ->).
            destruct IH as (dfs & IH).
            exists (normal_dfact R' args' :: dfs). constructor; eauto. }
        destruct Hdfs_ex as (dfs & Hdfs).
        (* Forall (knows_dfact s) dfs from Hderived *)
        assert (Hknown_dfs : Forall (knows_dfact s) dfs).
        { clear -Hderived Hdfs.
          induction Hdfs as [|h df hs dfs Hpair Hrest IH]; constructor.
          - destruct Hpair as (R' & args' & -> & ->).
            apply Forall_cons_iff in Hderived. destruct Hderived as (Hd & _).
            simpl in Hd. exact Hd.
          - apply Forall_cons_iff in Hderived. destruct Hderived as (_ & Hderived').
            apply IH. assumption. }
        (* Flush all dfs into rule k's known *)
        pose proof (flush_waiting_to_known inputs s k dfs Hinp Hsane_save Hknown_dfs Hk_lt_s)
          as (s1 & rs_k & Hsteps1 & Hnth_k & Hin_dfs & Hiff_kn).
        (* Preservation lemmas at s1 *)
        assert (Hsane1 : sane_state inputs s1) by eauto using steps_preserves_sane.
        assert (Hmfc1 : meta_facts_correct s1) by eauto using steps_preserves_mfs_correct.
        assert (Hsound1 : state_correct inputs s1) by eauto using comp_steps_sound.
        (* Build can_deduce_normal_fact nmr rs_k.known R_concl args_concl *)
        assert (Hcdn : can_deduce_normal_fact nmr rs_k.(known_facts) R_concl args_concl).
        { cbv [can_deduce_normal_fact]. exists hyps. split.
          - unfold nmr. simpl. econstructor; eassumption.
          - clear -Hdfs Hin_dfs.
            induction Hdfs as [|h df hs dfs0 Hpair Hrest IH]; constructor.
            + destruct Hpair as (R' & args' & -> & ->). simpl.
              apply Forall_cons_iff in Hin_dfs. apply Hin_dfs.
            + apply IH. apply Forall_cons_iff in Hin_dfs. apply Hin_dfs. }
        (* Case split on whether rs_k.sent contains a conflicting meta_dfact *)
        destruct (classic (exists mf_args num,
                              In (meta_dfact R_concl mf_args (Some k) num) rs_k.(sent_facts) /\
                              Forall2 matches mf_args args_concl)) as [Hconflict | Hno_conflict].
        * (* Conflict case: meta_facts_correct forces normal_dfact in rs_k.known *)
          destruct Hconflict as (mf_args & num & Hin_meta & Hmatch).
          cbv [meta_facts_correct] in Hmfc1.
          (* Use Forall3 to find meta_facts_correct_at_rule at index k *)
          assert (Hk_nm : nth_error p.(non_meta_rules) k = Some nmr) by exact Hk_nmr.
          assert (Hk_lt_s1 : k < length s1).
          { erewrite <- steps_preserves_length; eauto. }
          assert (Hk_seq : nth_error (seq 0 (length s1)) k = Some k).
          { rewrite nth_error_seq.
            assert (E : k <? length s1 = true) by (apply Nat.ltb_lt; lia).
            rewrite E. reflexivity. }
          (* Forall3 → get the predicate at index k *)
          assert (Hmfcr : meta_facts_correct_at_rule p.(meta_rules) k rs_k nmr).
          { eapply (Forall3_nth_error_fwd _ _ _ _ Hmfc1); eassumption. }
          specialize (Hmfcr R_concl mf_args num Hin_meta).
          destruct Hmfcr as (mfc & mfh & hyps' & Hin_mr & Hcdmf & Hknown_hyps' & Hnoself).
          cbv [can_deduce_meta_fact] in Hcdmf.
          destruct Hcdmf as (ctx' & mfr' & mfa' & mfcnt' & Hres & _ & _ & _ & Hforce).
          injection Hres as -> -> ->.
          specialize (Hforce args_concl Hcdn Hmatch).
          (* normal_dfact R_concl args_concl is in rs_k.known *)
          exists s1. split; [exact Hsteps1|].
          simpl. cbv [knows_dfact]. apply Exists_exists.
          apply nth_error_In in Hnth_k. eauto.
          exists rs_k. split; auto. left. exact Hforce.
        * (* No-conflict case: apply fire_normal_rule *)
          (* Build the labels list: combine non_meta_rules (seq 0 (length s1)) *)
          (* We need to fire at position k with rule nmr *)
          (* Split s1 at index k *)
          pose proof Hnth_k as Hnth_save.
          apply nth_error_split in Hnth_save.
          destruct Hnth_save as (s1_pre & s1_post & Hs1_eq & Hs1_pre_len).
          assert (Hk_lt_s1 : k < length s1).
          { erewrite <- steps_preserves_length; eauto. }
          assert (Hlen_s1 : length s = length s1) by eauto using steps_preserves_length.
          assert (Hlc1 : length (combine p.(non_meta_rules) (seq 0 (length s1))) = length s1).
          { rewrite length_combine, length_seq. lia. }
          assert (Hk_seq : nth_error (seq 0 (length s1)) k = Some k).
          { rewrite nth_error_seq.
            assert (E : k <? length s1 = true) by (apply Nat.ltb_lt; lia).
            rewrite E. reflexivity. }
          (* Compute combine labels s1 *)
          set (labels := combine p.(non_meta_rules) (seq 0 (length s1))).
          assert (Hcomb_decomp : exists l1 l2,
                    combine labels s1 = l1 ++ ((nmr, k), rs_k) :: l2 /\
                    map snd l1 = s1_pre /\ map snd l2 = s1_post /\
                    length l1 = k).
          { (* Decompose non_meta_rules at k *)
            pose proof Hk_nmr as Hk_nmr_s.
            apply nth_error_split in Hk_nmr_s.
            destruct Hk_nmr_s as (nmrs_pre & nmrs_post & Hnmrs_eq & Hnmrs_pre_len).
            (* Decompose seq at k *)
            pose proof Hk_seq as Hk_seq_s.
            apply nth_error_split in Hk_seq_s.
            destruct Hk_seq_s as (seq_pre & seq_post & Hseq_eq & Hseq_pre_len).
            (* labels split *)
            assert (Hlabels_split : labels =
                      combine nmrs_pre seq_pre ++ (nmr, k) :: combine nmrs_post seq_post).
            { unfold labels. rewrite Hnmrs_eq, Hseq_eq.
              rewrite combine_app by lia. simpl. reflexivity. }
            assert (Hcc_pre_len : length (combine nmrs_pre seq_pre) = k).
            { rewrite length_combine. lia. }
            exists (combine (combine nmrs_pre seq_pre) s1_pre),
                   (combine (combine nmrs_post seq_post) s1_post).
            ssplit.
            - rewrite Hlabels_split, Hs1_eq.
              rewrite combine_app by lia. simpl. reflexivity.
            - apply map_combine_snd. lia.
            - apply map_combine_snd. rewrite length_combine.
              (* length s1_post and length combine nmrs_post seq_post *)
              assert (Hpost_eq : length s1_post = length nmrs_post).
              { pose proof (f_equal (@length _) Hs1_eq) as Hl_s1.
                rewrite app_length in Hl_s1. simpl in Hl_s1.
                pose proof (f_equal (@length _) Hnmrs_eq) as Hl_nm.
                rewrite app_length in Hl_nm. simpl in Hl_nm. lia. }
              assert (Hpost_seq_eq : length seq_post = length nmrs_post).
              { pose proof (f_equal (@length _) Hseq_eq) as Hl_sq.
                rewrite app_length in Hl_sq. simpl in Hl_sq.
                rewrite length_seq in Hl_sq.
                pose proof (f_equal (@length _) Hnmrs_eq) as Hl_nm.
                rewrite app_length in Hl_nm. simpl in Hl_nm. lia. }
              lia.
            - rewrite length_combine. lia. }
          destruct Hcomb_decomp as (l1 & l2 & Hcomb & Hl1_snd & Hl2_snd & Hl1_len).
          (* Apply fire_normal_rule *)
          set (F := normal_dfact R_concl args_concl).
          set (rs_k' := send_fact F rs_k).
          set (s2 := map snd l1 ++ rs_k' :: map snd l2).
          exists (map (add_waiting_fact F) s2).
          split.
          -- eapply crt1n_trans_compose; [exact Hsteps1|].
             eapply Relation_Operators.rt1n_trans; [|apply rt1n_refl].
             apply (fire_normal_rule R_concl args_concl s1 s2).
             cbv [stepWithLabel].
             exists l1, (nmr, k), rs_k, rs_k', l2.
             ssplit.
             { exact Hcomb. }
             { unfold s2. rewrite Hl1_snd, Hl2_snd. reflexivity. }
             { exact Hcdn. }
             { intros mf_args num Hin_meta Hmatch.
               apply Hno_conflict. exists mf_args, num. auto. }
             { reflexivity. }
          -- simpl. cbv [knows_dfact]. apply Exists_exists.
             eexists. split.
             ++ apply in_map_iff.
                eexists. split; [reflexivity|].
                rewrite Hs1_eq. apply in_or_app. right. left. reflexivity.
             ++ cbv [rule_has_dfact add_waiting_fact]. simpl. right. left. reflexivity.
      + (* agg_rule_impl: ru = agg_rule cr ag hr, nmr = nmr_agg cr ag hr.
           After invert, hyps = meta_fact hr (None :: None :: map Some args0) S
                              :: map (fun '(i, x_i) => normal_fact hr (...)) vals.
           Conclusion: normal_fact cr (interp_agg ag vals :: args0).
           Key insight: is_list_set ensures vals is finite enumeration of S's
           pairs (modulo args0), making the bicondition tractable. *)
        set (nmr := nmr_agg cr ag hr) in *.
        rename R into R_concl, args into args_concl.
        inversion Hnmri; subst.
        match goal with H : is_list_set _ _ |- _ => rename H into His_set end.
        rename args into args_rest, S into S_set, vals into vals_pairs.
        (* Decompose Hderived into meta-fact and val-normals *)
        apply Forall_cons_iff in Hderived.
        destruct Hderived as (Hd_meta & Hd_normals).
        apply Forall_cons_iff in Hcons.
        destruct Hcons as (Hc_meta & _).
        (* dfs from val normals *)
        pose (val_dfs := map (fun (p_pair : T * T) =>
                                let '(i, x_i) := p_pair in normal_dfact hr (i :: x_i :: args_rest))
                             vals_pairs).
        assert (Hkn_val_dfs : Forall (knows_dfact s) val_dfs).
        { unfold val_dfs.
          apply Forall_forall. intros df Hin.
          apply in_map_iff in Hin. destruct Hin as ((i, x_i) & Heq & Hin_pair). subst df.
          rewrite Forall_forall in Hd_normals.
          assert (Hin_map : In (normal_fact hr (i :: x_i :: args_rest))
                              (map (fun '(i, x_i) => normal_fact hr (i :: x_i :: args_rest)) vals_pairs)).
          { apply in_map_iff. exists (i, x_i). split; [reflexivity|exact Hin_pair]. }
          specialize (Hd_normals _ Hin_map). simpl in Hd_normals. exact Hd_normals. }
        (* Now extract meta_dfacts from Hd_meta, case-splitting on is_input hr *)
        pose (mf_args := None :: None :: map Some args_rest : list (option T)).
        destruct (is_input hr) eqn:Hhr_inp.
        * (* Input hr: single meta_dfact with None source *)
          cbv [has_derived_datalog_fact] in Hd_meta.
          rewrite Hhr_inp in Hd_meta.
          destruct Hd_meta as (num_inp & Hknows_meta).
          pose (all_dfs := meta_dfact hr mf_args None num_inp :: val_dfs).
          assert (Hkn_all_dfs : Forall (knows_dfact s) all_dfs).
          { constructor; [exact Hknows_meta|exact Hkn_val_dfs]. }
          (* Flush all_dfs into rs_k's known *)
          pose proof (flush_waiting_to_known inputs s k all_dfs Hinp Hsane_save Hkn_all_dfs Hk_lt_s)
            as (s_int & rs_k_int & Hsteps_int & Hnth_k_int & Hin_all_dfs_int & Hiff_int).
          assert (Hsane_int : sane_state inputs s_int) by eauto using steps_preserves_sane.
          (* Drain remaining matching from rs_k_int.waiting *)
          assert (Hk_lt_s_int : k < length s_int).
          { erewrite <- steps_preserves_length; eauto. }
          pose proof (flush_all_matching_from_waiting inputs s_int k hr mf_args
                       Hinp Hsane_int Hk_lt_s_int)
            as (s1 & rs_k & Hsteps_drain & Hnth_k & Hex_w_0 & Hiff_drain).
          (* Compose traces and iff *)
          assert (Hsteps1 : comp_step^* s s1) by (eapply crt1n_trans_compose; eassumption).
          assert (Hiff_kn : forall g, knows_dfact s1 g <-> knows_dfact s g).
          { intros g. rewrite Hiff_drain, Hiff_int. reflexivity. }
          (* all_dfs are still in rs_k.known (via steps_preserves_known_at) *)
          assert (Hin_all_dfs : Forall (fun h => In h rs_k.(known_facts)) all_dfs).
          { pose proof (steps_preserves_known_at _ _ _ _ _ Hinp Hsane_int Hsteps_drain Hnth_k_int)
              as (rs_k' & Hnth_eq & Hincl).
            rewrite Hnth_eq in Hnth_k. injection Hnth_k as ->.
            eapply Forall_impl; [|exact Hin_all_dfs_int].
            cbv beta. intros f Hf. apply Hincl. exact Hf. }
          assert (Hsane1 : sane_state inputs s1) by eauto using steps_preserves_sane.
          assert (Hmfc1 : meta_facts_correct s1) by eauto using steps_preserves_mfs_correct.
          assert (Hsound1 : state_correct inputs s1) by eauto using comp_steps_sound.
          (* Build can_deduce_normal_fact at rs_k *)
          assert (Hcdn : can_deduce_normal_fact nmr rs_k.(known_facts)
                          R_concl (interp_agg ag vals_pairs :: args_rest)).
          { cbv [can_deduce_normal_fact]. eexists. split.
            - unfold nmr. cbn [rule_of]. exact Hnmri.
            - constructor.
              + (* meta_fact case *)
                cbv [knows_datalog_fact]. exists num_inp. ssplit.
                * cbv [expect_num_R_facts]. rewrite Hhr_inp.
                  apply Forall_cons_iff in Hin_all_dfs. apply Hin_all_dfs.
                * (* Existsn count = num_inp via Hcount + drain (num_wait = 0) *)
                  destruct Hsane1 as (_ & Hmf_inp_s1 & _ & _ & Hcount_s1 & Hinp_sane_s1 & _).
                  pose proof (Hcount_s1 hr mf_args) as Hcount_hr.
                  destruct Hcount_hr as (msgs_sents & num_inp_actual & Hf2_msgs & Hex_inp_actual & Hforall_kn).
                  rewrite Forall_forall in Hforall_kn.
                  specialize (Hforall_kn rs_k (nth_error_In _ _ Hnth_k)).
                  destruct Hforall_kn as (num_known & num_wait & Hex_kn & Hex_w & Hsum).
                  pose proof (Existsn_unique _ _ _ _ Hex_w Hex_w_0) as Hnw_eq.
                  subst num_wait.
                  (* sum_sent = 0 for input hr by Hinp_sane *)
                  pose proof (Hinp_sane_s1 hr Hhr_inp) as (Hinp_zero & _).
                  specialize (Hinp_zero mf_args).
                  assert (Hsum_msgs_zero : fold_left Nat.add msgs_sents O = O).
                  { clear -Hinp_zero Hf2_msgs.
                    revert msgs_sents Hf2_msgs Hinp_zero.
                    induction s1 as [|rs s' IH]; intros [|m ms] Hf2 Hi.
                    - simpl. reflexivity.
                    - inversion Hf2.
                    - inversion Hf2.
                    - inversion Hf2 as [|? ? ? ? Hex' Hf2_rest]; subst.
                      apply Forall_cons_iff in Hi. destruct Hi as (Hrs_zero & Hi_rest).
                      pose proof (Existsn_unique _ _ _ _ Hex' Hrs_zero) as Heq. subst m.
                      simpl. apply IH; assumption. }
                  rewrite Hsum_msgs_zero, Nat.add_0_r in Hsum.
                  (* num_known = num_inp_actual *)
                  rewrite Nat.add_0_r in Hsum.
                  subst num_known.
                  (* Now num_inp = num_inp_actual since both come from same meta_dfact *)
                  assert (Hnum_eq : num_inp = num_inp_actual).
                  { (* Get prog_impl on the meta_fact hyp via state_correct *)
                    assert (Hd_meta_reconstr : has_derived_datalog_fact s
                                                 (meta_fact hr mf_args S_set)).
                    { cbv [has_derived_datalog_fact]. rewrite Hhr_inp.
                      exists num_inp. exact Hknows_meta. }
                    assert (Hprog_meta : prog_impl rules_of (knows_datalog_fact inputs)
                                          (meta_fact hr mf_args S_set)).
                    { apply Hsound. split; [exact Hd_meta_reconstr | exact Hc_meta]. }
                    (* By prog_impl_input_meta_implies_Q_leaf *)
                    pose proof (prog_impl_input_meta_implies_Q_leaf
                                 inputs hr mf_args S_set Hhr_inp Hprog_meta) as HQ.
                    cbv [knows_datalog_fact] in HQ. fold mf_args in HQ.
                    destruct HQ as (num_q & Hexp_q & Hex_q & _).
                    cbv [expect_num_R_facts] in Hexp_q. rewrite Hhr_inp in Hexp_q.
                    (* Hexp_q: In (meta_dfact hr mf_args None num_q) inputs.
                       Hex_q: Existsn match num_q inputs. *)
                    (* From Hknows_meta: knows_dfact s (meta_dfact ... num_inp).
                       By Hmf_inp at s (via Hsane_save): In meta_dfact ... num_inp inputs. *)
                    destruct Hsane_save as (_ & Hmf_inp_s & _ & _ & _ & _ & _).
                    specialize (Hmf_inp_s hr mf_args num_inp Hknows_meta).
                    (* good_input_facts uniqueness: num_q = num_inp *)
                    destruct Hinp as (_ & Hinp_unique).
                    pose proof (Hinp_unique hr mf_args num_q Hexp_q) as (Hunq & _).
                    specialize (Hunq num_inp Hmf_inp_s). subst num_q.
                    (* Hex_q : Existsn match num_inp inputs. Hex_inp_actual : Existsn match num_inp_actual inputs. *)
                    apply (Existsn_unique _ _ _ _ Hex_q Hex_inp_actual).
                  }
                  subst num_inp_actual.
                  exact Hex_kn.
                * (* Bicondition *)
                  intros nf_args Hmatch.
                  cbv [mf_consistent_state] in Hc_meta. specialize (Hc_meta nf_args Hmatch).
                  split.
                  -- (* S_set nf_args → In normal_dfact rs_k.known *)
                     intros HS.
                     destruct His_set as (His_iff & _).
                     (* Extract i, x: nf_args = y1 :: y2 :: args_rest by matching mf_args structure *)
                     inversion Hmatch as [|? y1 ? rr1 H1 Hmatch']; subst.
                     inversion Hmatch' as [|? y2 ? rr2 H2 Hmatch'']; subst.
                     assert (Hrest : rr2 = args_rest).
                     { clear -Hmatch''.
                       revert rr2 Hmatch''. induction args_rest as [|a args_r IH];
                         intros rr2 Hm.
                       - inversion Hm; reflexivity.
                       - simpl in Hm. inversion Hm as [|? ? ? rs Hmm Hmm']; subst.
                         cbv [matches] in Hmm. subst.
                         f_equal. apply IH. assumption. }
                     subst rr2.
                     pose proof (His_iff (y1, y2)) as His_y.
                     apply His_y in HS.
                     apply Forall_cons_iff in Hin_all_dfs. destruct Hin_all_dfs as (_ & Hin_val_dfs).
                     rewrite Forall_forall in Hin_val_dfs.
                     apply Hin_val_dfs.
                     unfold val_dfs. apply in_map_iff. exists (y1, y2).
                     split; [reflexivity|exact HS].
                  -- (* In normal_dfact rs_k.known → S_set nf_args *)
                     intros Hin_kn.
                     apply Hc_meta.
                     rewrite <- Hiff_kn.
                     cbv [knows_dfact]. apply Exists_exists.
                     exists rs_k. split; [apply nth_error_In in Hnth_k; exact Hnth_k|].
                     left. exact Hin_kn.
              + (* val normals: each In rs_k.known via Hin_all_dfs *)
                apply Forall_forall. intros f Hin.
                apply in_map_iff in Hin. destruct Hin as ((i, x_i) & <- & Hin_pair).
                simpl.
                apply Forall_cons_iff in Hin_all_dfs. destruct Hin_all_dfs as (_ & Hin_val_dfs).
                rewrite Forall_forall in Hin_val_dfs.
                apply Hin_val_dfs.
                unfold val_dfs. apply in_map_iff.
                exists (i, x_i). split; [reflexivity|exact Hin_pair]. }
          (* The rest mirrors normal_rule_impl: case split on conflict, fire *)
          destruct (classic (exists mf_args' num,
                              In (meta_dfact R_concl mf_args' (Some k) num) rs_k.(sent_facts) /\
                              Forall2 matches mf_args' (interp_agg ag vals_pairs :: args_rest))) as [Hconflict | Hno_conflict].
          -- (* Conflict case: meta_facts_correct forces normal_dfact in rs_k.known *)
             destruct Hconflict as (mf_args' & num & Hin_meta & Hmatch).
             assert (Hk_seq : nth_error (seq 0 (length s1)) k = Some k).
             { assert (Hk_lt_s1 : k < length s1) by (erewrite <- steps_preserves_length; eauto).
               rewrite nth_error_seq.
               assert (E : k <? length s1 = true) by (apply Nat.ltb_lt; lia).
               rewrite E. reflexivity. }
             assert (Hmfcr : meta_facts_correct_at_rule p.(meta_rules) k rs_k nmr).
             { eapply (Forall3_nth_error_fwd _ _ _ _ Hmfc1); eassumption. }
             specialize (Hmfcr R_concl mf_args' num Hin_meta).
             destruct Hmfcr as (mfc & mfh & hyps' & Hin_mr & Hcdmf & Hknown_hyps' & Hnoself).
             cbv [can_deduce_meta_fact] in Hcdmf.
             destruct Hcdmf as (ctx' & mfr' & mfa' & mfcnt' & Hres & _ & _ & _ & Hforce).
             injection Hres as -> -> ->.
             specialize (Hforce (interp_agg ag vals_pairs :: args_rest) Hcdn Hmatch).
             exists s1. split; [exact Hsteps1|].
             simpl. cbv [knows_dfact]. apply Exists_exists.
             exists rs_k. split; [apply nth_error_In in Hnth_k; exact Hnth_k|].
             left. exact Hforce.
          -- (* No-conflict: apply fire_normal_rule *)
             pose proof Hnth_k as Hnth_save.
             apply nth_error_split in Hnth_save.
             destruct Hnth_save as (s1_pre & s1_post & Hs1_eq & Hs1_pre_len).
             assert (Hk_lt_s1 : k < length s1) by (erewrite <- steps_preserves_length; eauto).
             assert (Hlen_s1 : length s = length s1) by eauto using steps_preserves_length.
             assert (Hk_seq : nth_error (seq 0 (length s1)) k = Some k).
             { rewrite nth_error_seq.
               assert (E : k <? length s1 = true) by (apply Nat.ltb_lt; lia).
               rewrite E. reflexivity. }
             set (labels := combine p.(non_meta_rules) (seq 0 (length s1))).
             assert (Hcomb_decomp : exists l1 l2,
                       combine labels s1 = l1 ++ ((nmr, k), rs_k) :: l2 /\
                       map snd l1 = s1_pre /\ map snd l2 = s1_post /\
                       length l1 = k).
             { pose proof Hk_nmr as Hk_nmr_s.
               apply nth_error_split in Hk_nmr_s.
               destruct Hk_nmr_s as (nmrs_pre & nmrs_post & Hnmrs_eq & Hnmrs_pre_len).
               pose proof Hk_seq as Hk_seq_s.
               apply nth_error_split in Hk_seq_s.
               destruct Hk_seq_s as (seq_pre & seq_post & Hseq_eq & Hseq_pre_len).
               assert (Hlabels_split : labels =
                         combine nmrs_pre seq_pre ++ (nmr, k) :: combine nmrs_post seq_post).
               { unfold labels. rewrite Hnmrs_eq, Hseq_eq.
                 rewrite combine_app by lia. simpl. reflexivity. }
               assert (Hcc_pre_len : length (combine nmrs_pre seq_pre) = k).
               { rewrite length_combine. lia. }
               exists (combine (combine nmrs_pre seq_pre) s1_pre),
                      (combine (combine nmrs_post seq_post) s1_post).
               ssplit.
               - rewrite Hlabels_split, Hs1_eq.
                 rewrite combine_app by lia. simpl. reflexivity.
               - apply map_combine_snd. lia.
               - apply map_combine_snd. rewrite length_combine.
                 assert (Hpost_eq : length s1_post = length nmrs_post).
                 { pose proof (f_equal (@length _) Hs1_eq) as Hl_s1.
                   rewrite length_app in Hl_s1. simpl in Hl_s1.
                   pose proof (f_equal (@length _) Hnmrs_eq) as Hl_nm.
                   rewrite length_app in Hl_nm. simpl in Hl_nm. lia. }
                 assert (Hpost_seq_eq : length seq_post = length nmrs_post).
                 { pose proof (f_equal (@length _) Hseq_eq) as Hl_sq.
                   rewrite length_app in Hl_sq. simpl in Hl_sq.
                   rewrite length_seq in Hl_sq.
                   pose proof (f_equal (@length _) Hnmrs_eq) as Hl_nm.
                   rewrite length_app in Hl_nm. simpl in Hl_nm. lia. }
                 lia.
               - rewrite length_combine. lia. }
             destruct Hcomb_decomp as (l1 & l2 & Hcomb & Hl1_snd & Hl2_snd & Hl1_len).
             set (F := normal_dfact R_concl (interp_agg ag vals_pairs :: args_rest)).
             set (rs_k' := send_fact F rs_k).
             set (s2 := map snd l1 ++ rs_k' :: map snd l2).
             exists (map (add_waiting_fact F) s2).
             split.
             ++ eapply crt1n_trans_compose; [exact Hsteps1|].
                eapply Relation_Operators.rt1n_trans; [|apply rt1n_refl].
                apply (fire_normal_rule R_concl (interp_agg ag vals_pairs :: args_rest) s1 s2).
                cbv [stepWithLabel].
                exists l1, (nmr, k), rs_k, rs_k', l2.
                ssplit.
                { exact Hcomb. }
                { unfold s2. rewrite Hl1_snd, Hl2_snd. reflexivity. }
                { exact Hcdn. }
                { intros mf_args' num Hin_meta Hmatch.
                  apply Hno_conflict. exists mf_args', num. auto. }
                { reflexivity. }
             ++ simpl. cbv [knows_dfact]. apply Exists_exists.
                eexists. split.
                ** apply in_map_iff.
                   eexists. split; [reflexivity|].
                   rewrite Hs1_eq. apply in_or_app. right. left. reflexivity.
                ** cbv [rule_has_dfact add_waiting_fact]. simpl. right. left. reflexivity.
        * (* Non-input hr: per-source meta_dfacts *)
          cbv [has_derived_datalog_fact] in Hd_meta.
          rewrite Hhr_inp in Hd_meta.
          (* Hd_meta : forall k_src < length non_meta_rules, exists num, knows_dfact s (meta_dfact hr mf_args (Some k_src) num) *)
          pose proof (extract_per_source_meta_dfacts s hr mf_args (length p.(non_meta_rules)) Hd_meta)
            as (nums & Hlen_nums & HF2_nums).
          pose (meta_dfs := map (fun '(k_src, num) => meta_dfact hr mf_args (Some k_src) num)
                                (combine (seq 0 (length p.(non_meta_rules))) nums)).
          assert (Hnth_combine_split : forall {A B} (l1 : list A) (l2 : list B) i a b,
                    nth_error (combine l1 l2) i = Some (a, b) ->
                    nth_error l1 i = Some a /\ nth_error l2 i = Some b).
          { clear. intros A B l1. induction l1 as [|x xs IH]; intros l2 i a b;
              destruct l2 as [|y ys]; destruct i; simpl; try discriminate.
            - intros [= -> ->]. split; reflexivity.
            - intros H. apply (IH _ _ _ _ H). }
          assert (Hkn_meta_dfs : Forall (knows_dfact s) meta_dfs).
          { unfold meta_dfs.
            apply Forall_forall. intros df Hin.
            apply in_map_iff in Hin. destruct Hin as ((k_src, num) & Heq & Hin_pair). subst df.
            apply In_nth_error in Hin_pair. destruct Hin_pair as (i & Hnth).
            destruct (Hnth_combine_split nat nat _ _ _ _ _ Hnth) as (Hi_seq & Hi_nums).
            pose proof (Forall2_nth_error_fwd _ _ _ HF2_nums i k_src num Hi_seq Hi_nums)
              as Hknows. exact Hknows. }
          pose (all_dfs := meta_dfs ++ val_dfs).
          assert (Hkn_all_dfs : Forall (knows_dfact s) all_dfs).
          { unfold all_dfs. apply Forall_app. split; assumption. }
          (* Initial flush *)
          pose proof (flush_waiting_to_known inputs s k all_dfs Hinp Hsane_save Hkn_all_dfs Hk_lt_s)
            as (s_int & rs_k_int & Hsteps_int & Hnth_k_int & Hin_all_dfs_int & Hiff_int).
          assert (Hsane_int : sane_state inputs s_int) by eauto using steps_preserves_sane.
          assert (Hk_lt_s_int : k < length s_int).
          { erewrite <- steps_preserves_length; eauto. }
          (* Drain remaining matching from waiting *)
          pose proof (flush_all_matching_from_waiting inputs s_int k hr mf_args
                       Hinp Hsane_int Hk_lt_s_int)
            as (s1 & rs_k & Hsteps_drain & Hnth_k & Hex_w_0 & Hiff_drain).
          assert (Hsteps1 : comp_step^* s s1) by (eapply crt1n_trans_compose; eassumption).
          assert (Hiff_kn : forall g, knows_dfact s1 g <-> knows_dfact s g).
          { intros g. rewrite Hiff_drain, Hiff_int. reflexivity. }
          assert (Hin_all_dfs : Forall (fun h => In h rs_k.(known_facts)) all_dfs).
          { pose proof (steps_preserves_known_at _ _ _ _ _ Hinp Hsane_int Hsteps_drain Hnth_k_int)
              as (rs_k' & Hnth_eq & Hincl).
            rewrite Hnth_eq in Hnth_k. injection Hnth_k as ->.
            eapply Forall_impl; [|exact Hin_all_dfs_int].
            cbv beta. intros f Hf. apply Hincl. exact Hf. }
          assert (Hsane1 : sane_state inputs s1) by eauto using steps_preserves_sane.
          assert (Hmfc1 : meta_facts_correct s1) by eauto using steps_preserves_mfs_correct.
          assert (Hsound1 : state_correct inputs s1) by eauto using comp_steps_sound.
          assert (Hcdn : can_deduce_normal_fact nmr rs_k.(known_facts)
                          R_concl (interp_agg ag vals_pairs :: args_rest)).
          { cbv [can_deduce_normal_fact]. eexists. split.
            - unfold nmr. cbn [rule_of]. exact Hnmri.
            - constructor.
              + (* meta_fact case (non-input hr) *)
                cbv [knows_datalog_fact].
                exists (fold_left Nat.add nums 0). ssplit.
                * (* expect_num_R_facts: Forall2 ... In meta_dfact ... rs_k.known per source *)
                  cbv [expect_num_R_facts]. rewrite Hhr_inp.
                  exists nums. split; [|reflexivity].
                  (* meta_dfs (all flushed) at each source; show via Forall2_nth_error_bwd *)
                  apply Forall2_nth_error_bwd; [rewrite length_seq; lia|].
                  intros i k_src num_i Hi_seq Hi_nums.
                  apply Forall_app in Hin_all_dfs. destruct Hin_all_dfs as (Hin_meta_dfs & _).
                  rewrite Forall_forall in Hin_meta_dfs.
                  apply Hin_meta_dfs.
                  unfold meta_dfs. apply in_map_iff.
                  exists (k_src, num_i). split; [reflexivity|].
                  apply nth_error_In with (n := i).
                  (* combine at position i gives (k_src, num_i) *)
                  clear -Hi_seq Hi_nums.
                  revert nums i Hi_seq Hi_nums.
                  generalize (seq 0 (length p.(non_meta_rules))) as l1.
                  induction l1 as [|a l1' IH]; intros [|b nums'] i Hi_seq Hi_nums;
                    destruct i; simpl in *; try discriminate.
                  -- injection Hi_seq as ->. injection Hi_nums as ->. reflexivity.
                  -- apply IH; assumption.
                * (* Existsn count = fold_left Nat.add nums 0 *)
                  destruct Hsane1 as (_ & _ & Hmf_sent_s1 & _ & Hcount_s1 & _ & _).
                  pose proof (Hcount_s1 hr mf_args) as Hcount_hr.
                  destruct Hcount_hr as (msgs_sents & num_inp_actual & Hf2_msgs & Hex_inp_actual & Hforall_kn).
                  rewrite Forall_forall in Hforall_kn.
                  specialize (Hforall_kn rs_k (nth_error_In _ _ Hnth_k)).
                  destruct Hforall_kn as (num_known & num_wait & Hex_kn & Hex_w & Hsum).
                  pose proof (Existsn_unique _ _ _ _ Hex_w Hex_w_0) as Hnw_eq.
                  subst num_wait.
                  rewrite Nat.add_0_r in Hsum.
                  (* num_inp_actual = 0 for non-input rel *)
                  assert (Hinp_zero : num_inp_actual = 0).
                  { destruct Hinp as (Hinp_all & _). rewrite Forall_forall in Hinp_all.
                    (* No matching items in inputs for non-input hr *)
                    clear -Hex_inp_actual Hinp_all Hhr_inp.
                    revert num_inp_actual Hex_inp_actual.
                    induction inputs as [|f rest IH]; intros num_inp_actual Hex.
                    - inversion Hex; reflexivity.
                    - inversion Hex as [|? ? ? Hnot Hex_rest|? ? ? Hyes Hex_rest]; subst.
                      + apply IH; auto.
                        intros f' Hf'. apply Hinp_all. right. exact Hf'.
                      + exfalso.
                        destruct Hyes as (nf_args & Heq & _). subst f.
                        specialize (Hinp_all _ (or_introl eq_refl)).
                        simpl in Hinp_all. congruence. }
                  subst num_inp_actual.
                  simpl in Hsum.
                  (* num_known = sum_sent. We want = num = fold_left Nat.add nums 0. *)
                  (* sum_sent = fold_left Nat.add msgs_sents 0, where msgs_sents counts matching in each rule's sent. *)
                  (* nums was constructed from per-source meta_dfact's count.
                     By Hmf_sent_s1: nums[k_src] = matching count in rs_{k_src}.sent.
                     msgs_sents[k_src] = matching count in rs_{k_src}.sent (by Hf2_msgs).
                     So msgs_sents = nums (extensionally; Forall2_eq via uniqueness). *)
                  (* Stronger: show fold_left = fold_left *)
                  assert (Hsents_eq : forall (l1 l2 : list nat),
                            Forall2 eq l1 l2 -> fold_left Nat.add l1 0 = fold_left Nat.add l2 0).
                  { clear. intros l1 l2 H.
                    assert (Heq : l1 = l2).
                    { induction H; subst; reflexivity. }
                    subst. reflexivity. }
                  assert (Hmsgs_eq : Forall2 eq msgs_sents nums).
                  { (* Both lists count matching in each rule's sent (by Hf2_msgs and HF2_nums via Hmf_sent_s1) *)
                    eapply Forall2_nth_error_bwd.
                    { pose proof (Forall2_length Hf2_msgs) as Hl_ms.
                      apply Forall2_length in HF2_nums. rewrite length_seq in HF2_nums.
                      pose proof (steps_preserves_length _ _ _ Hinp Hsane_save Hsteps1) as Hlen_s1.
                      pose proof Hsane_save as (Hlen_s_outer & _). lia. }
                    intros i ms_i num_i Hi_ms Hi_num.
                    (* Step 1: knows_dfact s (meta_dfact ... (Some i) num_i) from HF2_nums *)
                    pose proof (Forall2_length HF2_nums) as Hlen_HF2.
                    rewrite length_seq in Hlen_HF2.
                    assert (Hi_lt : i < length p.(non_meta_rules)).
                    { apply nth_error_Some_bound_index in Hi_num. lia. }
                    assert (Hi_seq : nth_error (seq 0 (length p.(non_meta_rules))) i = Some i).
                    { rewrite nth_error_seq.
                      assert (E : i <? length p.(non_meta_rules) = true) by (apply Nat.ltb_lt; lia).
                      rewrite E. reflexivity. }
                    pose proof (Forall2_nth_error_fwd _ _ _ HF2_nums i i num_i Hi_seq Hi_num)
                      as Hknows_s.
                    (* Step 2: knows_dfact s1 ... via Hiff_kn *)
                    assert (Hknows_s1 : knows_dfact s1 (meta_dfact hr mf_args (Some i) num_i)).
                    { apply Hiff_kn. exact Hknows_s. }
                    (* Step 3: By Hmf_sent_s1, at rs_i_s1.sent matching count = num_i *)
                    specialize (Hmf_sent_s1 _ _ _ _ Hknows_s1).
                    cbv [nth_sat] in Hmf_sent_s1.
                    (* Step 4: from Hf2_msgs at i, get Existsn at rs_i_s1.sent = ms_i *)
                    pose proof (Forall2_length Hf2_msgs) as Hf2_len.
                    assert (Hi_s1 : exists rs_i, nth_error s1 i = Some rs_i).
                    { destruct (nth_error s1 i) eqn:E; [eauto|].
                      apply nth_error_None in E.
                      apply nth_error_Some_bound_index in Hi_ms. lia. }
                    destruct Hi_s1 as (rs_i & Hnth_s1).
                    rewrite Hnth_s1 in Hmf_sent_s1.
                    destruct Hmf_sent_s1 as (Hex_num_i & _).
                    pose proof (Forall2_nth_error_fwd _ _ _ Hf2_msgs i rs_i ms_i Hnth_s1 Hi_ms)
                      as Hex_ms_i.
                    pose proof (Existsn_unique _ _ _ _ Hex_ms_i Hex_num_i) as Heq. exact Heq. }
                  apply Hsents_eq in Hmsgs_eq.
                  rewrite Hmsgs_eq in Hsum.
                  rewrite <- Hsum. exact Hex_kn.
                * (* Bicondition (same as input case) *)
                  intros nf_args Hmatch.
                  cbv [mf_consistent_state] in Hc_meta. specialize (Hc_meta nf_args Hmatch).
                  split.
                  -- intros HS.
                     destruct His_set as (His_iff & _).
                     inversion Hmatch as [|? y1 ? rr1 H1 Hmatch']; subst.
                     inversion Hmatch' as [|? y2 ? rr2 H2 Hmatch'']; subst.
                     assert (Hrest : rr2 = args_rest).
                     { clear -Hmatch''.
                       revert rr2 Hmatch''. induction args_rest as [|a args_r IH];
                         intros rr2 Hm.
                       - inversion Hm; reflexivity.
                       - simpl in Hm. inversion Hm as [|? ? ? rs Hmm Hmm']; subst.
                         cbv [matches] in Hmm. subst.
                         f_equal. apply IH. assumption. }
                     subst rr2.
                     pose proof (His_iff (y1, y2)) as His_y.
                     apply His_y in HS.
                     apply Forall_app in Hin_all_dfs. destruct Hin_all_dfs as (_ & Hin_val_dfs).
                     rewrite Forall_forall in Hin_val_dfs.
                     apply Hin_val_dfs.
                     unfold val_dfs. apply in_map_iff. exists (y1, y2).
                     split; [reflexivity|exact HS].
                  -- intros Hin_kn.
                     apply Hc_meta.
                     rewrite <- Hiff_kn.
                     cbv [knows_dfact]. apply Exists_exists.
                     exists rs_k. split; [apply nth_error_In in Hnth_k; exact Hnth_k|].
                     left. exact Hin_kn.
              + apply Forall_forall. intros f Hin.
                apply in_map_iff in Hin. destruct Hin as ((i, x_i) & <- & Hin_pair).
                simpl.
                (* all_dfs = meta_dfs ++ val_dfs; val_dfs has the normal_dfact *)
                apply Forall_app in Hin_all_dfs. destruct Hin_all_dfs as (_ & Hin_val_dfs).
                rewrite Forall_forall in Hin_val_dfs.
                apply Hin_val_dfs.
                unfold val_dfs. apply in_map_iff.
                exists (i, x_i). split; [reflexivity|exact Hin_pair]. }
          (* Mirror the input-case case-split + fire structure *)
          destruct (classic (exists mf_args' num,
                              In (meta_dfact R_concl mf_args' (Some k) num) rs_k.(sent_facts) /\
                              Forall2 matches mf_args' (interp_agg ag vals_pairs :: args_rest))) as [Hconflict | Hno_conflict].
          -- destruct Hconflict as (mf_args' & num_c & Hin_meta & Hmatch).
             assert (Hk_seq : nth_error (seq 0 (length s1)) k = Some k).
             { assert (Hk_lt_s1 : k < length s1) by (erewrite <- steps_preserves_length; eauto).
               rewrite nth_error_seq.
               assert (E : k <? length s1 = true) by (apply Nat.ltb_lt; lia).
               rewrite E. reflexivity. }
             assert (Hmfcr : meta_facts_correct_at_rule p.(meta_rules) k rs_k nmr).
             { eapply (Forall3_nth_error_fwd _ _ _ _ Hmfc1); eassumption. }
             specialize (Hmfcr R_concl mf_args' num_c Hin_meta).
             destruct Hmfcr as (mfc & mfh & hyps' & Hin_mr & Hcdmf & Hknown_hyps' & Hnoself).
             cbv [can_deduce_meta_fact] in Hcdmf.
             destruct Hcdmf as (ctx' & mfr' & mfa' & mfcnt' & Hres & _ & _ & _ & Hforce).
             injection Hres as -> -> ->.
             specialize (Hforce (interp_agg ag vals_pairs :: args_rest) Hcdn Hmatch).
             exists s1. split; [exact Hsteps1|].
             simpl. cbv [knows_dfact]. apply Exists_exists.
             exists rs_k. split; [apply nth_error_In in Hnth_k; exact Hnth_k|].
             left. exact Hforce.
          -- pose proof Hnth_k as Hnth_save.
             apply nth_error_split in Hnth_save.
             destruct Hnth_save as (s1_pre & s1_post & Hs1_eq & Hs1_pre_len).
             assert (Hk_lt_s1 : k < length s1) by (erewrite <- steps_preserves_length; eauto).
             assert (Hlen_s1 : length s = length s1) by eauto using steps_preserves_length.
             assert (Hk_seq : nth_error (seq 0 (length s1)) k = Some k).
             { rewrite nth_error_seq.
               assert (E : k <? length s1 = true) by (apply Nat.ltb_lt; lia).
               rewrite E. reflexivity. }
             set (labels := combine p.(non_meta_rules) (seq 0 (length s1))).
             assert (Hcomb_decomp : exists l1 l2,
                       combine labels s1 = l1 ++ ((nmr, k), rs_k) :: l2 /\
                       map snd l1 = s1_pre /\ map snd l2 = s1_post /\
                       length l1 = k).
             { pose proof Hk_nmr as Hk_nmr_s.
               apply nth_error_split in Hk_nmr_s.
               destruct Hk_nmr_s as (nmrs_pre & nmrs_post & Hnmrs_eq & Hnmrs_pre_len).
               pose proof Hk_seq as Hk_seq_s.
               apply nth_error_split in Hk_seq_s.
               destruct Hk_seq_s as (seq_pre & seq_post & Hseq_eq & Hseq_pre_len).
               assert (Hlabels_split : labels =
                         combine nmrs_pre seq_pre ++ (nmr, k) :: combine nmrs_post seq_post).
               { unfold labels. rewrite Hnmrs_eq, Hseq_eq.
                 rewrite combine_app by lia. simpl. reflexivity. }
               assert (Hcc_pre_len : length (combine nmrs_pre seq_pre) = k).
               { rewrite length_combine. lia. }
               exists (combine (combine nmrs_pre seq_pre) s1_pre),
                      (combine (combine nmrs_post seq_post) s1_post).
               ssplit.
               - rewrite Hlabels_split, Hs1_eq.
                 rewrite combine_app by lia. simpl. reflexivity.
               - apply map_combine_snd. lia.
               - apply map_combine_snd. rewrite length_combine.
                 assert (Hpost_eq : length s1_post = length nmrs_post).
                 { pose proof (f_equal (@length _) Hs1_eq) as Hl_s1.
                   rewrite length_app in Hl_s1. simpl in Hl_s1.
                   pose proof (f_equal (@length _) Hnmrs_eq) as Hl_nm.
                   rewrite length_app in Hl_nm. simpl in Hl_nm. lia. }
                 assert (Hpost_seq_eq : length seq_post = length nmrs_post).
                 { pose proof (f_equal (@length _) Hseq_eq) as Hl_sq.
                   rewrite length_app in Hl_sq. simpl in Hl_sq.
                   rewrite length_seq in Hl_sq.
                   pose proof (f_equal (@length _) Hnmrs_eq) as Hl_nm.
                   rewrite length_app in Hl_nm. simpl in Hl_nm. lia. }
                 lia.
               - rewrite length_combine. lia. }
             destruct Hcomb_decomp as (l1 & l2 & Hcomb & Hl1_snd & Hl2_snd & Hl1_len).
             set (F := normal_dfact R_concl (interp_agg ag vals_pairs :: args_rest)).
             set (rs_k' := send_fact F rs_k).
             set (s2 := map snd l1 ++ rs_k' :: map snd l2).
             exists (map (add_waiting_fact F) s2).
             split.
             ++ eapply crt1n_trans_compose; [exact Hsteps1|].
                eapply Relation_Operators.rt1n_trans; [|apply rt1n_refl].
                apply (fire_normal_rule R_concl (interp_agg ag vals_pairs :: args_rest) s1 s2).
                cbv [stepWithLabel].
                exists l1, (nmr, k), rs_k, rs_k', l2.
                ssplit.
                { exact Hcomb. }
                { unfold s2. rewrite Hl1_snd, Hl2_snd. reflexivity. }
                { exact Hcdn. }
                { intros mf_args' num_c Hin_meta Hmatch.
                  apply Hno_conflict. exists mf_args', num_c. auto. }
                { reflexivity. }
             ++ simpl. cbv [knows_dfact]. apply Exists_exists.
                eexists. split.
                ** apply in_map_iff.
                   eexists. split; [reflexivity|].
                   rewrite Hs1_eq. apply in_or_app. right. left. reflexivity.
                ** cbv [rule_has_dfact add_waiting_fact]. simpl. right. left. reflexivity.
    - (* meta_rule_impl: ru = meta_rule rule_concls rule_hyps.
         f = meta_fact R args S.
         By Hp_meta_input + good_meta_rule_inputs, is_input R = false. *)
      rename hyps into hyps_facts.
      rename H into Hexists_meta_concl, H0 into Hforall2_meta_hyps, H1 into HS_def.
      rename R into R_concl, args into args_concl, S into S_set.
      (* ru = meta_rule rule_concls rule_hyps is in rules_of, so
         (rule_concls, rule_hyps) ∈ p.(meta_rules). *)
      assert (Hin_mr : In (rule_concls, rule_hyps) p.(meta_rules)).
      { cbv [rules_of] in Hin_r. apply in_app_or in Hin_r.
        destruct Hin_r as [Hin_meta | Hin_nm].
        - apply in_map_iff in Hin_meta.
          destruct Hin_meta as ((c, h) & Heq & Hin_mr). inversion Heq; subst. exact Hin_mr.
        - exfalso. apply in_map_iff in Hin_nm.
          destruct Hin_nm as (nmr & Heq & _). destruct nmr; discriminate. }
      (* is_input R_concl = false: derived from good_meta_rule_inputs *)
      assert (HR_noninput : is_input R_concl = false).
      { rewrite Forall_forall in Hp_meta_input.
        specialize (Hp_meta_input _ Hin_mr). simpl in Hp_meta_input.
        rewrite Forall_forall in Hp_meta_input.
        apply Exists_exists in Hexists_meta_concl.
        destruct Hexists_meta_concl as (c & Hin_c & Hint).
        cbv [interp_meta_clause] in Hint.
        destruct Hint as (mfa & mfs & _ & Heq).
        injection Heq as -> _ _.
        apply (Hp_meta_input _ Hin_c). }
      (* Goal: exists s', comp_step^* s s' /\ has_derived s' (meta_fact R_concl args_concl S_set).
         For non-input R: forall k_target, exists num, knows_dfact s' (meta_dfact ...). *)
      (* Strategy: induct on n = number of source rules to fire. *)
      assert (Hgoal_n : forall n, n <= length p.(non_meta_rules) ->
                exists s', comp_step^* s s' /\
                  (forall k, k < n ->
                     exists num, knows_dfact s' (meta_dfact R_concl args_concl (Some k) num))).
      { induction n as [|n IH]; intros Hn.
        - exists s. split; [apply rt1n_refl|]. intros k Hk. lia.
        - destruct (IH ltac:(lia)) as (s' & Hsteps_s' & Hk_lt_n).
          (* Fire fire_meta_rule at source n. Setup: *)
          assert (Hsane_s' : sane_state inputs s') by eauto using steps_preserves_sane.
          assert (Hlen_s_outer : length s = length p.(non_meta_rules))
            by (destruct Hsane as (Hl & _); exact Hl).
          assert (Hlen_s' : length s' = length p.(non_meta_rules)).
          { erewrite <- steps_preserves_length; eauto. }
          assert (Hn_lt_s' : n < length s') by lia.
          assert (Hn_lt_p : n < length p.(non_meta_rules)) by lia.
          destruct (nth_error p.(non_meta_rules) n) as [rn|] eqn:Hnth_rn;
            [|apply nth_error_None in Hnth_rn; lia].
          destruct (nth_error s' n) as [rs_n|] eqn:Hnth_rs_n;
            [|apply nth_error_None in Hnth_rs_n; lia].
          (* Apply flush_all_meta_hyps to get knows_datalog_fact on all hyps at rule n *)
          assert (Hmfc_s' : meta_facts_correct s') by eauto using steps_preserves_mfs_correct.
          assert (Hsound_s' : state_correct inputs s') by eauto using comp_steps_sound.
          assert (Hd_s' : Forall (has_derived_datalog_fact s') hyps_facts).
          { eapply Forall_impl; [|exact Hderived].
            intros f Hd. eapply steps_preserves_has_derived;
              [exact Hinp | exact Hsane | exact Hsteps_s' | exact Hd]. }
          (* prog_impl on each hyp via state_correct at s *)
          assert (Hpi_hyps : Forall (prog_impl rules_of (knows_datalog_fact inputs)) hyps_facts).
          { apply Forall_forall. intros h Hin.
            apply Hsound. split.
            - rewrite Forall_forall in Hderived. apply Hderived. exact Hin.
            - rewrite Forall_forall in Hcons. apply Hcons. exact Hin. }
          assert (Hpi_s' : Forall (prog_impl rules_of (knows_datalog_fact inputs)) hyps_facts)
            by exact Hpi_hyps.
          (* mf_consistent_state at s' via correct_impl_consistent *)
          assert (Hc_s' : Forall (mf_consistent_state s') hyps_facts).
          { apply Forall_forall. intros h Hin.
            eapply correct_impl_consistent.
            - exact Hinp.
            - lia.
            - exact Hsound_s'.
            - rewrite Forall_forall in Hpi_s'. apply Hpi_s'. exact Hin.
            - rewrite Forall_forall in Hd_s'. apply Hd_s'. exact Hin. }
          (* Each hyp from interp_meta_clause is a meta_fact *)
          assert (Hshape_s' : Forall (fun h => exists R mf_args mf_set, h = meta_fact R mf_args mf_set) hyps_facts).
          { apply Forall_forall. intros h Hin.
            apply In_nth_error in Hin. destruct Hin as (i & Hnth_h).
            destruct (nth_error rule_hyps i) as [c|] eqn:Hnth_c.
            - pose proof (Forall2_nth_error_fwd _ _ _ Hforall2_meta_hyps _ _ _ Hnth_c Hnth_h) as Hint.
              cbv [interp_meta_clause] in Hint.
              destruct Hint as (mfa & mfs & _ & Heq). subst h. eauto.
            - exfalso. apply nth_error_None in Hnth_c.
              apply nth_error_Some_bound_index in Hnth_h.
              apply Forall2_length in Hforall2_meta_hyps. lia. }
          pose proof (flush_all_meta_hyps inputs s' n hyps_facts
                       Hinp Hsane_s' Hmfc_s' Hsound_s' Hn_lt_s' ltac:(lia)
                       Hd_s' Hc_s' Hpi_s' Hshape_s')
            as (s'' & rs_n_post & Hsteps_flush & Hnth_rs_n_post & Hknow_hyps_post & Hiff_flush).
          assert (Hsane_s'' : sane_state inputs s'') by eauto using steps_preserves_sane.
          assert (Hsteps_total : comp_step^* s s'').
          { eapply crt1n_trans_compose; eassumption. }
          (* Build can_deduce_meta_fact and apply fire_meta_rule *)
          (* mf_cnt = matching count in rs_n_post.sent_facts *)
          destruct Hsane_s'' as (Hlen_s'' & _ & Hmf_sent_s'' & _ & Hcount_s'' & _ & _).
          (* Existsn count for matching in rs_n_post.sent: from Hcount *)
          pose proof (Hcount_s'' R_concl args_concl) as (msgs_sents_post & num_inp_post & Hf2_post & _ & _).
          assert (Hms_n_ex : exists ms_n, nth_error msgs_sents_post n = Some ms_n).
          { pose proof (Forall2_length Hf2_post) as Hl_post.
            destruct (nth_error msgs_sents_post n) as [mn|] eqn:Hnth_mn; [eauto|].
            apply nth_error_None in Hnth_mn.
            assert (Hn_lt_s'' : n < length s'') by
              (erewrite <- steps_preserves_length;
                [|exact Hinp|exact Hsane_s'|exact Hsteps_flush]; exact Hn_lt_s').
            lia. }
          destruct Hms_n_ex as (ms_n & Hms_n).
          pose proof (Forall2_nth_error_fwd _ _ _ Hf2_post _ _ _ Hnth_rs_n_post Hms_n) as Hex_sent.
          (* Apply fire_meta_rule *)
          assert (Hn_lt_s'' : n < length s'').
          { erewrite <- steps_preserves_length;
              [|exact Hinp|exact Hsane_s'|exact Hsteps_flush]. exact Hn_lt_s'. }
          pose proof Hnth_rs_n_post as Hnth_save.
          apply nth_error_split in Hnth_save.
          destruct Hnth_save as (s''_pre & s''_post & Hs''_eq & Hs''_pre_len).
          assert (Hk_seq : nth_error (seq 0 (length s'')) n = Some n).
          { rewrite nth_error_seq.
            assert (E : n <? length s'' = true) by (apply Nat.ltb_lt; lia).
            rewrite E. reflexivity. }
          set (labels := combine p.(non_meta_rules) (seq 0 (length s''))).
          assert (Hcomb_decomp : exists l1 l2,
                    combine labels s'' = l1 ++ ((rn, n), rs_n_post) :: l2 /\
                    map snd l1 = s''_pre /\ map snd l2 = s''_post /\
                    length l1 = n).
          { pose proof Hnth_rn as Hk_nmr_s.
            apply nth_error_split in Hk_nmr_s.
            destruct Hk_nmr_s as (nmrs_pre & nmrs_post & Hnmrs_eq & Hnmrs_pre_len).
            pose proof Hk_seq as Hk_seq_s.
            apply nth_error_split in Hk_seq_s.
            destruct Hk_seq_s as (seq_pre & seq_post & Hseq_eq & Hseq_pre_len).
            assert (Hlabels_split : labels =
                      combine nmrs_pre seq_pre ++ (rn, n) :: combine nmrs_post seq_post).
            { unfold labels. rewrite Hnmrs_eq, Hseq_eq.
              rewrite combine_app by lia. simpl. reflexivity. }
            assert (Hcc_pre_len : length (combine nmrs_pre seq_pre) = n).
            { rewrite length_combine. lia. }
            exists (combine (combine nmrs_pre seq_pre) s''_pre),
                   (combine (combine nmrs_post seq_post) s''_post).
            ssplit.
            - rewrite Hlabels_split, Hs''_eq.
              rewrite combine_app by lia. simpl. reflexivity.
            - apply map_combine_snd. lia.
            - apply map_combine_snd. rewrite length_combine.
              assert (Hpost_eq : length s''_post = length nmrs_post).
              { pose proof (f_equal (@length _) Hs''_eq) as Hl1.
                rewrite length_app in Hl1. simpl in Hl1.
                pose proof (f_equal (@length _) Hnmrs_eq) as Hl2.
                rewrite length_app in Hl2. simpl in Hl2. lia. }
              assert (Hpost_seq_eq : length seq_post = length nmrs_post).
              { pose proof (f_equal (@length _) Hseq_eq) as Hl3.
                rewrite length_app in Hl3. simpl in Hl3.
                rewrite length_seq in Hl3.
                pose proof (f_equal (@length _) Hnmrs_eq) as Hl2.
                rewrite length_app in Hl2. simpl in Hl2. lia. }
              lia.
            - rewrite length_combine. lia. }
          destruct Hcomb_decomp as (l1 & l2 & Hcomb & Hl1_snd & Hl2_snd & Hl1_len).
          (* Define the new meta_dfact and target state *)
          set (new_fact := meta_dfact R_concl args_concl (Some n) ms_n).
          set (rs_n_post' := send_fact new_fact rs_n_post).
          set (s2 := map snd l1 ++ rs_n_post' :: map snd l2).
          exists (map (add_waiting_fact new_fact) s2).
          split.
          { eapply crt1n_trans_compose; [exact Hsteps_total|].
            eapply Relation_Operators.rt1n_trans; [|apply rt1n_refl].
            apply (fire_meta_rule rule_concls rule_hyps hyps_facts new_fact s'' s2 Hin_mr).
            cbv [stepWithLabel].
            exists l1, (rn, n), rs_n_post, rs_n_post', l2.
            ssplit.
            { exact Hcomb. }
            { unfold s2. rewrite Hl1_snd, Hl2_snd. reflexivity. }
            (* The step function evaluated: can_deduce_meta_fact + Forall + send_fact *)
            { (* can_deduce_meta_fact *)
              cbv [can_deduce_meta_fact].
              (* Extract ctx and c from Hexists_meta_concl *)
              apply Exists_exists in Hexists_meta_concl.
              destruct Hexists_meta_concl as (c & Hin_c & Hint_c).
              cbv [interp_meta_clause] in Hint_c.
              destruct Hint_c as (mfa & mfs & Hf2_args & Heq_meta).
              injection Heq_meta as Hrel Hmfa _.
              exists ctx, R_concl, args_concl, ms_n. ssplit.
              - reflexivity.
              - exact Hex_sent.
              - apply Exists_exists. exists c. split; [exact Hin_c|].
                cbv [interp_meta_clause]. exists args_concl, (fun _ => False).
                split.
                + rewrite Hmfa. exact Hf2_args.
                + rewrite Hrel. reflexivity.
              - exact Hforall2_meta_hyps.
              - (* Forcing clause: forall nf_args, can_deduce_normal_fact rn rs_n_post.known
                   R_concl nf_args -> matches args_concl nf_args ->
                   In (normal_dfact R_concl nf_args) rs_n_post.known *)
                admit. (* Forcing clause: requires "closure" at rs_n_post.known *) }
            { exact Hknow_hyps_post. }
            { reflexivity. } }
          { (* has_derived part *)
            intros k Hk_lt.
            destruct (Nat.eq_dec k n) as [Heq | Hneq].
            - (* k = n: emit the new meta_dfact *)
              subst k. exists ms_n.
              cbv [knows_dfact]. apply Exists_exists.
              eexists. split.
              + apply in_map_iff. eexists. split; [reflexivity|].
                unfold s2. apply in_or_app. right. left. reflexivity.
              + cbv [rule_has_dfact add_waiting_fact]. simpl.
                right. left. reflexivity.
            - (* k < n: from IH *)
              assert (Hk_lt_n_orig : k < n) by lia.
              specialize (Hk_lt_n k Hk_lt_n_orig) as (num & Hk_knows).
              exists num.
              (* knows_dfact preserved across comp_step^* *)
              eapply steps_preserves_knows_dfact;
                [exact Hinp | exact Hsane_s' | | exact Hk_knows].
              eapply crt1n_trans_compose; [exact Hsteps_flush|].
              eapply Relation_Operators.rt1n_trans; [|apply rt1n_refl].
              apply (fire_meta_rule rule_concls rule_hyps hyps_facts new_fact s'' s2 Hin_mr).
              cbv [stepWithLabel].
              exists l1, (rn, n), rs_n_post, rs_n_post', l2.
              ssplit.
              { exact Hcomb. }
              { unfold s2. rewrite Hl1_snd, Hl2_snd. reflexivity. }
              { admit. (* same as above *) }
              { exact Hknow_hyps_post. }
              { reflexivity. } } }
      specialize (Hgoal_n (length p.(non_meta_rules)) ltac:(lia)).
      destruct Hgoal_n as (s' & Hsteps & Hknows_all).
      exists s'. split; [exact Hsteps|].
      cbv [has_derived_datalog_fact]. rewrite HR_noninput.
      intros k Hk_lt. apply Hknows_all. exact Hk_lt.
  Admitted.

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
    state_correct inputs s ->
    state_complete inputs s.
  Proof.
    intros Hinp Hlen Hsane Hmfc Hsound f Himpl.
    set (R := fun (f0 : fact) =>
                forall s0,
                  sane_state inputs s0 ->
                  meta_facts_correct s0 ->
                  state_correct inputs s0 ->
                  exists s', comp_step^* s0 s' /\ has_derived_datalog_fact s' f0).
    enough (HR : R f).
    { apply HR; assumption. }
    revert f Himpl.
    apply prog_impl_ind.
    - (* base case: knows_datalog_fact inputs f *)
      intros f0 Hkdf s0 Hsane0 Hmfc0 Hsound0.
      exists s0. split; [apply rt1n_refl|].
      eapply knows_datalog_fact_inputs_has_derived; eassumption.
    - (* step case *)
      intros f0 hyps Hexists Hforall_pi Hforall_R s0 Hsane0 Hmfc0 Hsound0.
      apply Exists_exists in Hexists.
      destruct Hexists as (ru & Hin_r & Hrule_impl).
      (* Apply compose_completion to get s1 reachable with Forall has_derived s1 hyps *)
      pose proof (compose_completion inputs s0 hyps Hinp Hsane0 Hmfc0 Hsound0 Hforall_R)
        as (s1 & Hsteps1 & Hderived1).
      assert (Hsane1 : sane_state inputs s1) by eauto using steps_preserves_sane.
      assert (Hmfc1 : meta_facts_correct s1) by eauto using steps_preserves_mfs_correct.
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
                    Hinp Hsane1 Hmfc1 Hsound1 Hin_r Hrule_impl Hderived1 Hcons1)
        as (s2 & Hsteps2 & Hderived2).
      exists s2. split; [|exact Hderived2].
      eapply crt1n_trans_compose; eassumption.
  Qed.

End __.
