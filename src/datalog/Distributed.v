From Stdlib Require Import List Permutation RelationClasses Classical_Prop Lia.
From coqutil Require Import Datatypes.List.
From Datalog Require Import Datalog Node Graph Smallstep List Map Tactics.
From coqutil Require Import Map.Interface Tactics Tactics.fwd.
Import ListNotations.

Section Distributed.
  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.

  Context (R_senders : rel -> list node_name).
  Context (R_senders_NoDup : forall R, NoDup (R_senders R)).

  Context (rel_input_allowed : node_id -> rel -> bool).
  Context (rel_forward : node_id -> node_id -> rel -> bool).
  Context (rel_visible : node_id -> rel -> bool).

  Definition input_allowed n (f : dfact) := rel_input_allowed n (dfact_rel f).
  Definition forward n1 n2 (f : dfact) := rel_forward n1 n2 (dfact_rel f).
  Definition output_visible n (f : dfact) := rel_visible n (dfact_rel f).

  Lemma output_visible_equiv n a b :
    dfact_equiv a b ->
    output_visible n a = output_visible n b.
  Proof.
    intros Heq. unfold output_visible. f_equal.
    destruct a, b; simpl in Heq; fwd; congruence || reflexivity.
  Qed.

  Lemma forward_equiv n1 n2 a b :
    dfact_equiv a b ->
    forward n1 n2 a = forward n1 n2 b.
  Proof.
    intros Heq. unfold forward. f_equal.
    destruct a, b; simpl in Heq; fwd; congruence || reflexivity.
  Qed.

  (* The graph runs one node program [np] replicated across nodes. *)
  Context (np : node_prog).
  Context (Hmrv : meta_rules_valid np.(np_rules)).

  Local Notation nstep := (node_step R_senders np).
  Local Notation nallowed := (allowed_inputs R_senders).

  #[local] Instance nequiv_equiv : Equivalence dfact_equiv.
  Proof.
    constructor.
    - intros f. apply dfact_equiv_refl.
    - intros f1 f2. apply dfact_equiv_sym.
    - intros [R1 a1 | R1 m1 s1 c1] [R2 a2 | R2 m2 s2 c2] [R3 a3 | R3 m3 s3 c3] H12 H23;
        cbn [dfact_equiv] in *; try congruence.
      destruct H12 as (-> & -> & ->), H23 as (-> & -> & ->). repeat split.
  Qed.

  Definition stmt : Type := (rel * list (option T))%type.

  Definition claim (s : stmt) (l : list dfact) :=
    let '(R, mf_args) := s in
    forall src, In src (R_senders R) ->
      exists cnt, In (meta_dfact R mf_args src cnt) l.

  Lemma claim_mono s ms1 ms2 :
    claim s ms1 -> incl_mod dfact_equiv ms1 ms2 -> claim s ms2.
  Proof.
    cbv [claim]. intros H Hincl. fwd.
    intros. especialize H; eauto. fwd.
    cbv [incl_mod] in Hincl. especialize Hincl; eauto. fwd.
    cbv [dfact_equiv] in Hinclp1. fwd. eauto.
  Qed.

  Definition claim_output (s : stmt) (n : option node_id) (fs : list dfact) : Prop :=
    let '(R, mf_args) := s in
    In n (R_senders R) -> exists cnt, In (meta_dfact R mf_args n cnt) fs.

  Definition consistent_output (s : stmt) (n : option node_id) (fs : list dfact) : Prop :=
    let '(R, mf_args) := s in
    In n (R_senders R) ->
    exists cnt, In (meta_dfact R mf_args n cnt) fs /\
      Existsn_ge (dfact_matches R mf_args) cnt fs.

  Definition allowed_output (n : option node_id) (fs : list dfact) : Prop :=
    (forall R mf_args src cnt,
       In (meta_dfact R mf_args src cnt) fs ->
       n = src /\ Existsn_le (dfact_matches R mf_args) cnt fs) /\
    (forall f, In f fs -> In n (R_senders (dfact_rel f))).

  Definition consistent (s : stmt) (l : list dfact) : Prop :=
    let '(R, mf_args) := s in
    exists num, expect_num_R_facts R_senders R mf_args l num /\
      Existsn_ge (dfact_matches R mf_args) num l.

  Lemma consistent_mono s ms1 ms2 :
    consistent s ms1 -> submultiset ms1 ms2 -> consistent s ms2.
  Proof.
    destruct s as [R mf_args].
    intros (num & (ems & Hf2 & Hnum) & Hge) Hsub.
    pose proof (submultiset_incl _ _ Hsub) as Hincl.
    exists num. split.
    - exists ems. split; [ | exact Hnum ].
      eapply Forall2_impl; [ | exact Hf2 ]. intros k e Hin. exact (Hincl _ Hin).
    - eapply Existsn_ge_submultiset; [ exact Hge | exact Hsub ].
  Qed.

  Lemma consistent_output_mono s n ms1 ms2 :
    consistent_output s n ms1 -> submultiset ms1 ms2 -> consistent_output s n ms2.
  Proof.
    destruct s as [R mf_args].
    intros Hco Hsub Hn.
    destruct (Hco Hn) as (cnt & Hin & Hge).
    pose proof (submultiset_incl _ _ Hsub) as Hincl.
    exists cnt. split; [ apply Hincl; exact Hin | ].
    eapply Existsn_ge_submultiset; [ exact Hge | exact Hsub ].
  Qed.

  Lemma allowed_output_submultiset n : multiset_monotone_dec (allowed_output n).
  Proof.
    intros l1 l2 (Hmeta2 & Hsender2) Hsub.
    pose proof (submultiset_incl _ _ Hsub) as Hincl.
    split; [ | intros f Hin; apply Hsender2, Hincl, Hin ].
    intros R mf_args src cnt Hin.
    destruct (Hmeta2 R mf_args src cnt (Hincl _ Hin)) as (Hsrc & Hle2).
    split; [ exact Hsrc | ].
    eapply Existsn_le_submultiset; [ exact Hle2 | exact Hsub ].
  Qed.

  Lemma Forall2_In_combine {A B} (R : A -> B -> Prop) xs ys x y :
    Forall2 R xs ys -> In (x, y) (combine xs ys) -> R x y.
  Proof.
    induction 1 as [| a b xs' ys' Hab HF IH]; simpl; [ contradiction | ].
    intros [Heq | Hin]; [ injection Heq as -> ->; exact Hab | exact (IH Hin) ].
  Qed.

  Lemma In_concat_pair {A B} (xs : list A) (yss : list (list B)) y :
    length xs = length yss ->
    In y (concat yss) ->
    exists x ys, In (x, ys) (combine xs yss) /\ In y ys.
  Proof.
    revert xs. induction yss as [| ys yss' IH]; intros xs Hlen Hin; [ destruct Hin | ].
    destruct xs as [| x xs']; [ discriminate Hlen | ].
    simpl in Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    - exists x, ys. split; [ left; reflexivity | exact Hin ].
    - simpl in Hlen. injection Hlen as Hlen.
      destruct (IH xs' Hlen Hin) as (x' & ys' & Hcomb & Hin').
      exists x', ys'. split; [ right; exact Hcomb | exact Hin' ].
  Qed.

  Lemma meta_locate R mf_args nodes mss n cnt :
    Forall2 allowed_output nodes mss ->
    In (meta_dfact R mf_args n cnt) (concat mss) ->
    exists ms, In (n, ms) (combine nodes mss) /\ In (meta_dfact R mf_args n cnt) ms.
  Proof.
    intros HF Hin.
    edestruct (In_concat_pair nodes mss) as (n' & ms & Hcomb & Hin');
      [ eapply Forall2_length; exact HF | exact Hin | ].
    pose proof (Forall2_In_combine _ _ _ _ _ HF Hcomb) as (Hm' & _).
    destruct (Hm' _ _ _ _ Hin') as (Hsrc & _). subst n'.
    exists ms. split; [ exact Hcomb | exact Hin' ].
  Qed.

  Lemma meta_in_head_block R mf_args n0 ms0 nodes' mss' cnt :
    Forall2 allowed_output nodes' mss' ->
    ~ In n0 nodes' ->
    In (meta_dfact R mf_args n0 cnt) (ms0 ++ concat mss') ->
    In (meta_dfact R mf_args n0 cnt) ms0.
  Proof.
    intros HF Hn0notin Hmeta0.
    apply in_app_or in Hmeta0. destruct Hmeta0 as [H | H]; [ exact H | exfalso ].
    destruct (meta_locate _ _ _ _ _ _ HF H) as (ms' & Hcomb & _).
    apply Hn0notin. eapply in_combine_l; exact Hcomb.
  Qed.

  Lemma meta_not_in_block R mf_args n0 ms0 k e mss' :
    allowed_output n0 ms0 ->
    k <> n0 ->
    In (meta_dfact R mf_args k e) (ms0 ++ concat mss') ->
    In (meta_dfact R mf_args k e) (concat mss').
  Proof.
    intros (Hmeta & _) Hne Hin. apply in_app_or in Hin.
    destruct Hin as [Hin | Hin]; [ | exact Hin ].
    destruct (Hmeta _ _ _ _ Hin) as (Hsrc & _). congruence.
  Qed.

  Lemma Forall2_meta_shift R mf_args n0 ms0 mss' senders ems :
    allowed_output n0 ms0 ->
    ~ In n0 senders ->
    Forall2 (fun k e => In (meta_dfact R mf_args k e) (ms0 ++ concat mss')) senders ems ->
    Forall2 (fun k e => In (meta_dfact R mf_args k e) (concat mss')) senders ems.
  Proof.
    intros Hao Hnin HF. induction HF as [| k e senders' ems' Hin HF IH]; constructor.
    - eapply meta_not_in_block; [ exact Hao | | exact Hin ].
      intros ->. apply Hnin. left. reflexivity.
    - apply IH. intros Hin'. apply Hnin. right. exact Hin'.
  Qed.

  Lemma cover_shift (R : rel) (mf_args : list (option T))
        (n0 : node_name) (ms0 : list dfact)
        (nodes' : list node_name) (mss' : list (list dfact))
        (s1 s2 : list node_name) :
    ~ In n0 nodes' ->
    (forall n ms f, In (n, ms) ((n0, ms0) :: combine nodes' mss') ->
                    In f ms -> dfact_matches R mf_args f -> In n (s1 ++ n0 :: s2)) ->
    forall n ms f, In (n, ms) (combine nodes' mss') ->
                   In f ms -> dfact_matches R mf_args f -> In n (s1 ++ s2).
  Proof.
    intros Hn0notin Hcover n ms f Hcomb Hf Hmatch.
    assert (Hne : n <> n0) by (intros ->; apply Hn0notin; eapply in_combine_l; exact Hcomb).
    pose proof (Hcover n ms f (or_intror Hcomb) Hf Hmatch) as Hin_s.
    apply in_app_or in Hin_s. apply in_or_app.
    destruct Hin_s as [H | [H | H]]; [ left; exact H | congruence | right; exact H ].
  Qed.

  Lemma scatter (Q : node_name -> list dfact -> nat -> Prop) :
    forall (nodes : list node_name) (mss : list (list dfact)),
      length nodes = length mss -> NoDup nodes ->
    forall (senders : list node_name) (ems : list nat), NoDup senders ->
      (forall n ms, In (n, ms) (combine nodes mss) -> ~ In n senders -> Q n ms 0) ->
      Forall2 (fun k e => exists ms, In (k, ms) (combine nodes mss) /\ Q k ms e) senders ems ->
      exists bes, list_sum bes = list_sum ems /\ Forall3 Q nodes mss bes.
  Proof.
    induction nodes as [| n0 nodes' IH]; intros mss Hlen Hnd senders ems Hnds Hdef HF.
    - destruct mss as [| ms0 mss0]; [ | discriminate Hlen ].
      inversion HF as [| k e sl el Hhead Htl]; subst.
      + exists []. split; [ reflexivity | constructor ].
      + destruct Hhead as (ms & [] & _).
    - destruct mss as [| ms0 mss']; [ discriminate Hlen | ].
      cbn [length] in Hlen. injection Hlen as Hlen.
      apply NoDup_cons_iff in Hnd. destruct Hnd as (Hn0notin & Hnd').
      assert (Hshift : forall k e, k <> n0 ->
                (exists ms, In (k, ms) ((n0, ms0) :: combine nodes' mss') /\ Q k ms e) ->
                exists ms, In (k, ms) (combine nodes' mss') /\ Q k ms e).
      { intros k e Hne (ms & Hin & Hq). exists ms. split; [ | exact Hq ].
        destruct Hin as [E | Htail]; [ inversion E; congruence | exact Htail ]. }
      assert (Hne_nodes : forall n ms, In (n, ms) (combine nodes' mss') -> n <> n0)
        by (intros n ms Hcomb ->; apply Hn0notin; eapply in_combine_l; exact Hcomb).
      destruct (classic (In n0 senders)) as [Hin0 | Hnin0].
      + apply in_split in Hin0. destruct Hin0 as (s1 & s2 & ->).
        apply Forall2_app_inv_l in HF. destruct HF as (e1 & ems2 & He1 & Hems2 & ->).
        destruct ems2 as [| e0 e2]; [ solve [ inversion Hems2 ] | ].
        inversion Hems2 as [| ? ? ? ? Hhead He2]; subst.
        destruct Hhead as (ms & Hinms & Hq0).
        assert (ms = ms0)
          by (destruct Hinms as [E | Htail];
              [ inversion E; reflexivity
              | exfalso; apply Hn0notin; eapply in_combine_l; exact Htail ]).
        subst ms.
        pose proof (NoDup_remove_1 _ _ _ Hnds) as Hnds'.
        pose proof (NoDup_remove_2 _ _ _ Hnds) as Hn0notin_s.
        assert (HFtail : Forall2 (fun k e => exists ms, In (k, ms) (combine nodes' mss') /\ Q k ms e)
                                 (s1 ++ s2) (e1 ++ e2)).
        { apply Forall2_app.
          - eapply Forall2_impl_strong; [ | exact He1 ]. intros k e Hp Hk _.
            eapply Hshift; [ intros ->; apply Hn0notin_s; apply in_or_app; left; exact Hk | exact Hp ].
          - eapply Forall2_impl_strong; [ | exact He2 ]. intros k e Hp Hk _.
            eapply Hshift; [ intros ->; apply Hn0notin_s; apply in_or_app; right; exact Hk | exact Hp ]. }
        assert (Hdef' : forall n ms, In (n, ms) (combine nodes' mss') -> ~ In n (s1 ++ s2) -> Q n ms 0).
        { intros n ms Hcomb Hnin. apply Hdef; [ right; exact Hcomb | ].
          intros Hin. apply in_app_or in Hin. apply Hnin.
          destruct Hin as [H | [H | H]];
            [ apply in_or_app; left; exact H
            | exfalso; exact (Hne_nodes _ _ Hcomb (eq_sym H))
            | apply in_or_app; right; exact H ]. }
        destruct (IH mss' Hlen Hnd' (s1 ++ s2) (e1 ++ e2) Hnds' Hdef' HFtail)
          as (bes & Hbes & HF3).
        exists (e0 :: bes). split.
        * rewrite list_sum_app in Hbes.
          rewrite (list_sum_cons e0 bes), (list_sum_app e1 (e0 :: e2)), (list_sum_cons e0 e2). lia.
        * constructor; assumption.
      + assert (HFtail : Forall2 (fun k e => exists ms, In (k, ms) (combine nodes' mss') /\ Q k ms e)
                                 senders ems).
        { eapply Forall2_impl_strong; [ | exact HF ]. intros k e Hp Hk _.
          eapply Hshift; [ intros ->; exact (Hnin0 Hk) | exact Hp ]. }
        assert (Hdef' : forall n ms, In (n, ms) (combine nodes' mss') -> ~ In n senders -> Q n ms 0)
          by (intros n ms Hcomb Hnin; apply Hdef; [ right; exact Hcomb | exact Hnin ]).
        destruct (IH mss' Hlen Hnd' senders ems Hnds Hdef' HFtail) as (bes & Hbes & HF3).
        exists (0 :: bes). split.
        * rewrite list_sum_cons. lia.
        * constructor; [ apply Hdef; [ left; reflexivity | exact Hnin0 ] | exact HF3 ].
  Qed.

  Lemma allowed_of_outputs nodes mss :
    NoDup nodes -> Forall2 allowed_output nodes mss -> nallowed (concat mss).
  Proof.
    intros Hnd HF2 R mf_args ems Hems.
    assert (Hdef : forall n ms, In (n, ms) (combine nodes mss) -> ~ In n (R_senders R) ->
                     Existsn_le (dfact_matches R mf_args) 0 ms).
    { intros n ms Hcomb Hnin. apply Existsn_le_0_Forall_not. apply Forall_forall.
      intros f Hf Hmatch. apply Hnin.
      pose proof (Forall2_In_combine _ _ _ _ _ HF2 Hcomb) as (_ & Hsend).
      destruct Hmatch as (nf_args & -> & _). exact (Hsend _ Hf). }
    assert (Hin : Forall2 (fun k e => exists ms, In (k, ms) (combine nodes mss) /\
                    Existsn_le (dfact_matches R mf_args) e ms) (R_senders R) ems).
    { eapply Forall2_impl; [ | exact Hems ]. intros k e Hmeta.
      destruct (meta_locate _ _ _ _ _ _ HF2 Hmeta) as (ms & Hcomb & Hin_ms).
      exists ms. split; [ exact Hcomb | ].
      pose proof (Forall2_In_combine _ _ _ _ _ HF2 Hcomb) as (Hall & _).
      destruct (Hall _ _ _ _ Hin_ms) as (_ & Hle). exact Hle. }
    destruct (scatter _ nodes mss ltac:(eapply Forall2_length; exact HF2) Hnd
                (R_senders R) ems (R_senders_NoDup R) Hdef Hin) as (bes & Hbes & HF3).
    rewrite <- Hbes. apply Existsn_le_concat.
    apply Forall3_ignore1 in HF3.
    eapply Forall2_impl; [ | exact HF3 ]. intros ms e (n & Hle). exact Hle.
  Qed.

  Lemma combine_l_unique {X Y} (xs : list X) (ys : list Y) x y1 y2 :
    NoDup xs -> In (x, y1) (combine xs ys) -> In (x, y2) (combine xs ys) -> y1 = y2.
  Proof.
    revert ys. induction xs as [| x0 xs' IH]; intros ys Hnd H1 H2; [ destruct H1 | ].
    destruct ys as [| y0 ys']; [ destruct H1 | ].
    cbn [combine] in H1, H2. apply NoDup_cons_iff in Hnd. destruct Hnd as (Hnotin & Hnd').
    destruct H1 as [E1 | H1].
    - inversion E1; subst.
      destruct H2 as [E2 | H2]; [ inversion E2; subst; reflexivity | ].
      exfalso. apply Hnotin. eapply in_combine_l; exact H2.
    - destruct H2 as [E2 | H2].
      + inversion E2; subst. exfalso. apply Hnotin. eapply in_combine_l; exact H1.
      + exact (IH ys' Hnd' H1 H2).
  Qed.

  Lemma meta_in_own_block R mf_args nodes mss n ms cnt :
    Forall2 allowed_output nodes mss ->
    NoDup nodes ->
    In (n, ms) (combine nodes mss) ->
    In (meta_dfact R mf_args n cnt) (concat mss) ->
    In (meta_dfact R mf_args n cnt) ms.
  Proof.
    intros HF2 Hnd Hcomb Hin.
    destruct (meta_locate _ _ _ _ _ _ HF2 Hin) as (ms' & Hcomb' & Hin').
    assert (ms = ms') by (eapply combine_l_unique; [ exact Hnd | exact Hcomb | exact Hcomb' ]).
    subst ms'. exact Hin'.
  Qed.

  Lemma consistent_good_holds :
    consistent_good claim claim_output consistent_output allowed_output consistent.
  Proof.
    intros [R mf_args] nodes mss Hnd HF2 Hclaim. cbn [claim] in Hclaim.
    assert (Hlen : length nodes = length mss) by (eapply Forall2_length; exact HF2).
    split.
    - apply (Forall_combine_Forall2 (fun p => claim_output (R, mf_args) (fst p) (snd p)));
        [ | exact Hlen ].
      apply Forall_forall. intros [n ms] Hcomb. cbn [fst snd claim_output]. intros Hn.
      destruct (Hclaim n Hn) as (cnt & Hin).
      exists cnt. eapply meta_in_own_block; [ exact HF2 | exact Hnd | exact Hcomb | exact Hin ].
    - split.
      + intros (num & (ems & Hexpect & Hnum) & Hge). subst num.
        assert (Hdef : forall n ms, In (n, ms) (combine nodes mss) -> ~ In n (R_senders R) ->
                  Existsn_le (dfact_matches R mf_args) 0 ms /\
                  (In n (R_senders R) -> In (meta_dfact R mf_args n 0) ms)).
        { intros n ms Hcomb Hnin. split; [ | intros HH; contradiction ].
          apply Existsn_le_0_Forall_not. apply Forall_forall. intros f Hf Hmatch. apply Hnin.
          pose proof (Forall2_In_combine _ _ _ _ _ HF2 Hcomb) as (_ & Hsend).
          destruct Hmatch as (nf_args & -> & _). exact (Hsend _ Hf). }
        assert (Hin : Forall2 (fun k e => exists ms, In (k, ms) (combine nodes mss) /\
                  (Existsn_le (dfact_matches R mf_args) e ms /\
                   (In k (R_senders R) -> In (meta_dfact R mf_args k e) ms))) (R_senders R) ems).
        { eapply Forall2_impl; [ | exact Hexpect ]. intros k e Hmeta.
          destruct (meta_locate _ _ _ _ _ _ HF2 Hmeta) as (ms & Hcomb & Hin_ms).
          exists ms. split; [ exact Hcomb | ].
          pose proof (Forall2_In_combine _ _ _ _ _ HF2 Hcomb) as (Hall & _).
          destruct (Hall _ _ _ _ Hin_ms) as (_ & Hle).
          split; [ exact Hle | intros _; exact Hin_ms ]. }
        destruct (scatter _ nodes mss Hlen Hnd (R_senders R) ems (R_senders_NoDup R) Hdef Hin)
          as (bes & Hbes & HF3).
        assert (Hle_all : Forall2 (fun ms e => Existsn_le (dfact_matches R mf_args) e ms) mss bes).
        { pose proof HF3 as Hp. apply Forall3_ignore1 in Hp.
          eapply Forall2_impl; [ | exact Hp ]. intros ms e (n & Hle & _). exact Hle. }
        assert (Hge' : Existsn_ge (dfact_matches R mf_args) (list_sum bes) (concat mss))
          by (rewrite Hbes; exact Hge).
        pose proof (Existsn_squeeze _ _ _ Hge' Hle_all) as Hge_all.
        pose proof (Forall3_Forall2_conj _ _ _ _ _ HF3 Hge_all) as HF3'.
        apply Forall3_ignore3 in HF3'.
        eapply Forall2_impl; [ | exact HF3' ].
        intros n ms (e & (Hle & Hmeta) & Hge_e). cbn [consistent_output]. intros Hn.
        exists e. split; [ exact (Hmeta Hn) | exact Hge_e ].
      + intros HcoF.
        assert (Hbuild : Forall (fun k => exists e, exists ms,
                    In (k, ms) (combine nodes mss) /\
                    In (meta_dfact R mf_args k e) ms /\
                    Existsn_ge (dfact_matches R mf_args) e ms) (R_senders R)).
        { apply Forall_forall. intros k Hk.
          destruct (Hclaim k Hk) as (cnt & Hin).
          destruct (meta_locate _ _ _ _ _ _ HF2 Hin) as (ms & Hcomb & _).
          pose proof (Forall2_In_combine _ _ _ _ _ HcoF Hcomb) as Hco.
          cbn [consistent_output] in Hco. destruct (Hco Hk) as (cnt2 & Hin2 & Hge2).
          exists cnt2, ms.
          split; [ exact Hcomb | split; [ exact Hin2 | exact Hge2 ] ]. }
        apply Forall_exists_r_Forall2 in Hbuild. destruct Hbuild as (ems & Hbuild2).
        exists (list_sum ems). split.
        * exists ems. split; [ | reflexivity ].
          eapply Forall2_impl; [ | exact Hbuild2 ].
          intros k e (ms & Hcomb & Hinms & _).
          apply in_concat. exists ms. split; [ eapply in_combine_r; exact Hcomb | exact Hinms ].
        * assert (Hdef : forall n ms, In (n, ms) (combine nodes mss) -> ~ In n (R_senders R) ->
                    Existsn_ge (dfact_matches R mf_args) 0 ms) by (intros; apply Eg_zero).
          assert (Hin : Forall2 (fun k e => exists ms, In (k, ms) (combine nodes mss) /\
                    Existsn_ge (dfact_matches R mf_args) e ms) (R_senders R) ems).
          { eapply Forall2_impl; [ | exact Hbuild2 ].
            intros k e (ms & Hcomb & _ & Hge). exists ms. split; [ exact Hcomb | exact Hge ]. }
          destruct (scatter _ nodes mss Hlen Hnd (R_senders R) ems (R_senders_NoDup R) Hdef Hin)
            as (bes & Hbes & HF3).
          rewrite <- Hbes. apply Existsn_ge_concat.
          apply Forall3_ignore1 in HF3.
          eapply Forall2_impl; [ | exact HF3 ]. intros ms e (n & Hge). exact Hge.
  Qed.

  Context {graph_state : map.map node_id (@graph_node_state dfact dfact_mod_count node_state)}.
  Context {graph_state_ok : map.ok graph_state}.
  Context (initial_gs : graph_state).
  Context (initial_gs_empty :
             forall n gns, map.get initial_gs n = Some gns ->
                           gns.(gns_trace) = [] /\ gns.(gns_queue) = []).
  Context (initial_gs_node_init :
             forall n gns, map.get initial_gs n = Some gns ->
                           gns.(gns_node_state) = node_init).

  Lemma nallowed_multiset_monotone : multiset_monotone_dec nallowed.
  Proof. intros l1 l2 Hl2 Hsub. eapply allowed_inputs_submultiset; eauto. Qed.

  Lemma nstep_input_total : input_total nstep.
  Proof. intros s m. eexists. apply node_input_step. Qed.

  Lemma nodes_good_holds :
    Forall_map (node_good forward dfact_equiv claim claim_output consistent_output allowed_output
                          consistent nallowed nstep) initial_gs.
  Admitted.

  Local Notation gstep := (graph_step input_allowed forward output_visible nstep).
  Local Notation gia := (graph_inputs_allowed allowed_output).

  Theorem distributed_might_implies_will
          (t : list (IO_event (@graph_label dfact dfact_mod_count) (dfact * node_id)))
          (gs : graph_state) (o : dfact * node_id) :
    star gstep initial_gs t gs ->
    gia (inputs_of t) ->
    might_output gstep gs t o ->
    will_output_equiv gstep (graph_equiv dfact_equiv) gia gs t o.
  Proof.
    intros.
    eapply graph_might_implies_will; try eassumption.
    - exact nequiv_equiv.
    - exact output_visible_equiv.
    - exact forward_equiv.
    - exact claim_mono.
    - exact consistent_mono.
    - exact consistent_output_mono.
    - exact consistent_good_holds.
    - exact nallowed_multiset_monotone.
    - exact allowed_output_submultiset.
    - exact allowed_of_outputs.
    - exact nstep_input_total.
    - exact nodes_good_holds.
  Qed.

End Distributed.
