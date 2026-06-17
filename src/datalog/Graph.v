From coqutil Require Import Map.Interface.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
From Stdlib Require Import List PeanoNat.
From Datalog Require Import Smallstep Map.
Import ListNotations.

Definition node_id := nat.
Section __.
  Context {message : Type}.
  Context (input_allowed : node_id -> message -> bool).
  Context (forward : node_id -> message -> list node_id).
  Context (output_visible : node_id -> message -> bool).

  Section graph.
    Context {node_prog : Type} {graph_prog : map.map node_id node_prog}.
    Context {node_state : Type} {node_states : map.map node_id node_state}.
    Context (p : graph_prog).

    Variant IO_event :=
      | I_event (_ : message)
      | O_event (_ : list message).

    Context (node_step : node_prog -> node_state -> IO_event -> node_state -> Prop).

    Record graph_state :=
      { g_nodes : node_states;
        g_messages : list (node_id (*destination*) * message) }.

    Inductive graph_step : graph_state -> IO_event -> graph_state -> Prop :=
    | gstep_input gs n m :
      input_allowed n m = true ->
      graph_step gs (I_event m)
                 {| g_nodes := gs.(g_nodes);
                   g_messages := (n, m) :: gs.(g_messages) |}
    | gstep_run gs n np ns ns' outs :
      map.get p n = Some np ->
      map.get gs.(g_nodes) n = Some ns ->
      node_step np ns (O_event outs) ns' ->
      graph_step gs (O_event (filter (output_visible n) outs))
                 {| g_nodes := map.put gs.(g_nodes) n ns';
                   g_messages := gs.(g_messages) ++
                                      flat_map (fun m => map (fun n' => (n', m)) (forward n m))
                                      outs |}
    | gstep_receive gs n np ns ns' m ms1 ms2 :
      map.get p n = Some np ->
      map.get gs.(g_nodes) n = Some ns ->
      node_step np ns (I_event m) ns' ->
      gs.(g_messages) = ms1 ++ (n, m) :: ms2 ->
      graph_step gs (O_event [])
                 {| g_nodes := map.put gs.(g_nodes) n ns';
                   g_messages := ms1 ++ ms2 |}.
  End graph.

  Context (A : list message -> message -> Prop).

  Definition inputs_of (t : list IO_event) :=
    flat_map (fun e => match e with I_event m => [m] | _ => [] end) t.

  Definition output_in_trace (output : message) (t : list IO_event) :=
    exists outs, In (O_event outs) t /\ In output outs.

  Definition event_guaranteed (e : IO_event) :=
    match e with
    | O_event _ => True
    | I_event _ => False
    end.

  Definition allowed_IO_event (t : list IO_event) (e : IO_event) :=
    match e with
    | O_event _ => True
    | I_event inp => A (inputs_of t) inp
    end.

  Definition allowed_trace t :=
    forall t1 e t2,
      t = t2 ++ e :: t1 ->
      allowed_IO_event t1 e.

  Lemma output_in_trace_app o (l1 l2 : list IO_event) :
    output_in_trace o (l1 ++ l2) <-> output_in_trace o l1 \/ output_in_trace o l2.
  Proof.
    unfold output_in_trace; split.
    - intros (outs & Hin & Hino).
      apply in_app_or in Hin as [Hin|Hin]; [left|right]; eauto.
    - intros [(outs & Hin & Hino)|(outs & Hin & Hino)];
        exists outs; (split; [apply in_or_app|exact Hino]); auto.
  Qed.

  Lemma output_in_trace_rev o (l : list IO_event) :
    output_in_trace o (rev l) <-> output_in_trace o l.
  Proof.
    unfold output_in_trace; split; intros (outs & Hin & Hino); exists outs;
      (split; [|exact Hino]); apply in_rev; auto.
    rewrite rev_involutive. exact Hin.
  Qed.

  Lemma allowed_trace_universal :
    (forall t m, A t m) -> forall t, allowed_trace t.
  Proof.
    intros Au t. unfold allowed_trace, allowed_IO_event; intros.
    destruct e; auto.
  Qed.

  Section node.
    Context {node_state : Type}.
    Context (node_step : node_state -> IO_event -> node_state -> Prop).
    Context (D : list message (*inputs*) -> message (*output*) -> Prop).
    Context (initial_ns : node_state).

    Definition node_might_output start t (output : message) : Prop :=
      exists t' ns,
        star node_step start t' ns /\
          allowed_trace (t' ++ t) /\
          output_in_trace output (t' ++ t).

    Definition node_will_output start t (output : message) : Prop :=
      eventually (can_step node_step allowed_trace (fun _ => event_guaranteed))
        (fun '(_, t') => output_in_trace output t')
        (start, t).

    Definition monotone :=
      forall inputs1 inputs2 output,
        D inputs1 output ->
        incl inputs1 inputs2 ->
        D inputs2 output.

    Definition node_described_by :=
      forall t ns,
        star node_step initial_ns t ns ->
        allowed_trace t ->
        (forall output,
            D (inputs_of t) output ->
            node_will_output ns t output) /\
          (forall output,
              node_might_output ns t output ->
              D (inputs_of t) output).
  End node.

  Section gen.
    Context {NP : Type} {graph_prog : map.map node_id NP}.
    Context {NS : Type} {node_states : map.map node_id NS}.
    Context {node_states_ok : map.ok node_states}.
    Context (p : graph_prog).
    Context (node_step : NP -> NS -> IO_event -> NS -> Prop).

    Lemma drive_node :
      (forall t m, A t m) ->
      forall (np : NP) (n : node_id) (o : message),
        map.get p n = Some np ->
        output_visible n o = true ->
        forall (s : NS * list IO_event),
          eventually (can_step (node_step np) allowed_trace
                               (fun _ => event_guaranteed))
                     (fun '(_, t') => output_in_trace o t')
                     s ->
          forall gs,
            map.get (@g_nodes _ node_states gs) n = Some (fst s) ->
            exists T gs',
              star (graph_step p node_step) gs T gs' /\
              (output_in_trace o T \/ output_in_trace o (snd s)).
    Proof.
      intros A_univ np n o Hp Hvis s Hwill.
      induction Hwill as [[ns trace] HP | [ns trace] midset Hcan Hmid IH];
        intros gs Hgs; cbn in *.
      - exists [], gs. split; [constructor | right; exact HP].
      - destruct (Hcan ns [] (star_refl _ _) (allowed_trace_universal A_univ _))
          as (s'' & [m_|outs] & Hguar & Hstep & Hmidset); [contradiction|].
        pose (gs' := {| g_nodes := map.put (g_nodes gs) n s'';
                        g_messages := g_messages gs ++
                          flat_map (fun m0 => map (fun n' => (n', m0))
                                                  (forward n m0)) outs |}).
        edestruct (IH _ Hmidset gs') as (T & gs'' & Hstar' & Hcase);
          [cbn; apply map.get_put_same|].
        exists (O_event (filter (output_visible n) outs) :: T), gs''.
        split; [econstructor; [eapply gstep_run; eauto | exact Hstar']|].
        destruct Hcase as [(outs' & Hin & Hino) | (outs' & Hin & Hino)].
        + left. exists outs'. split; [right; exact Hin | exact Hino].
        + destruct Hin as [Heq|Hin'].
          * injection Heq as Heq; subst outs'.
            left. exists (filter (output_visible n) outs).
            split; [left; reflexivity|].
            apply filter_In. split; assumption.
          * right. exists outs'. split; assumption.
    Qed.

    Lemma graph_emits_implies_node_emits :
      forall T gs0 gs,
        star (graph_step p node_step) gs0 T gs ->
        forall o, output_in_trace o T ->
          exists n np ns_at_gs0,
            map.get p n = Some np /\
            map.get (@g_nodes _ node_states gs0) n = Some ns_at_gs0 /\
            output_visible n o = true /\
            exists tau ns,
              star (node_step np) ns_at_gs0 tau ns /\
              output_in_trace o tau.
    Proof.
      intros T gs0 gs Hstar.
      induction Hstar as [|s e s' t0 s'' Hstep Hstar IH];
        intros o (outs_o & Hin_o & Hino); [inversion Hin_o|].
      cbn in Hin_o. destruct Hin_o as [Heq|Hin_o'].
      - subst e. inversion Hstep; subst.
        + apply filter_In in Hino as [Hino Hvis].
          exists n, np, ns. do 3 (split; [auto|]).
          exists [O_event outs], ns'.
          split; [econstructor; [eassumption|constructor]|].
          exists outs. split; [now left|exact Hino].
        + inversion Hino.
      - destruct (IH o (ex_intro _ outs_o (conj Hin_o' Hino)))
          as (nn & npp & ns_at_s' & Hp1 & Hgs' & Hvis & tau & ns_end & Htau & Houttau).
        inversion Hstep; subst; cbn in Hgs'.
        + exists nn, npp, ns_at_s'. do 3 (split; [auto|]).
          exists tau, ns_end. tauto.
        + destruct (Nat.eq_dec nn n) as [<-|Hne].
          * rewrite H in Hp1. inversion Hp1; subst npp.
            rewrite map.get_put_same in Hgs'. inversion Hgs'; subst ns_at_s'.
            exists nn, np, ns. do 3 (split; [auto|]).
            exists (O_event outs :: tau), ns_end.
            split; [econstructor; eassumption|].
            destruct Houttau as (outs' & Hin' & Hino').
            exists outs'. split; [right; exact Hin'|exact Hino'].
          * rewrite map.get_put_diff in Hgs' by auto.
            exists nn, npp, ns_at_s'. do 3 (split; [auto|]).
            exists tau, ns_end. tauto.
        + destruct (Nat.eq_dec nn n) as [<-|Hne].
          * rewrite H in Hp1. inversion Hp1; subst npp.
            rewrite map.get_put_same in Hgs'. inversion Hgs'; subst ns_at_s'.
            exists nn, np, ns. do 3 (split; [auto|]).
            exists (I_event m :: tau), ns_end.
            split; [econstructor; eassumption|].
            destruct Houttau as (outs' & Hin' & Hino').
            exists outs'. split; [right; exact Hin'|exact Hino'].
          * rewrite map.get_put_diff in Hgs' by auto.
            exists nn, npp, ns_at_s'. do 3 (split; [auto|]).
            exists tau, ns_end. tauto.
    Qed.

    Lemma project_node :
      forall T gs0 gs,
        star (graph_step p node_step) gs0 T gs ->
        forall n np ns_at_gs0,
          map.get p n = Some np ->
          map.get (@g_nodes _ node_states gs0) n = Some ns_at_gs0 ->
          exists tau ns_at_gs,
            star (node_step np) ns_at_gs0 tau ns_at_gs /\
            map.get (g_nodes gs) n = Some ns_at_gs /\
            (forall o, output_visible n o = true ->
                       output_in_trace o tau -> output_in_trace o T).
    Proof.
      intros T gs0 gs Hstar.
      induction Hstar as [|s e s' t0 s'' Hstep Hstar IH];
        intros n np ns_at_gs0 Hp Hg0.
      - exists [], ns_at_gs0. split; [constructor|]. split; [exact Hg0|].
        intros o _ (outs & Hin & _); inversion Hin.
      - inversion Hstep; subst.
        + destruct (IH n np ns_at_gs0 Hp Hg0) as (tau & ns_at_gs & Htau & Hg & Hpres).
          exists tau, ns_at_gs. do 2 (split; [auto|]).
          intros o Hvis Hout. cbn.
          destruct (Hpres o Hvis Hout) as (outs' & Hin' & Hino').
          exists outs'. split; [right; exact Hin'|exact Hino'].
        + destruct (Nat.eq_dec n0 n) as [Heq|Hne].
          * subst n0.
            rewrite H in Hp. inversion Hp; subst np0.
            rewrite H0 in Hg0. inversion Hg0; subst ns_at_gs0.
            destruct (IH n np ns') as (tau & ns_at_gs & Htau & Hg & Hpres);
              [exact H | cbn; apply map.get_put_same|].
            exists (O_event outs :: tau), ns_at_gs.
            split; [econstructor; eassumption|]. split; [exact Hg|].
            intros o Hvis (outs' & [Heq|Hin_rest] & Hino).
            -- injection Heq as ->.
               exists (filter (output_visible n) outs').
               split; [now left|].
               apply filter_In. split; assumption.
            -- destruct (Hpres o Hvis (ex_intro _ outs' (conj Hin_rest Hino)))
                 as (outs'' & Hin'' & Hino'').
               exists outs''. split; [right; exact Hin''|exact Hino''].
          * destruct (IH n np ns_at_gs0 Hp) as (tau & ns_at_gs & Htau & Hg & Hpres);
              [cbn; rewrite map.get_put_diff by auto; exact Hg0|].
            exists tau, ns_at_gs. do 2 (split; [auto|]).
            intros o Hvis Hout. cbn.
            destruct (Hpres o Hvis Hout) as (outs' & Hin' & Hino').
            exists outs'. split; [right; exact Hin'|exact Hino'].
        + destruct (Nat.eq_dec n0 n) as [Heq|Hne].
          * subst n0.
            rewrite H in Hp. inversion Hp; subst np0.
            rewrite H0 in Hg0. inversion Hg0; subst ns_at_gs0.
            destruct (IH n np ns') as (tau & ns_at_gs & Htau & Hg & Hpres);
              [exact H | cbn; apply map.get_put_same|].
            exists (I_event m :: tau), ns_at_gs.
            split; [econstructor; eassumption|]. split; [exact Hg|].
            intros o Hvis (outs' & [|Hin_rest] & Hino); [discriminate|].
            destruct (Hpres o Hvis (ex_intro _ outs' (conj Hin_rest Hino)))
              as (outs'' & Hin'' & Hino'').
            exists outs''. split; [right; exact Hin''|exact Hino''].
          * destruct (IH n np ns_at_gs0 Hp) as (tau & ns_at_gs & Htau & Hg & Hpres);
              [cbn; rewrite map.get_put_diff by auto; exact Hg0|].
            exists tau, ns_at_gs. do 2 (split; [auto|]).
            intros o Hvis Hout. cbn.
            destruct (Hpres o Hvis Hout) as (outs' & Hin' & Hino').
            exists outs'. split; [right; exact Hin'|exact Hino'].
    Qed.

    Lemma drive_node_must :
      (forall t m, A t m) ->
      forall (np : NP) (n : node_id) (o : message),
        map.get p n = Some np ->
        output_visible n o = true ->
        forall (s : NS * list IO_event),
          eventually (can_step (node_step np) allowed_trace
                               (fun _ => event_guaranteed))
                     (fun '(_, t') => output_in_trace o t')
                     s ->
          forall gs t,
            map.get (@g_nodes _ node_states gs) n = Some (fst s) ->
            (output_in_trace o (snd s) -> output_in_trace o t) ->
            eventually (can_step (graph_step p node_step) allowed_trace
                                 (fun _ => event_guaranteed))
                       (fun '(_, t') => output_in_trace o t')
                       (gs, t).
    Proof.
      intros A_univ np n o Hp Hvis s Hwill.
      induction Hwill as [[ns trace] HP | [ns trace] midset Hcan Hmid IH];
        intros gs t Hg Hout_proj; cbn in *.
      - apply eventually_done. cbn. auto.
      - apply eventually_step_cps.
        intros gs_demon t_demon Hstar_demon _.
        destruct (project_node _ _ _ Hstar_demon n np _ Hp Hg)
          as (τd & ns_d & Hτd & Hg_d & Hpres_d).
        destruct (Hcan ns_d τd Hτd (allowed_trace_universal A_univ _))
          as (s'' & [m_|outs] & Hguar & Hns_step & Hmidset_at); [contradiction|].
        pose (gs' := {| g_nodes := map.put (g_nodes gs_demon) n s'';
                        g_messages := g_messages gs_demon ++
                          flat_map (fun m0 => map (fun n' => (n', m0))
                                                  (forward n m0)) outs |}).
        exists gs', (O_event (filter (output_visible n) outs)).
        split; [exact I|]. split; [eapply gstep_run; eauto|].
        apply (IH _ Hmidset_at gs'); [cbn; apply map.get_put_same|].
        intros (outs' & [Heq|Hin_rest] & Hino).
        + injection Heq as ->.
          exists (filter (output_visible n) outs').
          split; [now left|]. apply filter_In. split; assumption.
        + apply in_app_or in Hin_rest as [Hin_τd|Hin_τn].
          * destruct (Hpres_d o Hvis (ex_intro _ outs' (conj Hin_τd Hino)))
              as (outs'' & Hin'' & Hino'').
            exists outs''. split; [right; apply in_or_app; left; exact Hin''|exact Hino''].
          * destruct (Hout_proj (ex_intro _ outs' (conj Hin_τn Hino)))
              as (outs'' & Hin'' & Hino'').
            exists outs''. split; [right; apply in_or_app; right; exact Hin''|exact Hino''].
    Qed.
  End gen.

  Section nodes.
    Context {node_state1 : Type}.
    Context (node_step1 : node_state1 -> IO_event -> node_state1 -> Prop).
    Context (initial_ns1 : node_state1).

    Context {node_state2 : Type}.
    Context (node_step2 : node_state2 -> IO_event -> node_state2 -> Prop).
    Context (initial_ns2 : node_state2).

    Definition nodes_equiv :=
      exists D,
        monotone D /\
        node_described_by node_step1 D initial_ns1 /\
          node_described_by node_step2 D initial_ns2.
  End nodes.

  Lemma nodes_equiv_sym {NS1 NS2}
    (step1 : NS1 -> IO_event -> NS1 -> Prop) (ns1 : NS1)
    (step2 : NS2 -> IO_event -> NS2 -> Prop) (ns2 : NS2) :
    nodes_equiv step1 ns1 step2 ns2 -> nodes_equiv step2 ns2 step1 ns1.
  Proof. intros (D & Hm & H1 & H2). exists D. split; [|split]; assumption. Qed.

  Section transfer.
    Context {NP_s : Type} {graph_prog_s : map.map node_id NP_s}.
    Context {NS_s : Type} {node_states_s : map.map node_id NS_s}.
    Context {node_states_s_ok : map.ok node_states_s}.
    Context (p_s : graph_prog_s).
    Context (node_step_s : NP_s -> NS_s -> IO_event -> NS_s -> Prop).
    Context (initial_ns_s : node_states_s).

    Context {NP_d : Type} {graph_prog_d : map.map node_id NP_d}.
    Context {NS_d : Type} {node_states_d : map.map node_id NS_d}.
    Context {node_states_d_ok : map.ok node_states_d}.
    Context (p_d : graph_prog_d).
    Context (node_step_d : NP_d -> NS_d -> IO_event -> NS_d -> Prop).
    Context (initial_ns_d : node_states_d).

    Lemma ever_produces_same :
      (forall t m, A t m) ->
      Forall4_map
        (fun n np_s np_d ns_s ns_d =>
           nodes_equiv (node_step_s np_s) ns_s (node_step_d np_d) ns_d)
        p_s p_d initial_ns_s initial_ns_d ->
      forall o T_s gs_s,
        star (graph_step p_s node_step_s)
             {| g_nodes := initial_ns_s; g_messages := [] |} T_s gs_s ->
        output_in_trace o T_s ->
        exists T gs, star (graph_step p_d node_step_d)
                          {| g_nodes := initial_ns_d; g_messages := [] |}
                          T gs /\ output_in_trace o T.
    Proof.
      intros A_univ Hcorr o T_s gs_s Hstar_s Hout_s.
      pose proof (allowed_trace_universal A_univ []) as Hnil.
      destruct (graph_emits_implies_node_emits p_s node_step_s _ _ _ Hstar_s _ Hout_s)
        as (n & np_s & ns_s & Hp_s & Hg_s & Hvis & tau & ns_end & Htau & Hout_tau).
      cbn in Hg_s. pose proof (Hcorr n) as Hn. rewrite Hp_s, Hg_s in Hn.
      destruct (map.get p_d n) as [np_d|] eqn:Hp_d; [|contradiction].
      destruct (map.get initial_ns_d n) as [ns_d|] eqn:Hg_d; [|contradiction].
      destruct Hn as (D & _ & Hd_s & Hd_d).
      destruct (Hd_s [] ns_s (star_refl _ _) Hnil) as [_ Hmay].
      destruct (Hd_d [] ns_d (star_refl _ _) Hnil) as [Hmust _].
      assert (D [] o) as HD0.
      { apply Hmay. exists tau, ns_end. repeat split;
          [exact Htau|apply allowed_trace_universal; auto
          |rewrite app_nil_r; exact Hout_tau]. }
      destruct (drive_node p_d node_step_d A_univ np_d n o Hp_d Hvis
                           (ns_d, []) (Hmust o HD0)
                           {| g_nodes := initial_ns_d; g_messages := [] |} Hg_d)
        as (T & gs & Hstar & [Hout|(? & Hin & _)]); [|inversion Hin].
      exists T, gs. split; assumption.
    Qed.
  End transfer.

  Section graphs.
    Context {node_prog1 : Type} {graph_prog1 : map.map node_id node_prog1}.
    Context {node_state1 : Type} {node_states1 : map.map node_id node_state1}.
    Context {node_states1_ok : map.ok node_states1}.
    Context (p1 : graph_prog1).
    Context (node_step1 : node_prog1 -> node_state1 -> IO_event -> node_state1 -> Prop).
    Context (initial_ns1 : node_states1).

    Context {node_prog2 : Type} {graph_prog2 : map.map node_id node_prog2}.
    Context {node_state2 : Type} {node_states2 : map.map node_id node_state2}.
    Context {node_states2_ok : map.ok node_states2}.
    Context (p2 : graph_prog2).
    Context (node_step2 : node_prog2 -> node_state2 -> IO_event -> node_state2 -> Prop).
    Context (initial_ns2 : node_states2).

    Definition initial_gs1 : @graph_state node_state1 node_states1 :=
      {| g_nodes := initial_ns1; g_messages := [] |}.

    Definition initial_gs2 : @graph_state node_state2 node_states2 :=
      {| g_nodes := initial_ns2; g_messages := [] |}.

    Lemma will_output_transport :
      (forall t m, A t m) ->
      Forall4_map
        (fun n np1 np2 ns1 ns2 =>
           nodes_equiv (node_step1 np1) ns1 (node_step2 np2) ns2)
        p1 p2 initial_ns1 initial_ns2 ->
      forall t gs2 o,
        star (graph_step p2 node_step2) initial_gs2 t gs2 ->
        (exists T1 gs1,
           star (graph_step p1 node_step1) initial_gs1 T1 gs1 /\
           inputs_of T1 = inputs_of t /\
           node_will_output (graph_step p1 node_step1) gs1 T1 o) ->
        node_will_output (graph_step p2 node_step2) gs2 t o.
    Proof.
      intros A_univ Hcorr t gs2 o Hstar2 (T1 & gs1 & HT1 & _ & Hwill1).
      pose proof (allowed_trace_universal A_univ []) as Hnil.
      destruct (eventually_can_step_to_star (graph_step p1 node_step1) _ _ _ gs1 T1
                  (fun _ => allowed_trace_universal A_univ _) Hwill1)
        as (gs1' & tr & Hstar_extra & Hout_extra).
      assert (output_in_trace o (T1 ++ tr)) as Hout_full.
      { apply output_in_trace_app.
        apply output_in_trace_app in Hout_extra as [Hout|Hout];
          [right; apply output_in_trace_rev; exact Hout|left; exact Hout]. }
      destruct (graph_emits_implies_node_emits p1 node_step1 _ _ _
                  (star_app _ _ _ _ _ _ HT1 Hstar_extra) _ Hout_full)
        as (n & np1 & ns1 & Hp1 & Hg1 & Hvis & tau1 & ns_end1 & Htau1 & Hout_tau1).
      cbn in Hg1.
      pose proof (Hcorr n) as Hn. rewrite Hp1, Hg1 in Hn.
      destruct (map.get p2 n) as [np2|] eqn:Hp2; [|contradiction].
      destruct (map.get initial_ns2 n) as [ns2|] eqn:Hg2; [|contradiction].
      destruct Hn as (D & Hmono & Hd1 & Hd2).
      destruct (Hd1 [] _ (star_refl _ _) Hnil) as [_ Hmay].
      destruct (project_node p2 node_step2 _ _ _ Hstar2 n np2 _ Hp2 Hg2)
        as (tau2 & ns_at_gs2 & Htau2 & Hg_gs2 & Hpres2).
      destruct (Hd2 tau2 _ Htau2 (allowed_trace_universal A_univ _)) as [Hmust _].
      assert (D [] o) as HD0.
      { apply Hmay. exists tau1, ns_end1. repeat split;
          [exact Htau1|apply allowed_trace_universal; auto
          |rewrite app_nil_r; exact Hout_tau1]. }
      apply (drive_node_must p2 node_step2 A_univ np2 n o Hp2 Hvis
                             (ns_at_gs2, tau2)
                             (Hmust o (Hmono _ _ _ HD0 (incl_nil_l _)))
                             gs2 t Hg_gs2).
      intros Hout. apply Hpres2; assumption.
    Qed.

    Lemma env_only_lift :
      forall t gs0_2 gs2,
        star (graph_step p2 node_step2) gs0_2 t gs2 ->
        forall gs0_1,
        exists T1 gs1,
          star (graph_step p1 node_step1) gs0_1 T1 gs1 /\
          inputs_of T1 = inputs_of t.
    Proof.
      induction 1 as [|s e s' t0 s'' Hstep Hstar IH]; intros gs0_1;
        [exists [], gs0_1; split; [constructor|reflexivity]|].
      inversion Hstep; subst.
      - destruct (IH {| g_nodes := g_nodes gs0_1;
                        g_messages := (n, m) :: g_messages gs0_1 |})
          as (T1' & gs1' & HT1' & Hinp).
        exists (I_event m :: T1'), gs1'.
        split; [econstructor; [apply gstep_input|exact HT1']
               |cbn; f_equal; exact Hinp]; auto.
      - destruct (IH gs0_1) as (T1 & gs1 & HT1 & Hinp).
        exists T1, gs1. split; [exact HT1|exact Hinp].
      - destruct (IH gs0_1) as (T1 & gs1 & HT1 & Hinp).
        exists T1, gs1. split; [exact HT1|exact Hinp].
    Qed.

    Theorem graphs_equiv D :
      (forall t m, A t m) ->
      Forall4_map
        (fun n np1 np2 ns1 ns2 =>
           nodes_equiv (node_step1 np1) ns1 (node_step2 np2) ns2)
        p1 p2 initial_ns1 initial_ns2 ->
      monotone D ->
      node_described_by (graph_step p1 node_step1) D initial_gs1 ->
      node_described_by (graph_step p2 node_step2) D initial_gs2.
    Proof.
      intros A_univ Hcorr Hmono H1.
      pose proof (allowed_trace_universal A_univ) as Ha.
      intros t gs2 Hstar2 _.
      split.
      - intros o Hd.
        destruct (env_only_lift _ _ _ Hstar2 initial_gs1) as (T1 & gs1 & HT1star & Heqinputs).
        eapply will_output_transport; try eassumption.
        exists T1, gs1; repeat split; auto.
        destruct (H1 _ _ HT1star (Ha _)) as [Hmust1 _].
        apply Hmust1. rewrite Heqinputs; exact Hd.
      - intros o (t' & gs2' & Hstar' & _ & Hout).
        apply (Hmono [] (inputs_of t) o); [|apply incl_nil_l].
        destruct (H1 [] initial_gs1 (star_refl _ _) (Ha _)) as [_ Hmay1].
        apply Hmay1.
        edestruct (ever_produces_same p2 node_step2 initial_ns2 p1 node_step1 initial_ns1
                                      A_univ) as (T1 & gs1 & HT1 & HT1out).
        { intros n. specialize (Hcorr n).
          destruct (map.get p1 n), (map.get p2 n),
                   (map.get initial_ns1 n), (map.get initial_ns2 n);
            try contradiction; auto using nodes_equiv_sym. }
        { eapply star_app; eauto. }
        { apply output_in_trace_app.
          apply output_in_trace_app in Hout as [Houtl|Houtr];
            [right; exact Houtl|left; exact Houtr]. }
        exists T1, gs1. rewrite app_nil_r. repeat split; auto.
    Qed.
  End graphs.
End __.
