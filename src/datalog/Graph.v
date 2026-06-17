From coqutil Require Import Map.Interface.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
From Stdlib Require Import List PeanoNat.
From Datalog Require Import Smallstep Map.
Import ListNotations.

Definition node_id := nat.
Section __.
  Context {message : Type}.
  Context (A : list message -> message -> Prop).
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

  Section node.
    Context {node_state : Type}.
    Context (node_step : node_state -> IO_event -> node_state -> Prop).
    Context (D : list message (*inputs*) -> message (*output*) -> Prop).
    Context (initial_ns : node_state).

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

    (* Under universal A, [allowed_trace] is trivially True everywhere, so we
       can drop it from both [node_described_by] hypotheses and from
       [node_might_output] / the [can_step] inside [node_will_output]. *)

    (* The two halves of [node_described_by] each reduce to a clean
       statement that the two graphs have matching {may-outputs, will-outputs}
       sets at initial state.  Per-node [nodes_equiv] + the routing structure
       is what would prove these set equalities, and we leave them as
       [Admitted].  Once they are proved, the conclusion drops out via
       [monotone D] + [graph 1 ⊨ D]. *)

    Lemma star_app {st ev} (step : st -> ev -> st -> Prop) s1 t1 s2 t2 s3 :
      star step s1 t1 s2 -> star step s2 t2 s3 -> star step s1 (t1 ++ t2) s3.
    Proof.
      induction 1; cbn; [auto|].
      econstructor; eauto.
    Qed.

    Lemma output_in_trace_app o (l1 l2 : list IO_event) :
      output_in_trace o (l1 ++ l2) <-> output_in_trace o l1 \/ output_in_trace o l2.
    Proof.
      unfold output_in_trace; split.
      - intros (outs & Hin & Hino).
        apply in_app_or in Hin as [Hin|Hin]; [left|right]; eauto.
      - intros [(outs & Hin & Hino)|(outs & Hin & Hino)];
          exists outs; (split; [apply in_or_app|exact Hino]); auto.
    Qed.

    Lemma allowed_trace_universal :
      (forall t m, A t m) -> forall t, allowed_trace t.
    Proof.
      intros Au t. unfold allowed_trace, allowed_IO_event; intros.
      destruct e; auto.
    Qed.

    (* Generic [drive_node]: given a node-level eventually-emit-o proof,
       drive the graph (with that node's program) to emit o by doing
       gstep_runs on n corresponding to the angel's choices. *)
    Lemma drive_node_gen :
      (forall t m, A t m) ->
      forall {NP : Type} {graph_prog : map.map node_id NP}
             {NS : Type} {node_states : map.map node_id NS}
             {node_states_ok : map.ok node_states}
             (p : graph_prog)
             (node_step : NP -> NS -> IO_event -> NS -> Prop),
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
      intros A_univ NP graph_prog NS node_states node_states_ok p node_step np n o Hp Hvis s Hwill.
      induction Hwill as [[ns_curr trace_curr] HP|
                          [ns_curr trace_curr] midset Hcan Hmid IH];
        intros gs Hgs.
      - (* eventually_done: P (ns_curr, trace_curr) *)
        cbn in HP. cbn.
        exists [], gs. split; [constructor|right; exact HP].
      - (* eventually_step *)
        cbn in *.
        pose proof (Hcan ns_curr []) as Hcan'.
        specialize (Hcan' (star_refl _ _)).
        assert (allowed_trace ([] ++ trace_curr)) as Hallow
          by (apply allowed_trace_universal; auto).
        specialize (Hcan' Hallow).
        destruct Hcan' as (s'' & e & Hguar & Hstep & Hmidset).
        destruct e as [m_|outs]; [cbn in Hguar; contradiction|].
        set (gs_next :=
               {| g_nodes := map.put (g_nodes gs) n s'';
                  g_messages :=
                    g_messages gs ++
                    flat_map (fun m0 => map (fun n' => (n', m0))
                                            (forward n m0)) outs |}).
        assert (Hgstep : graph_step p node_step gs
                                    (O_event (filter (output_visible n) outs))
                                    gs_next).
        { eapply gstep_run; eauto. }
        cbn in IH.
        specialize (IH (s'', O_event outs :: [] ++ trace_curr) Hmidset gs_next).
        cbn in IH.
        assert (map.get (g_nodes gs_next) n = Some s'') as Hgs_next.
        { cbn. apply map.get_put_same. }
        specialize (IH Hgs_next).
        destruct IH as (T2' & gs'' & Hstar' & Hcase).
        exists (O_event (filter (output_visible n) outs) :: T2'), gs''.
        split.
        { econstructor; eassumption. }
        destruct Hcase as [Hout|Hout].
        + left. destruct Hout as (outs' & Hin & Hino).
          exists outs'. split; [right; exact Hin|exact Hino].
        + destruct Hout as (outs' & Hin & Hino).
          cbn in Hin. destruct Hin as [Heq|Hin'].
          * injection Heq as Heqo. subst outs'.
            left. exists (filter (output_visible n) outs). split.
            { cbn. left; reflexivity. }
            apply filter_In. split; [exact Hino|exact Hvis].
          * right. exists outs'. split; [exact Hin'|exact Hino].
    Qed.

    (* Generic version: if a graph emits o, then some node has a node-level
       trace from its starting state producing o, and o is visible at n. *)
    Lemma graph_emits_implies_node_emits_gen :
      forall {NP : Type} {graph_prog : map.map node_id NP}
             {NS : Type} {node_states : map.map node_id NS}
             {node_states_ok : map.ok node_states}
             (p : graph_prog)
             (node_step : NP -> NS -> IO_event -> NS -> Prop),
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
      intros NP graph_prog NS node_states node_states_ok p node_step T gs0 gs Hstar.
      induction Hstar as [s|s e s' t0 s'' Hstep Hstar IH];
        intros o (outs_o & Hin_o & Hino).
      - inversion Hin_o.
      - cbn in Hin_o. destruct Hin_o as [Heq|Hin_o'].
        + (* e = O_event outs_o, in head position *)
          subst e.
          inversion Hstep; subst.
          * (* gstep_run *)
            apply filter_In in Hino as [Hino Hvis].
            exists n, np, ns.
            split; [auto|]. split; [auto|]. split; [auto|].
            exists [O_event outs], ns'.
            split.
            { econstructor; [eassumption|constructor]. }
            exists outs. split; [left; reflexivity|exact Hino].
          * (* gstep_receive: O_event [], but In o [] is false *)
            inversion Hino.
        + (* o is in t0 *)
          specialize (IH o (ex_intro _ outs_o (conj Hin_o' Hino))).
          destruct IH as (nn & npp & ns_at_s' & Hp1 & Hgs' & Hvis & tau & ns_end & Htau & Houttau).
          inversion Hstep; subst.
          * (* gstep_input: g_nodes unchanged *)
            cbn in Hgs'. exists nn, npp, ns_at_s'.
            split; [exact Hp1|]. split; [exact Hgs'|]. split; [exact Hvis|].
            exists tau, ns_end. split; [exact Htau|exact Houttau].
          * (* gstep_run: variables n, np, ns, ns', outs from inversion *)
            cbn in Hgs'.
            destruct (Nat.eq_dec nn n) as [Heq|Hne].
            -- (* nn = n: node nn was stepped *)
               subst nn.
               rewrite H in Hp1. inversion Hp1; subst npp.
               rewrite map.get_put_same in Hgs'. inversion Hgs'; subst ns_at_s'.
               exists n, np, ns.
               split; [exact H|]. split; [exact H0|]. split; [exact Hvis|].
               exists (O_event outs :: tau), ns_end.
               split.
               { econstructor; [exact H1|exact Htau]. }
               destruct Houttau as (outs' & Hin' & Hino').
               exists outs'. split; [right; exact Hin'|exact Hino'].
            -- (* nn ≠ n *)
               rewrite map.get_put_diff in Hgs' by auto.
               exists nn, npp, ns_at_s'.
               split; [exact Hp1|]. split; [exact Hgs'|]. split; [exact Hvis|].
               exists tau, ns_end. split; [exact Htau|exact Houttau].
          * (* gstep_receive: variables n, np, ns, ns', m, ms1, ms2 from inversion *)
            cbn in Hgs'.
            destruct (Nat.eq_dec nn n) as [Heq|Hne].
            -- subst nn.
               rewrite H in Hp1. inversion Hp1; subst npp.
               rewrite map.get_put_same in Hgs'. inversion Hgs'; subst ns_at_s'.
               exists n, np, ns.
               split; [exact H|]. split; [exact H0|]. split; [exact Hvis|].
               exists (I_event m :: tau), ns_end.
               split.
               { econstructor; [exact H1|exact Htau]. }
               destruct Houttau as (outs' & Hin' & Hino').
               exists outs'. split; [right; exact Hin'|exact Hino'].
            -- rewrite map.get_put_diff in Hgs' by auto.
               exists nn, npp, ns_at_s'.
               split; [exact Hp1|]. split; [exact Hgs'|]. split; [exact Hvis|].
               exists tau, ns_end. split; [exact Htau|exact Houttau].
    Qed.

    (* The two graphs ever-produce the same outputs.
       Direct proof via [graph_emits_implies_node_emits_gen] (project to a
       node-level may-emit) + [nodes_equiv] (transfer to the other node) +
       [drive_node_gen] (drive the other graph to emit). *)
    Lemma ever_produces_same :
      (forall t m, A t m) ->
      Forall4_map
        (fun n np1 np2 ns1 ns2 =>
           nodes_equiv (node_step1 np1) ns1 (node_step2 np2) ns2)
        p1 p2 initial_ns1 initial_ns2 ->
      forall o,
        (exists T1 gs1, star (graph_step p1 node_step1) initial_gs1 T1 gs1
                        /\ output_in_trace o T1) <->
        (exists T2 gs2, star (graph_step p2 node_step2) initial_gs2 T2 gs2
                        /\ output_in_trace o T2).
    Proof.
      intros A_univ Hcorr o.
      pose proof (allowed_trace_universal A_univ []) as Hallow_nil.
      split.
      - intros (T1 & gs1 & Hstar1 & Hout1).
        edestruct (graph_emits_implies_node_emits_gen p1 node_step1 _ _ _ Hstar1 _ Hout1)
          as (n & np1 & ns_init1 & Hp1 & Hg1 & Hvis & tau & ns_end & Htau & Hout_tau).
        cbn in Hg1.
        pose proof (Hcorr n) as Hn.
        rewrite Hp1, Hg1 in Hn.
        destruct (map.get p2 n) as [np2|] eqn:Hp2; [|cbn in Hn; contradiction].
        destruct (map.get initial_ns2 n) as [ns_init2|] eqn:Hg2;
          [|cbn in Hn; contradiction].
        destruct Hn as (D_n & Hmono_n & Hdesc1 & Hdesc2).
        destruct (Hdesc1 [] ns_init1 (star_refl _ _) Hallow_nil) as [_ Hmay1].
        assert (node_might_output (node_step1 np1) ns_init1 [] o) as Hmight.
        { exists tau, ns_end. split; [exact Htau|].
          split; [apply allowed_trace_universal; auto|].
          rewrite app_nil_r. exact Hout_tau. }
        pose proof (Hmay1 o Hmight) as HD0.
        cbn in HD0.
        destruct (Hdesc2 [] ns_init2 (star_refl _ _) Hallow_nil) as [Hmust2 _].
        pose proof (Hmust2 o HD0) as Hwill2.
        edestruct (drive_node_gen A_univ p2 node_step2 np2 n o Hp2 Hvis
                                  (ns_init2, []) Hwill2 initial_gs2 Hg2)
          as (T2 & gs2 & Hstar2 & Hcase).
        exists T2, gs2. split; [auto|].
        cbn in Hcase. destruct Hcase as [Hout|Hout]; [exact Hout|].
        destruct Hout as (outs & Hin & _); inversion Hin.
      - intros (T2 & gs2 & Hstar2 & Hout2).
        edestruct (graph_emits_implies_node_emits_gen p2 node_step2 _ _ _ Hstar2 _ Hout2)
          as (n & np2 & ns_init2 & Hp2 & Hg2 & Hvis & tau & ns_end & Htau & Hout_tau).
        cbn in Hg2.
        pose proof (Hcorr n) as Hn.
        rewrite Hp2, Hg2 in Hn.
        destruct (map.get p1 n) as [np1|] eqn:Hp1; [|cbn in Hn; contradiction].
        destruct (map.get initial_ns1 n) as [ns_init1|] eqn:Hg1;
          [|cbn in Hn; contradiction].
        destruct Hn as (D_n & Hmono_n & Hdesc1 & Hdesc2).
        destruct (Hdesc2 [] ns_init2 (star_refl _ _) Hallow_nil) as [_ Hmay2].
        assert (node_might_output (node_step2 np2) ns_init2 [] o) as Hmight.
        { exists tau, ns_end. split; [exact Htau|].
          split; [apply allowed_trace_universal; auto|].
          rewrite app_nil_r. exact Hout_tau. }
        pose proof (Hmay2 o Hmight) as HD0.
        cbn in HD0.
        destruct (Hdesc1 [] ns_init1 (star_refl _ _) Hallow_nil) as [Hmust1 _].
        pose proof (Hmust1 o HD0) as Hwill1.
        edestruct (drive_node_gen A_univ p1 node_step1 np1 n o Hp1 Hvis
                                  (ns_init1, []) Hwill1 initial_gs1 Hg1)
          as (T1 & gs1 & Hstar1 & Hcase).
        exists T1, gs1. split; [auto|].
        cbn in Hcase. destruct Hcase as [Hout|Hout]; [exact Hout|].
        destruct Hout as (outs & Hin & _); inversion Hin.
    Qed.

    (* Projection: graph 1's trace projects to a node-level trace at each
       node, with the resulting state matching gs.g_nodes[n]. *)
    Lemma project_node_gen :
      forall {NP : Type} {graph_prog : map.map node_id NP}
             {NS : Type} {node_states : map.map node_id NS}
             {node_states_ok : map.ok node_states}
             (p : graph_prog)
             (node_step : NP -> NS -> IO_event -> NS -> Prop),
      forall T gs0 gs,
        star (graph_step p node_step) gs0 T gs ->
        forall n np ns_at_gs0,
          map.get p n = Some np ->
          map.get (@g_nodes _ node_states gs0) n = Some ns_at_gs0 ->
          exists tau ns_at_gs,
            star (node_step np) ns_at_gs0 tau ns_at_gs /\
            map.get (g_nodes gs) n = Some ns_at_gs.
    Proof.
      intros NP graph_prog NS node_states node_states_ok p node_step T gs0 gs Hstar.
      induction Hstar as [s|s e s' t0 s'' Hstep Hstar IH];
        intros n np ns_at_gs0 Hp Hg0.
      - exists [], ns_at_gs0. split; [constructor|exact Hg0].
      - inversion Hstep; subst.
        + (* gstep_input: g_nodes unchanged *)
          destruct (IH n np ns_at_gs0 Hp Hg0) as (tau & ns_at_gs & Htau & Hg).
          exists tau, ns_at_gs. split; auto.
        + (* gstep_run: variables n, np, ns, ns', outs from inversion *)
          destruct (Nat.eq_dec n0 n) as [Heq|Hne].
          * subst n0.
            rewrite H in Hp. inversion Hp; subst np0.
            rewrite H0 in Hg0. inversion Hg0; subst ns_at_gs0.
            destruct (IH n np ns') as (tau & ns_at_gs & Htau & Hg);
              [exact H | cbn; apply map.get_put_same|].
            exists (O_event outs :: tau), ns_at_gs.
            split; [econstructor; [exact H1|exact Htau]|exact Hg].
          * destruct (IH n np ns_at_gs0 Hp) as (tau & ns_at_gs & Htau & Hg).
            { cbn. rewrite map.get_put_diff by auto. exact Hg0. }
            exists tau, ns_at_gs. split; auto.
        + (* gstep_receive: variables n, np, ns, ns', m, ms1, ms2 *)
          destruct (Nat.eq_dec n0 n) as [Heq|Hne].
          * subst n0.
            rewrite H in Hp. inversion Hp; subst np0.
            rewrite H0 in Hg0. inversion Hg0; subst ns_at_gs0.
            destruct (IH n np ns') as (tau & ns_at_gs & Htau & Hg);
              [exact H | cbn; apply map.get_put_same|].
            exists (I_event m :: tau), ns_at_gs.
            split; [econstructor; [exact H1|exact Htau]|exact Hg].
          * destruct (IH n np ns_at_gs0 Hp) as (tau & ns_at_gs & Htau & Hg).
            { cbn. rewrite map.get_put_diff by auto. exact Hg0. }
            exists tau, ns_at_gs. split; auto.
    Qed.

    (* The transport lemma we actually use in the theorem.
       Currently Admitted: see comments below. *)
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
    Proof. Admitted.

    (* An env-only trace using the env-input sequence of an existing trace
       is always reachable in graph 1.  [gstep_input] only checks
       [input_allowed n m = true], independent of state, so any env-input
       sequence taken by graph 2 can be replayed in graph 1.  Other steps
       (gstep_run / gstep_receive) emit O_events and don't contribute to
       [inputs_of], so we simply skip them in the replay. *)
    Lemma env_only_lift_gen :
      forall t gs0 gs2,
        star (graph_step p2 node_step2) gs0 t gs2 ->
        forall gs1_0,
        exists T1 gs1,
          star (graph_step p1 node_step1) gs1_0 T1 gs1 /\
          inputs_of T1 = inputs_of t.
    Proof.
      induction 1 as [s|s e s' t0 s'' Hstep Hstar IH]; intros gs1_0.
      - exists [], gs1_0. split; [constructor|reflexivity].
      - inversion Hstep; subst.
        + (* gstep_input n m *)
          destruct (IH {| g_nodes := g_nodes gs1_0;
                          g_messages := (n, m) :: g_messages gs1_0 |})
            as (T1' & gs1' & HT1' & Hinp).
          exists (I_event m :: T1'), gs1'.
          split.
          * econstructor; [|exact HT1']. apply gstep_input; auto.
          * cbn. f_equal. exact Hinp.
        + (* gstep_run *)
          destruct (IH gs1_0) as (T1 & gs1 & HT1 & Hinp).
          exists T1, gs1. split; [exact HT1|]. cbn. exact Hinp.
        + (* gstep_receive *)
          destruct (IH gs1_0) as (T1 & gs1 & HT1 & Hinp).
          exists T1, gs1. split; [exact HT1|]. cbn. exact Hinp.
    Qed.

    Lemma env_only_lift :
      forall t gs2,
        star (graph_step p2 node_step2) initial_gs2 t gs2 ->
        exists T1 gs1,
          star (graph_step p1 node_step1) initial_gs1 T1 gs1 /\
          inputs_of T1 = inputs_of t.
    Proof.
      intros. eapply env_only_lift_gen; eauto.
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
      - (* MUST: D(inputs_of t, o) -> node_will_output graph_step2 gs2 t o.
           Plan: env-only-lift t to a graph 1 trace T1 with the same env
           inputs; apply graph 1 ⊨ D's must side to get the graph 1
           will-output proof; then transport across via the per-node
           simulation. *)
        intros o Hd.
        destruct (env_only_lift _ _ Hstar2) as (T1 & gs1 & HT1star & Heqinputs).
        eapply will_output_transport; try eassumption.
        exists T1, gs1; repeat split; auto.
        destruct (H1 _ _ HT1star (Ha _)) as [Hmust1 _].
        apply Hmust1.
        rewrite Heqinputs; exact Hd.
      - (* MAY: node_might_output graph_step2 gs2 t o -> D(inputs_of t, o).
           Use Hmono [] (inputs_of t) o; the smaller-input D([], o) is then
           obtained from graph 1 ⊨ D's may side at the INITIAL state.  The
           may-witness for graph 1 (any trace producing o from initial) is
           obtained from graph 2 via [ever_produces_same]. *)
        intros o Hmight.
        destruct Hmight as (t' & gs2' & Hstar' & _ & Hout).
        apply (Hmono [] (inputs_of t) o); [|apply incl_nil_l].
        destruct (H1 [] initial_gs1 (star_refl _ _) (Ha _)) as [_ Hmay1].
        apply Hmay1.
        assert (exists T2 gs2'',
                   star (graph_step p2 node_step2) initial_gs2 T2 gs2'' /\
                   output_in_trace o T2) as Hgraph2_out.
        { exists (t ++ t'), gs2'. split.
          - eapply star_app; eauto.
          - apply output_in_trace_app.
            apply output_in_trace_app in Hout as [|]; auto. }
        apply (proj2 (ever_produces_same A_univ Hcorr o)) in Hgraph2_out.
        destruct Hgraph2_out as (T1 & gs1 & HT1star & HT1out).
        exists T1, gs1; repeat split; auto.
        rewrite app_nil_r; exact HT1out.
    Qed.
  End graphs.
End __.
