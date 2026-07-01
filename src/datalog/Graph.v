From coqutil Require Import Map.Interface.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
From Stdlib Require Import List PeanoNat Permutation.
From Stdlib Require Import RelationClasses.
From Datalog Require Import Smallstep Map.
Import ListNotations.

Definition node_id := nat.
Section __.
  Context {message : Type}.
  Context {label : Type}.
  Context (input_allowed : node_id -> message -> bool).
  Context (forward : node_id -> message -> list node_id).
  (* A message is forwarded to a given node at most once per emission. *)
  Context (forward_nodup : forall n m, NoDup (forward n m)).
  Context (output_visible : node_id -> message -> bool).

  Context (equiv : message -> message -> Prop).
  Context (equiv_equiv : Equivalence equiv).
  Context (output_visible_equiv :
             forall n a b, equiv a b -> output_visible n a = output_visible n b).
  Context (well_formed_output : node_id -> list message -> Prop).
  Context {constraint} (well_formed : constraint -> list message -> Prop).
  Context (well_formed_inputs : constraint -> list message -> Prop).

  Local Notation IO_event := (Smallstep.IO_event label message).

  Variant graph_label :=
    | receive (_ : node_id) (_ : message)
    | run (_ : node_id) (_ : label).

  Definition well_formed_graph_inputs (c : constraint) (inps : list (message * node_id)) :=
    forall n, well_formed_inputs c (map fst (filter (fun '(_, n') => Nat.eqb n n') inps)).

  Local Notation gevent := (Smallstep.IO_event graph_label (message * node_id)).

  Definition equiv_g : message * node_id -> message * node_id -> Prop :=
    fun '(m1, n1) '(m2, n2) => n1 = n2 /\ equiv m1 m2.

  Definition well_formed_good :=
    forall nodes fss,
      NoDup nodes ->
      Forall2 well_formed_output nodes fss ->
      forall c inps,
        well_formed c (concat fss ++ inps) <-> well_formed_inputs c inps.

  Context (Hwfg : well_formed_good).

  (* Same monotonicity hypothesis as in Smallstep: on [allowed] input multisets,
     growth preserves each well-formedness constraint. *)
  Context (well_formed_monotone :
    forall c l1 l2, allowed well_formed l1 -> allowed well_formed l2 ->
                    submultiset l1 l2 -> well_formed c l1 -> well_formed c l2).

  Section graph.
    Context {node_prog : Type} {graph_prog : map.map node_id node_prog}.
    (* Each node stores its state together with its own local IO trace (the events
       it has gone through, in forward order).  This makes a node's "projection"
       a pure function of the graph state: it is just [snd (g_nodes n)]. *)
    Context {node_state : Type}
            {node_states : map.map node_id (node_state * list IO_event)}.
    Context (p : graph_prog).
    Context (node_step : node_prog -> node_state -> IO_event -> node_state -> Prop).

    Record graph_state :=
      { g_nodes : node_states;
        g_messages : list (node_id (*destination*) * message) }.

    Inductive graph_step : graph_state -> gevent -> graph_state -> Prop :=
    | gstep_input gs n m :
      input_allowed n m = true ->
      graph_step gs (I_event (m, n))
                 {| g_nodes := gs.(g_nodes);
                   g_messages := (n, m) :: gs.(g_messages) |}
    | gstep_run gs n np ns t ns' lbl outs :
      map.get p n = Some np ->
      map.get gs.(g_nodes) n = Some (ns, t) ->
      node_step np ns (O_event lbl outs) ns' ->
      graph_step gs (O_event (run n lbl) (map (fun m => (m, n)) (filter (output_visible n) outs)))
                 {| g_nodes := map.put gs.(g_nodes) n (ns', t ++ [O_event lbl outs]);
                   g_messages := gs.(g_messages) ++
                                      flat_map (fun m => map (fun n' => (n', m)) (forward n m))
                                      outs |}
    | gstep_receive gs n np ns t ns' m ms1 ms2 :
      map.get p n = Some np ->
      map.get gs.(g_nodes) n = Some (ns, t) ->
      node_step np ns (I_event m) ns' ->
      gs.(g_messages) = ms1 ++ (n, m) :: ms2 ->
      graph_step gs (O_event (receive n m) [])
                 {| g_nodes := map.put gs.(g_nodes) n (ns', t ++ [I_event m]);
                   g_messages := ms1 ++ ms2 |}.
  End graph.

  (* The graph's allowed predicate: a tagged trace is allowed iff its underlying
     (untagged) inputs are allowed by A. *)

  Section graph.
    Context {node_prog : Type} {graph_prog : map.map node_id node_prog}.
    Context {node_state : Type}
            {node_states : map.map node_id (node_state * list IO_event)}.
    Context {node_states_ok : map.ok node_states}.
    Context (p : graph_prog) (initial_ns : node_states).
    (* The initial node states carry empty local traces. *)
    Context (initial_ns_empty :
               forall n x, map.get initial_ns n = Some x -> snd x = []).
    Context (node_step : node_prog -> node_state -> IO_event -> node_state -> Prop).
    Context (p_initial_dom :
               forall n np, map.get p n = Some np -> exists x, map.get initial_ns n = Some x).

    Definition initial_graph_state : graph_state :=
      {| g_nodes := initial_ns; g_messages := [] |}.

    (* Every node accepts every input in every state. *)
    Context (nodes_input_total :
               forall n np, map.get p n = Some np -> input_total (node_step np)).

    (* The per-node modulo-[equiv] liveness bundle: a node's own outputs are
       well-formed; its inputs are monotone modulo [equiv]; and it is live modulo
       [equiv]. *)
    Definition node_good (n : node_id) (np : node_prog) : node_state * list IO_event -> Prop :=
      fun '(ns, _) =>
        outputs_well_formed    (node_step np)       (fun (_ : unit) => well_formed_output n) ns /\
        monotone_mod_equiv     (node_step np) equiv well_formed ns /\
        can_implies_will_equiv (node_step np) equiv well_formed ns.

    (* The modulo-[equiv] whole-graph liveness: from the per-node [node_good] bundle,
       the graph is live up to [equiv_g] for well-formed external inputs. *)
    Lemma graph_can_implies_will_equiv :
      Forall2_map node_good p initial_ns ->
      can_implies_will_equiv (graph_step p node_step) equiv_g well_formed_graph_inputs
                             initial_graph_state.
    Admitted.
  End graph.

End __.

Definition translate_event {L M M'} (t : M' -> M) (ev : IO_event L M') : IO_event L M :=
  match ev with
  | I_event m' => I_event (t m')
  | O_event l ms' => O_event l (map t ms')
  end.

Definition translate_step {NS L M M'} (t : M' -> M)
  (step : NS -> IO_event L M -> NS -> Prop)
  : NS -> IO_event L M' -> NS -> Prop :=
  fun ns ev ns' => step ns (translate_event t ev) ns'.
