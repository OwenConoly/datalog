From Stdlib Require Import List.
From Datalog Require Import List Datalog Smallstep.
From coqutil Require Import Map.Interface.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
Import ListNotations.

Section __.
  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.
  Context {node_name : Type}.

  Implicit Types mf_rel : rel.
  Implicit Types mf_args : list (option T).
  Implicit Types nf_args : list T.

  Inductive dfact :=
  | normal_dfact (nf_rel : rel) (nf_args : list T)
  | meta_dfact (mf_rel : rel) (mf_args : list (option T)) (source : node_name) (expected_msgs : nat).

  Implicit Types known_facts sent_facts input_facts inputs : list dfact.
  Implicit Types nf result : dfact.

  (* A node holds the facts it has received ([known_facts]) and the facts it has
     deduced/output ([sent_facts]).  There is no internal receive queue: an arrival
     ([I_event]) is delivered straight into [known_facts].  The old [waiting_facts]
     staging buffer plus its [sl_dequeue] step existed only to sequentialize a
     node's own outputs (FIFO), a role the distributed model dropped in favour of
     count-based completion, and which the graph's [gns_queue] otherwise duplicates. *)
  Record node_state :=
    { known_facts : list dfact;
      sent_facts : list dfact }.

  Context (R_senders : rel -> list node_name).

  Definition expect_num_R_facts R mf_args known_facts num :=
    exists expected_msgss,
      Forall2 (fun n expected_msgs => In (meta_dfact R mf_args n expected_msgs) known_facts) (R_senders R) expected_msgss /\
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

  Definition can_deduce_normal_fact (r : rule) (known_facts : list dfact) nf_rel nf_args :=
    exists hyps,
      non_meta_rule_impl r nf_rel nf_args hyps /\
        Forall (knows_datalog_fact known_facts) hyps.

  Definition can_deduce_meta_fact (mf_concls mf_hyps : list meta_clause) (node : node_name) (sent_facts : list dfact) (result : dfact) (hyps : list fact) :=
    exists ctx mf_rel mf_args mf_cnt,
      result = meta_dfact mf_rel mf_args node mf_cnt /\
        Existsn (dfact_matches mf_rel mf_args) mf_cnt sent_facts /\
        Exists (fun c => interp_meta_clause ctx c (meta_fact mf_rel mf_args (fun _ => False))) mf_concls /\
        Forall2 (interp_meta_clause ctx) mf_hyps hyps.

  Definition ok_to_deduce_fact (r : rule) known sent f :=
    match f with
    | normal_dfact nf_rel nf_args => True
    | meta_dfact mf_rel mf_args source num_msgs =>
        forall nf_args,
          can_deduce_normal_fact r known mf_rel nf_args ->
          Forall2 matches mf_args nf_args ->
          In (normal_dfact mf_rel nf_args) sent
    end.

  Definition can_deduce_fact (r : rule) node known sent f :=
    match f with
    | normal_dfact nf_rel nf_args =>
        can_deduce_normal_fact r known nf_rel nf_args /\
          forall mf_args num,
            In (meta_dfact nf_rel mf_args node num) sent ->
            Forall2 matches mf_args nf_args ->
            False
    | meta_dfact mf_rel mf_args source num_msgs =>
        source = node /\
          exists mr_concls mr_hyps hyps,
            r = meta_rule mr_concls mr_hyps /\
              can_deduce_meta_fact mr_concls mr_hyps node sent f hyps /\
              Forall (knows_datalog_fact known) hyps
    end.

  Record node_prog :=
    { np_rules : list rule;
      np_name : node_name }.

  Definition new_facts (sp : node_prog) (rs : node_state) f :=
    Exists
      (fun r => can_deduce_fact r sp.(np_name) rs.(known_facts) rs.(sent_facts) f)
      sp.(np_rules) /\
      Forall
        (fun r => ok_to_deduce_fact r rs.(known_facts) rs.(sent_facts) f)
        sp.(np_rules).

  Variant node_label :=
    | sl_deduce (f : dfact).

  Local Notation IO_event := (Smallstep.IO_event node_label dfact).

  Inductive node_step (sp : node_prog) : node_state -> IO_event -> node_state -> Prop :=
  | node_deduce_step rs output :
    new_facts sp rs output ->
    node_step sp rs (O_event (sl_deduce output) [output])
                   {| known_facts := rs.(known_facts);
                     sent_facts := output :: rs.(sent_facts) |}
  | node_input_step rs input :
    node_step sp rs (I_event input)
                   {| known_facts := input :: rs.(known_facts);
                     sent_facts := rs.(sent_facts) |}.

  Definition allowed_inputs (input_facts : list dfact) :=
    (forall R mf_args k num num0,
        In (meta_dfact R mf_args k num) input_facts ->
        In (meta_dfact R mf_args k num0) input_facts -> num0 = num)
    /\
    (forall R mf_args expected_msgss,
        Forall2 (fun k e => In (meta_dfact R mf_args k e) input_facts)
                (R_senders R) expected_msgss ->
        exists num', num' <= fold_left Nat.add expected_msgss 0 /\
                     Existsn (dfact_matches R mf_args) num' input_facts).

  Definition dfact_equiv (f1 f2 : dfact) : Prop :=
    match f1, f2 with
    | meta_dfact R1 a1 s1 _, meta_dfact R2 a2 s2 _ => R1 = R2 /\ a1 = a2 /\ s1 = s2
    | _, _ => f1 = f2
    end.

  Definition dfact_consistent (c l : list dfact) : Prop :=
    forall R mf_args num,
      expect_num_R_facts R mf_args c num ->
      Existsn (dfact_matches R mf_args) num l.

  Definition node_init : node_state :=
    {| known_facts := []; sent_facts := [] |}.

  (* ---- The le-simulation, mirroring Graph.v. ----

     Graph.v compares nodes by [inputs_of gns_trace] (the messages the node has
     received) for [le], and by [inputs_of gns_trace ++ gns_queue] (those plus
     messages delivered-but-not-yet-consumed) for [le_weak].  A standalone node
     has no delivery buffer -- every arrival is delivered straight into
     [known_facts] -- so [known_facts ~ inputs_of t] is the node's whole input
     trace, and BOTH orderings compare it, differing only in the relation:
     [nle_weak] uses [incl_mod_weak] (domination up to [dfact_equiv]), [nle] uses
     [incl_mod ... dfact_consistent] (consistency-respecting domination).
     [sent_facts] -- the node's outputs -- stays out of both; outputs are
     regenerated by re-running, not compared (as [outputs_of gns_trace] is at the
     graph level).

     [nle] on [known_facts] (= [inputs_of t]) is what makes the [le_node_output]
     analogue coincide with [might_implies_will_equiv'], whose domination
     hypothesis is exactly [incl_mod dfact_equiv dfact_consistent (inputs_of t1)
     (inputs_of t2)]. *)

  Definition nle_weak (s1 s2 : node_state) : Prop :=
    incl_mod_weak dfact_equiv s1.(known_facts) s2.(known_facts).

  Definition nle (s1 s2 : node_state) : Prop :=
    incl_mod dfact_equiv dfact_consistent s1.(known_facts) s2.(known_facts).

  (* Analogue of Graph.v's [node_will_match']: after [s1] takes one output step,
     a dominating [s2] can be driven to re-dominate [s1'] in the weak ordering.
     At the single node this is trivial: the only output step is a deduce, which
     touches only [sent_facts] and leaves [known_facts] (hence [nle_weak])
     unchanged.  [nle s1 s2] is kept for a faithful mirror of Graph.v and is
     expected to be unnecessary here. *)
  Lemma node_will_match' (np : node_prog) s1 t1 lbl outs s1' s2 t2 :
    star (node_step np) node_init t1 s1 ->
    star (node_step np) node_init t2 s2 ->
    allowed_inputs (inputs_of t1) ->
    allowed_inputs (inputs_of t2) ->
    node_step np s1 (O_event lbl outs) s1' ->
    nle s1 s2 ->
    nle_weak s1 s2 ->
    eventually (will_step (node_step np) allowed_inputs)
      (fun '(s2', _) => nle_weak s1' s2') (s2, t2).
  Admitted.

  Lemma node_might_implies_will (np : node_prog) :
    meta_rules_valid np.(np_rules) ->
    might_implies_will_equiv (node_step np) dfact_equiv allowed_inputs node_init.
  Admitted.

End __.
