From Stdlib Require Import List.
From Datalog Require Import List Datalog Smallstep.
From coqutil Require Import Map.Interface.
Import ListNotations.

Section __.
  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.

  Implicit Types mf_rel : rel.
  Implicit Types mf_args : list (option T).
  Implicit Types nf_args : list T.

  Inductive dfact :=
  | normal_dfact (nf_rel : rel) (nf_args : list T)
  | meta_dfact (mf_rel : rel) (mf_args : list (option T)) (source : option nat) (expected_msgs : nat).

  Implicit Types known_facts sent_facts waiting_facts input_facts inputs : list dfact.
  Implicit Types nf result : dfact.

  Record node_state :=
    { known_facts : list dfact;
      waiting_facts : list dfact;
      sent_facts : list dfact }.

  Definition learn_fact_at_rule (s1 s2 : node_state) : Prop :=
    exists l1 x l2,
      s2.(known_facts) = x :: s1.(known_facts) /\
        s1.(waiting_facts) = l1 ++ x :: l2 /\
        s2.(waiting_facts) = l1 ++ l2 /\
        s2.(sent_facts) = s1.(sent_facts).

  Context (is_input : rel -> bool).
  Context (R_senders : rel -> list nat).

  Definition expect_num_R_facts R mf_args known_facts num :=
    if is_input R then
      In (meta_dfact R mf_args None num) known_facts
    else
      exists expected_msgss,
        Forall2 (fun n expected_msgs => In (meta_dfact R mf_args (Some n) expected_msgs) known_facts) (R_senders R) expected_msgss /\
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

  Definition can_deduce_meta_fact (mf_concls mf_hyps : list meta_clause) (node: nat) (sent_facts : list dfact) (result : dfact) (hyps : list fact) :=
    exists ctx mf_rel mf_args mf_cnt,
      result = meta_dfact mf_rel mf_args (Some node) mf_cnt /\
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
            In (meta_dfact nf_rel mf_args (Some node) num) sent ->
            Forall2 matches mf_args nf_args ->
            False
    | meta_dfact mf_rel mf_args source num_msgs =>
        source = Some node /\
          exists mr_concls mr_hyps hyps,
            r = meta_rule mr_concls mr_hyps /\
              can_deduce_meta_fact mr_concls mr_hyps node sent f hyps /\
              Forall (knows_datalog_fact known) hyps
    end.

  Record spec_node_prog :=
    { spec_node_rules : list rule;
      spec_node_label : nat }.

  Definition new_facts (sp : spec_node_prog) (rs : node_state) f :=
    Exists
      (fun r => can_deduce_fact r sp.(spec_node_label) rs.(known_facts) rs.(sent_facts) f)
      sp.(spec_node_rules) /\
      Forall
        (fun r => ok_to_deduce_fact r rs.(known_facts) rs.(sent_facts) f)
        sp.(spec_node_rules).

  Variant spec_label :=
    | sl_dequeue
    | sl_deduce (f : dfact).

  Local Notation IO_event := (Smallstep.IO_event spec_label dfact).

  Inductive spec_node_step (sp : spec_node_prog) : node_state -> IO_event -> node_state -> Prop :=
  | spec_node_dequeue_step rs input rest :
    rs.(waiting_facts) = input :: rest ->
    spec_node_step sp rs (O_event sl_dequeue [])
                   {| known_facts := input :: rs.(known_facts);
                     waiting_facts := rest;
                     sent_facts := rs.(sent_facts) |}
  | spec_node_deduce_step rs output :
    new_facts sp rs output ->
    spec_node_step sp rs (O_event (sl_deduce output) [output])
                   {| known_facts := rs.(known_facts);
                     waiting_facts := rs.(waiting_facts);
                     sent_facts := output :: rs.(sent_facts) |}
  | spec_node_input_step rs input :
    spec_node_step sp rs (I_event input)
                   {| known_facts := rs.(known_facts);
                     waiting_facts := rs.(waiting_facts) ++ [input];
                     sent_facts := rs.(sent_facts) |}.

  Definition consistent_inputs (input_facts : list dfact) : Prop :=
    (forall R mf_args num,
        In (meta_dfact R mf_args None num) input_facts ->
        (forall num0, In (meta_dfact R mf_args None num0) input_facts -> num0 = num) /\
          exists num', num' <= num /\ Existsn (dfact_matches R mf_args) num' input_facts)
    /\
    (forall R mf_args k num num0,
        In (meta_dfact R mf_args (Some k) num) input_facts ->
        In (meta_dfact R mf_args (Some k) num0) input_facts -> num0 = num)
    /\
    (forall R mf_args expected_msgss,
        Forall2 (fun k e => In (meta_dfact R mf_args (Some k) e) input_facts)
                (R_senders R) expected_msgss ->
        exists num', num' <= fold_left Nat.add expected_msgss 0 /\
                     Existsn (dfact_matches R mf_args) num' input_facts).

  Definition node_allowed (inputs : list dfact) : Prop :=
    consistent_inputs inputs.

  Definition dfact_equiv (f1 f2 : dfact) : Prop :=
    match f1, f2 with
    | meta_dfact R1 a1 s1 _, meta_dfact R2 a2 s2 _ => R1 = R2 /\ a1 = a2 /\ s1 = s2
    | _, _ => f1 = f2
    end.

  Definition dfact_consistent (a l : list dfact) : Prop :=
    forall R margs source num,
      In (meta_dfact R margs source num) a ->
      Existsn (dfact_matches R margs) num l.

  Definition node_init : node_state :=
    {| known_facts := []; waiting_facts := []; sent_facts := [] |}.

End __.
