From Stdlib Require Import Lists.List.
From Datalog.Util Require Import Pftree.

From coqutil Require Import Map.Interface Tactics Tactics.fwd Datatypes.List.

From Datalog Require Import Map Tactics List Datalog.

Import ListNotations.

(*names the witness of an existential variable by the rule instance that introduces it*)
Module label.
  Record label {relt : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {value : valueT} := mk
    { rule : rule;
      var : exprvar;
      hyps : list normal_fact }.
End label. Abbreviation label := label.label.

Class existential_semantics {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {value : valueT} :=
  { null : label -> value }.
Arguments existential_semantics : clear implicits.

Module existential.
  Section __.
    Context `{params : datalog_params} {ex : existential_semantics rel exprvar fn aggregator value}.

    (*a conclusion variable the hypotheses don't bind is existential: it denotes the null labeled
      by the rule instance, so one instance names one witness, shared by all its conclusions*)
    Definition nulls_ok (r : rule) (hyps : list normal_fact) (ctx : context) (c : clause) :=
      forall x,
        In x (clause.vars c) ->
        ~ In x (rule.hyp_vars r) ->
        map.get ctx x = Some (null {| label.rule := r; label.var := x; label.hyps := hyps |}).

    Variant rule_interp : rule -> normal_fact -> list fact -> Prop :=
      | rule_interp_impl rule_concls rule_hyps ctx c nf hyps :
        In c rule_concls ->
        nulls_ok (rule.impl rule_concls rule_hyps) hyps ctx c ->
        clause.interp ctx c nf ->
        Forall2 (clause.interp ctx) rule_hyps hyps ->
        rule_interp (rule.impl rule_concls rule_hyps) nf (map fact.normal hyps)
      | rule_interp_agg concl_rel a hyp_rel nf hyps :
        rule.interp (rule.agg concl_rel a hyp_rel) nf hyps ->
        rule_interp (rule.agg concl_rel a hyp_rel) nf hyps.

    Definition one_step_derives (p : list rule) (mfs : list meta_fact) (nf : normal_fact) :=
      exists hyps,
        Exists (fun r => rule_interp r nf hyps) p /\
          Forall (fact.implied_by_mfs mfs) hyps.

    Definition meta_rule_interp prog (r : meta_rule) mf hyps :=
      meta_rule.pattern_interp r mf.(meta_fact.pattern) (map meta_fact.pattern hyps) /\
        forall nf,
          fact_pattern.matches mf.(meta_fact.pattern) nf ->
          fset.contains mf.(meta_fact.set) nf.(normal_fact.args) <->
            one_step_derives prog hyps nf.

    Variant interp_step (p : program) : fact -> list fact -> Prop :=
      | rule_step f hyps :
        Exists (fun r => rule_interp r f hyps) p.(program.rules) ->
        interp_step _ (fact.normal f) hyps
      | meta_rule_step f hyps :
        Exists (fun mr => meta_rule_interp p.(program.rules) mr f hyps) p.(program.meta_rules) ->
        interp_step _ (fact.meta f) (map fact.meta hyps).

    Abbreviation interp p := (pftree (interp_step p)).

    (*the universal reading of free conclusion variables over-approximates the existential one*)
    Lemma universal_of_rule_interp r nf hyps :
      rule_interp r nf hyps ->
      rule.interp r nf hyps.
    Proof.
      invert 1; [|assumption]. econstructor; [|eassumption]. apply Exists_exists. eauto.
    Qed.

    (*the two readings agree on bottom-up rules, which have no existential variables*)
    Lemma rule_interp_bottomup r nf hyps :
      rule.is_bottomup r ->
      rule_interp r nf hyps <-> rule.interp r nf hyps.
    Proof.
      intros Hbu. split; [apply universal_of_rule_interp|]. intros H.
      destruct r; [|constructor; assumption]. invert H. rewrite Exists_exists in *. fwd.
      econstructor; try eassumption.
      intros y Hy Hnb. exfalso. apply Hnb. eauto using rule.is_bottomup_concl_vars_bound.
    Qed.

    Lemma one_step_derives_bottomup p mfs nf :
      Forall rule.is_bottomup p ->
      one_step_derives p mfs nf <-> rule.one_step_derives p mfs nf.
    Proof.
      intros Hbu. cbv [one_step_derives rule.one_step_derives].
      setoid_rewrite Exists_exists. rewrite Forall_forall in Hbu. split.
      - intros (hyps & (r & Hr & Hrr) & Himp). exists hyps. split; [|exact Himp].
        exists r. split; [exact Hr|]. apply rule_interp_bottomup; auto.
      - intros (hyps & (r & Hr & Hrr) & Himp). exists hyps. split; [|exact Himp].
        exists r. split; [exact Hr|]. apply rule_interp_bottomup; auto.
    Qed.

    Lemma meta_rule_interp_bottomup prog r mf hyps :
      Forall rule.is_bottomup prog ->
      meta_rule_interp prog r mf hyps <-> meta_rule.interp prog r mf hyps.
    Proof.
      intros Hbu. cbv [meta_rule_interp meta_rule.interp].
      setoid_rewrite one_step_derives_bottomup; [reflexivity|assumption].
    Qed.

    Lemma interp_step_bottomup p f hyps :
      Forall rule.is_bottomup p.(program.rules) ->
      interp_step p f hyps <-> program.interp_step p f hyps.
    Proof.
      intros Hbu. split; invert 1; constructor.
      - eapply Exists_impl; [|eassumption]. intros r. apply universal_of_rule_interp.
      - eapply Exists_impl; [|eassumption]. intros mr. apply meta_rule_interp_bottomup. assumption.
      - apply Exists_exists in H0. destruct H0 as (r & Hr & Hrr). apply Exists_exists. exists r.
        rewrite Forall_forall in Hbu. split; [assumption|]. apply rule_interp_bottomup; auto.
      - eapply Exists_impl; [|eassumption]. intros mr. apply meta_rule_interp_bottomup. assumption.
    Qed.

    Lemma interp_bottomup p Q f :
      Forall rule.is_bottomup p.(program.rules) ->
      interp p Q f <-> program.interp p Q f.
    Proof. intros. apply pftree.step_ext. auto using interp_step_bottomup. Qed.
  End __.
  Abbreviation interp p := (pftree (interp_step p)).
End existential.
