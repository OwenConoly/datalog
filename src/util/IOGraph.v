From coqutil Require Import Semantics.OmniSmallstepCombinators.
From coqutil Require Import Eqb Tactics Tactics.fwd.
From Stdlib Require Import List Permutation Relations.
From Datalog Require Import Smallstep FinTypeclass Function List Relations Eqb Tactics.
From Datalog Require Import MessagelessSmallstep.
Import ListNotations.

Definition nodeT := Type. Existing Class nodeT.
#[global] Typeclasses Transparent nodeT.

Section withNode.
  Context {node : nodeT}.

  Variant source :=
    | node_source (_ : node)
    | input_source.

  Variant destn :=
    | node_destn (_ : node)
    | output_destn.

  Variant location :=
    | node_loc (_ : node)
    | input_loc
    | output_loc.

  Definition loc_of_source (s : source) : location :=
    match s with
    | node_source n => node_loc n
    | input_source => input_loc
    end.

  Lemma loc_of_source_inj s1 s2 :
    loc_of_source s1 = loc_of_source s2 -> s1 = s2.
  Proof. destruct s1, s2; simpl; congruence. Qed.

  Definition loc_of_dest (d : destn) : location :=
    match d with
    | node_destn n => node_loc n
    | output_destn => output_loc
    end.

  Lemma loc_of_dest_inj d1 d2 :
    loc_of_dest d1 = loc_of_dest d2 -> d1 = d2.
  Proof. destruct d1, d2; simpl; congruence. Qed.

  Definition source_of_loc (l : location) : option source :=
    match l with
    | node_loc n => Some (node_source n)
    | input_loc => Some input_source
    | output_loc => None
    end.

  Lemma source_of_loc_iff l s :
    source_of_loc l = Some s <-> loc_of_source s = l.
  Proof. destruct l, s; simpl; split; congruence. Qed.

  Definition dest_of_loc (l : location) : option destn :=
    match l with
    | node_loc n => Some (node_destn n)
    | input_loc => None
    | output_loc => Some output_destn
    end.

  Lemma dest_of_loc_iff l d :
    dest_of_loc l = Some d <-> loc_of_dest d = l.
  Proof. destruct l, d; simpl; split; congruence. Qed.
End withNode.

Scheme Boolean Equality for source.
Scheme Boolean Equality for destn.
Scheme Boolean Equality for location.

Section withNode.
  Context {node : nodeT} {node_eqb : Eqb node} {node_eqb_ok : Eqb_ok node_eqb}.

  #[export] Instance source_eqb : Eqb source := source_beq _ eqb.
  #[export] Instance source_eqb_ok : Eqb_ok source_eqb.
  Proof. eqb_ok. Qed.

  #[export] Instance destn_eqb : Eqb destn := destn_beq _ eqb.
  #[export] Instance destn_eqb_ok : Eqb_ok destn_eqb.
  Proof. eqb_ok. Qed.

  #[export] Instance location_eqb : Eqb location := location_beq _ eqb.
  #[export] Instance location_eqb_ok : Eqb_ok location_eqb.
  Proof. eqb_ok. Qed.
End withNode.

Section withNode.
  Context {node : nodeT} {node_fin : Fin.Fin node}.

  #[export, refine] Instance source_Fin : Fin.Fin source :=
    {| Fin.all := input_source :: map node_source (Fin.all node) |}.
  Proof.
    - constructor.
      + rewrite in_map_iff. intros (? & ? & _). discriminate.
      + apply Finite.Injective_map_NoDup; [ | apply Fin.all_NoDup ].
        intros ? ? H. congruence.
    - intros [n|].
      + right. apply in_map, Fin.all_Full.
      + left. reflexivity.
  Defined.
End withNode.
