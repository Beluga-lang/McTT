From Coq Require Import Morphisms Morphisms_Relations RelationClasses Relation_Definitions.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness.LogicalRelation Require Import Definitions Tactics.
Import Domain_Notations.

Add Parametric Morphism M ρ M' ρ' : (rel_exp M ρ M' ρ')
    with signature (@relation_equivalence domain) ==> iff as rel_exp_morphism.
Proof.
  intros R R' HRR'.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism σ ρ σ' ρ' : (rel_sub σ ρ σ' ρ')
    with signature (@relation_equivalence env) ==> iff as rel_sub_morphism.
Proof.
  intros R R' HRR'.
  split; intros []; econstructor; intuition.
Qed.

Lemma rel_exp_implies_rel_typ : forall {i A ρ A' ρ'},
    rel_exp A ρ A' ρ' (per_univ i) ->
    exists R, rel_typ i A ρ A' ρ' R.
Proof.
  intros.
  destruct_by_head rel_exp.
  destruct_by_head per_univ.
  mauto.
Qed.

#[export]
Hint Resolve rel_exp_implies_rel_typ : mctt.

Lemma rel_typ_implies_rel_exp : forall {i A ρ A' ρ' R},
    rel_typ i A ρ A' ρ' R ->
    rel_exp A ρ A' ρ' (per_univ i).
Proof.
  intros.
  destruct_by_head rel_typ.
  mauto.
Qed.

#[export]
Hint Resolve rel_typ_implies_rel_exp : mctt.

Lemma rel_exp_clean_inversion : forall {Γ env_rel A M M'},
    {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }} ->
    {{ Γ ⊨ M ≈ M' : A }} ->
    exists i,
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
    exists (elem_rel : relation domain),
      rel_typ i A ρ A ρ' elem_rel /\ rel_exp M ρ M' ρ' elem_rel.
Proof.
  intros * ? [].
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists.
  eassumption.
Qed.

Ltac invert_rel_exp H :=
  (unshelve (epose proof (rel_exp_clean_inversion _ H); deex); shelve_unifiable; [eassumption |]; clear H)
  + dependent destruction H.
