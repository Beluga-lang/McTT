From Coq Require Import Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses SetoidTactics.

From Mcltt Require Import Base LibTactics.
From Mcltt.Core.Completeness Require Import FundamentalTheorem.
From Mcltt.Core.Semantic Require Import Realizability.
From Mcltt.Core.Soundness Require Import LogicalRelation.
From Mcltt.Core.Syntactic Require Import Corollaries.
Import Domain_Notations.

Lemma glu_rel_ctx_empty : {{ ⊩ ⋅ }}.
Proof.
  do 2 econstructor; reflexivity.
Qed.

#[export]
Hint Resolve glu_rel_ctx_empty : mcltt.

Lemma glu_rel_ctx_extend : forall {Γ A i},
    {{ ⊩ Γ }} ->
    {{ Γ ⊩ A : Type@i }} ->
    {{ ⊩ Γ, A }}.
Proof.
  intros * [Sb] HA.
  assert {{ Γ ⊢ A : Type@i }} by mauto.
  invert_glu_rel_exp HA.
  eexists.
  econstructor; mauto; try reflexivity.
Qed.

#[export]
Hint Resolve glu_rel_ctx_extend : mcltt.