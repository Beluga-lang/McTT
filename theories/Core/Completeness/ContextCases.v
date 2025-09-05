From Coq Require Import Morphisms_Relations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import LogicalRelation UniverseCases.
Import Domain_Notations.

Proposition valid_ctx_empty :
  {{ ⊨ ⋅ }}.
Proof.
  do 2 econstructor.
  apply Equivalence_Reflexive.
Qed.

#[export]
Hint Resolve valid_ctx_empty : mctt.

Lemma rel_ctx_extend : forall {Γ Γ' A A' i},
    {{ ⊨ Γ ≈ Γ' }} ->
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ ⊨ Γ, A ≈ Γ', A' }}.
Proof with intuition.
  intros * [env_relΓ] HA.
  invert_rel_exp_of_typ HA.
  assert (exists (elem_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}), relation domain), forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}), rel_typ i A ρ A' ρ' (elem_rel equiv_ρ_ρ')) as []
    by (saturate_refl_for per_ctx_env; eapply rel_exp_under_ctx_implies_rel_typ_under_ctx; mauto 3).
  eexists.
  per_ctx_env_econstructor; eauto.
  solve_refl.
Qed.

Lemma rel_ctx_extend' : forall {Γ A i},
    {{ Γ ⊨ A : Type@i }} ->
    {{ ⊨ Γ, A }}.
Proof.
  intros.
  eapply rel_ctx_extend; eauto.
  destruct H as [? []].
  eexists. eassumption.
Qed.

#[export]
Hint Resolve rel_ctx_extend rel_ctx_extend' : mctt.

Lemma rel_ctx_sub_empty :
  {{ SubE ⋅ <: ⋅ }}.
Proof. mauto. Qed.

Lemma rel_ctx_sub_extend : forall Γ Δ i A A',
  {{ SubE Γ <: Δ }} ->
  {{ Γ ⊨ A : Type@i }} ->
  {{ Δ ⊨ A' : Type@i }} ->
  {{ Γ ⊨ A ⊆ A' }} ->
  {{ SubE Γ , A <: Δ , A' }}.
Proof.
  intros * ? []%rel_ctx_extend' []%rel_ctx_extend' [env_relΓ].
  pose env_relΓ.
  destruct_conjs.
  econstructor; try eassumption.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_exp.
  simplify_evals.
  eassumption.
Qed.

#[export]
Hint Resolve rel_ctx_sub_empty rel_ctx_sub_extend : mctt.
