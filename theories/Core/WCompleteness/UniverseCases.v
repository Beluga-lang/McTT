From Coq Require Import Morphisms_Relations RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.WCompleteness Require Import LogicalRelation.
Import Domain_Notations.

Lemma rel_exp_of_typ_inversion : forall {Γ A A' i},
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    exists env_rel (_ : {{ EF Γ ≈≈ Γ ∈ per_ctx_env ↘ env_rel }}),
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈≈ ρ' ∈ env_rel }}),
      rel_exp A ρ A' ρ' (per_univ i).
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists;
  eexists; [eassumption |].
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body_nouip.
  eassumption.
Qed.

Lemma rel_exp_of_typ : forall {Γ A A' i},
    (exists env_rel (_ : {{ EF Γ ≈≈ Γ ∈ per_ctx_env ↘ env_rel }}),
      forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈≈ ρ' ∈ env_rel }}),
        rel_exp A ρ A' ρ' (per_univ i)) ->
    {{ Γ ⊨ A ≈ A' : Type@i }}.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_exp.
  intros.
  eexists; split; eauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve rel_exp_of_typ : mctt.

Ltac eexists_rel_exp_of_typ :=
  apply rel_exp_of_typ;
  eexists;
  eexists; [eassumption |].

Lemma valid_exp_typ : forall {i Γ},
    {{ ⊨ Γ }} ->
    {{ Γ ⊨ Type@i : Type@(S i) }}.
Proof.
  intros * [].
  eexists_rel_exp_of_typ.
  intros.
  econstructor; mauto.
  eexists.
  per_univ_elem_econstructor; eauto.
  apply Equivalence_Reflexive.
Qed.

#[export]
Hint Resolve valid_exp_typ : mctt.

Lemma rel_exp_typ_sub : forall {i Γ σ Δ},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Γ ⊨ Type@i[σ] ≈ Type@i : Type@(S i) }}.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_exp_of_typ.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  econstructor; mauto.
  eexists.
  per_univ_elem_econstructor; eauto.
  apply Equivalence_Reflexive.
Qed.

#[export]
Hint Resolve rel_exp_typ_sub : mctt.

Lemma rel_exp_cumu : forall {i Γ A A'},
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ A ≈ A' : Type@(S i) }}.
Proof.
  intros * [env_relΓ]%rel_exp_of_typ_inversion.
  destruct_conjs.
  eexists_rel_exp_of_typ.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head per_univ.
  match_by_head per_univ_elem ltac:(fun H => apply per_univ_elem_cumu in H).
  econstructor; mauto.
Qed.

#[export]
Hint Resolve rel_exp_cumu : mctt.
