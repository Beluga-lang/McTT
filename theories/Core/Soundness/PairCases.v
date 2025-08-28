From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Soundness Require Import
  ContextCases
  LogicalRelation
  SubstitutionCases
  SubtypingCases
  TermStructureCases
  UniverseCases
  FunctionCases.
Import Domain_Notations.

Lemma glu_rel_exp_sigma : forall {Γ A B i},
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ, A ⊩ B : Type@i }} ->
    {{ Γ ⊩ Σ A B : Type@i }}.
Proof.
  intros * HA HB.
  assert {{ ⊩ Γ }} as [SbΓ] by mauto.
  assert {{ Γ ⊢ A : Type@i }} by mauto.
  invert_glu_rel_exp HA.
  assert {{ EG Γ, A ∈ glu_ctx_env ↘ cons_glu_sub_pred i Γ A SbΓ }} by (econstructor; mauto; reflexivity).
  assert {{ Γ, A ⊢ B : Type@i }} by mauto.
  invert_glu_rel_exp HB.
  eapply glu_rel_exp_of_typ; mauto 3.
  intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 4.
  split; mauto 3.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
  handle_functional_glu_univ_elem.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  rename m into a.
  assert {{ Γ ⊨ Σ A B : Type@i }} as [env_relΓ]%rel_exp_of_typ_inversion1 by mauto 3 using completeness_fundamental_exp.
  assert {{ Γ, A ⊨ B : Type@i }} as [env_relΓA]%rel_exp_of_typ_inversion1 by mauto 3 using completeness_fundamental_exp.
  destruct_conjs.
  match_by_head1 (per_ctx_env env_relΓA) invert_per_ctx_env.
  pose env_relΓA.
  assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  simplify_evals.
  eexists; repeat split; mauto.
  intros.
  match_by_head1 glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
  handle_per_univ_elem_irrel.
  handle_functional_glu_univ_elem.
Admitted.

#[export]
Hint Resolve glu_rel_exp_sigma : mctt.

Lemma glu_rel_exp_pair : forall {Γ M N A B i},
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ, A ⊩ B : Type@i }} ->
    {{ Γ ⊩ M : A }} ->
    {{ Γ ⊩ N : B[Id,,M] }} ->
    {{ Γ ⊩ ⟨ M ; N : B ⟩ : Σ A B }}.
Proof.
Admitted.

#[export]
Hint Resolve glu_rel_exp_pair : mctt.

Lemma glu_rel_exp_fst : forall {Γ M A B i},
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ, A ⊩ B : Type@i }} ->
    {{ Γ ⊩ M : Σ A B }} ->
    {{ Γ ⊩ fst M : A }}.
Proof.
Admitted.

#[export]
Hint Resolve glu_rel_exp_fst : mctt.

Lemma glu_rel_exp_snd : forall {Γ M A B i},
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ, A ⊩ B : Type@i }} ->
    {{ Γ ⊩ M : Σ A B }} ->
    {{ Γ ⊩ snd M : B[Id,,fst M] }}.
Proof.
Admitted.

#[export]
Hint Resolve glu_rel_exp_snd : mctt.
