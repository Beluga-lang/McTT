From Coq Require Import Morphisms_Relations RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import ContextCases LogicalRelation UniverseCases.
Import Domain_Notations.

Lemma rel_sub_id : forall {Γ},
    {{ ⊨ Γ }} ->
    {{ Γ ⊨s Id ≈ Id : Γ }}.
Proof with mautosolve.
  intros * [].
  eexists_rel_sub...
Qed.

#[export]
Hint Resolve rel_sub_id : mctt.

Lemma rel_sub_weaken : forall {Γ A},
    {{ ⊨ Γ, A }} ->
    {{ Γ, A ⊨s Wk ≈ Wk : Γ }}.
Proof with mautosolve.
  intros * [env_relΓA].
  invert_per_ctx_envs.
  apply_relation_equivalence.
  eexists_rel_sub.
  intros.
  destruct_by_head cons_per_ctx_env...
Qed.

#[export]
Hint Resolve rel_sub_weaken : mctt.

Lemma rel_sub_compose_cong : forall {Γ τ τ' Γ' σ σ' Γ''},
    {{ Γ ⊨s τ ≈ τ' : Γ' }} ->
    {{ Γ' ⊨s σ ≈ σ' : Γ'' }} ->
    {{ Γ ⊨s σ ∘ τ ≈ σ' ∘ τ' : Γ'' }}.
Proof with mautosolve.
  intros * [env_relΓ [? [env_relΓ' []]]] Hσ.
  invert_rel_sub Hσ.
  eexists_rel_sub.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ')...
Qed.

#[export]
Hint Resolve rel_sub_compose_cong : mctt.

Lemma rel_sub_extend_cong : forall {i Γ M M' σ σ' Δ A},
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ Δ ⊨ A : Type@i }} ->
    {{ Γ ⊨ M ≈ M' : A[σ] }} ->
    {{ Γ ⊨s σ ,, M ≈ σ' ,, M' : Δ, A }}.
Proof with mautosolve.
  intros * [env_relΓ [? [env_relΔ []]]] HA HM.
  invert_rel_exp HM.
  assert {{ ⊨ Δ, A }} as [] by (eapply rel_ctx_extend; eauto; eexists; eauto).
  invert_rel_exp_of_typ HA.
  eexists_rel_sub.
  invert_per_ctx_envs.
  apply_relation_equivalence.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  invert_rel_typ_body_nouip.
  destruct_by_head rel_exp...
Qed.

#[export]
Hint Resolve rel_sub_extend_cong : mctt.

Lemma rel_sub_id_compose_right : forall {Γ σ Δ},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Γ ⊨s Id ∘ σ ≈ σ : Δ }}.
Proof with mautosolve.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_sub.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ)...
Qed.

#[export]
Hint Resolve rel_sub_id_compose_right : mctt.

Lemma rel_sub_id_compose_left : forall {Γ σ Δ},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Γ ⊨s σ ∘ Id ≈ σ : Δ }}.
Proof with mautosolve.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_sub.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ)...
Qed.

#[export]
Hint Resolve rel_sub_id_compose_left : mctt.

Lemma rel_sub_compose_assoc : forall {Γ σ Γ' σ' Γ'' σ'' Γ'''},
    {{ Γ' ⊨s σ : Γ }} ->
    {{ Γ'' ⊨s σ' : Γ' }} ->
    {{ Γ''' ⊨s σ'' : Γ'' }} ->
    {{ Γ''' ⊨s (σ ∘ σ') ∘ σ'' ≈ σ ∘ (σ' ∘ σ'') : Γ }}.
Proof with mautosolve.
  intros * Hσ [env_relΓ'' [? [env_relΓ' []]]] Hσ''.
  invert_rel_sub Hσ.
  invert_rel_sub Hσ''.
  match goal with
  | _: per_ctx_env ?rel Γ Γ,
      _: per_ctx_env ?rel''' Γ''' Γ''' |- _ =>
      rename rel''' into env_relΓ''';
      rename rel into env_relΓ
  end.
  eexists_rel_sub.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ''').
  (on_all_hyp: destruct_rel_by_assumption env_relΓ'').
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  econstructor...
Qed.

#[export]
Hint Resolve rel_sub_compose_assoc : mctt.

Lemma rel_sub_extend_compose : forall {Γ τ Γ' M σ Γ'' A i},
    {{ Γ' ⊨s σ : Γ'' }} ->
    {{ Γ'' ⊨ A : Type@i }} ->
    {{ Γ' ⊨ M : A[σ] }} ->
    {{ Γ ⊨s τ : Γ' }} ->
    {{ Γ ⊨s (σ ,, M) ∘ τ ≈ (σ ∘ τ) ,, M[τ] : Γ'', A }}.
Proof with mautosolve.
  intros * [env_relΓ' [? [env_relΓ'' []]]] HA HM Hτ.
  invert_rel_exp HM.
  invert_rel_sub Hτ.
  assert {{ ⊨ Γ'', A }} as [] by (eapply rel_ctx_extend; eauto; eexists; eassumption).
  eexists_rel_sub.
  invert_per_ctx_envs.
  handle_per_ctx_env_irrel.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  (on_all_hyp: destruct_rel_by_assumption env_relΓ'').
  destruct_by_head rel_typ.
  invert_rel_typ_body_nouip.
  destruct_by_head rel_exp.
  econstructor...
Qed.

#[export]
Hint Resolve rel_sub_extend_compose : mctt.

Lemma rel_sub_p_extend : forall {Γ' M σ Γ A},
    {{ Γ' ⊨s σ : Γ }} ->
    {{ Γ' ⊨ M : A[σ] }} ->
    {{ Γ' ⊨s Wk ∘ (σ ,, M) ≈ σ : Γ }}.
Proof with mautosolve.
  intros * [env_relΓ' [? [env_relΓ []]]] HM.
  invert_rel_exp HM.
  eexists_rel_sub.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  destruct_by_head rel_typ.
  invert_rel_typ_body_nouip.
  destruct_by_head rel_exp.
  econstructor...
Qed.

#[export]
Hint Resolve rel_sub_p_extend : mctt.

Lemma rel_sub_extend : forall {Γ' σ Γ A},
    {{ Γ' ⊨s σ : Γ, A }} ->
    {{ Γ' ⊨s σ ≈ (Wk ∘ σ) ,, #0[σ] : Γ, A }}.
Proof with mautosolve.
  intros * [env_relΓ' [? [env_relΓA []]]].
  invert_per_ctx_envs_of env_relΓA.
  rename tail_rel into env_relΓ.
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  inversion_clear_by_head cons_per_ctx_env.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  econstructor...
Qed.

#[export]
Hint Resolve rel_sub_extend : mctt.

Lemma rel_sub_sym : forall {Γ σ σ' Δ},
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ Γ ⊨s σ' ≈ σ : Δ }}.
Proof with mautosolve.
  intros * [env_relΓ [? [env_relΔ []]]].
  eexists_rel_sub.
  intros.
  assert (env_relΓ ρ' ρ) by (symmetry; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  econstructor; mauto; symmetry...
Qed.

#[export]
Hint Resolve rel_sub_sym : mctt.

Lemma rel_sub_trans : forall {Γ σ σ' σ'' Δ},
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ Γ ⊨s σ' ≈ σ'' : Δ }} ->
    {{ Γ ⊨s σ ≈ σ'' : Δ }}.
Proof with mautosolve.
  intros * [env_relΓ [? [env_relΔ []]]] Hσ'.
  invert_rel_sub Hσ'.
  eexists_rel_sub.
  intros.
  assert (env_relΓ ρ' ρ') by (etransitivity; [symmetry |]; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  functional_eval_rewrite_clear.
  econstructor; mauto; etransitivity...
Qed.

#[export]
Hint Resolve rel_sub_trans : mctt.

#[export]
Instance rel_sub_PER {Γ A} : PER (rel_sub_under_ctx Γ A).
Proof.
  split; mauto.
Qed.

Lemma rel_sub_conv : forall {Γ σ σ' Δ Δ'},
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ ⊨ Δ ≈ Δ' }} ->
    {{ Γ ⊨s σ ≈ σ' : Δ' }}.
Proof with mautosolve.
  intros * Hσ [env_relΔ].
  invert_rel_sub Hσ.
  assert {{ EF Δ' ≈ Δ' ∈ per_ctx_env ↘ env_relΔ }} by (etransitivity; [symmetry |]; eassumption).
  eexists_rel_sub...
Qed.

#[export]
Hint Resolve rel_sub_conv : mctt.

Lemma presup_rel_sub : forall {Γ σ σ' Δ},
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ ⊨ Γ }} /\ {{ Γ ⊨s σ : Δ }} /\ {{ Γ ⊨s σ' : Δ }} /\ {{ ⊨ Δ }}.
Proof with mautosolve.
  intros * [].
  destruct_conjs.
  repeat split; try solve [eexists; eauto];
    unfold valid_sub_under_ctx;
    etransitivity; only 2,3: symmetry;
    econstructor...
Qed.

Lemma rel_sub_eq_subtyp : forall Γ σ σ' Δ Δ',
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ SubE Δ <: Δ' }} ->
    {{ Γ ⊨s σ ≈ σ' : Δ' }}.
Proof.
  intros * [env_relΓ] HSub.
  pose proof (per_ctx_subtyp_to_env _ _ HSub).
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  econstructor; eauto.
  eapply per_ctx_env_subtyping; eauto.
Qed.

#[export]
Hint Resolve rel_sub_eq_subtyp : mctt.
