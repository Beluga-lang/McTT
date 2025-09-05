From Coq Require Import Morphisms_Relations RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.WCompleteness Require Import ContextCases LogicalRelation UniverseCases.
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
  inversion_by_head (per_ctx_env env_relΓA); subst.
  eexists_rel_sub.
  intros.
  apply_relation_equivalence.
  destruct_conjs...
Qed.

#[export]
Hint Resolve rel_sub_weaken : mctt.

Lemma rel_sub_compose_cong : forall {Γ τ τ' Γ' σ σ' Γ''},
    {{ Γ ⊨s τ ≈ τ' : Γ' }} ->
    {{ Γ' ⊨s σ ≈ σ' : Γ'' }} ->
    {{ Γ ⊨s σ ∘ τ ≈ σ' ∘ τ' : Γ'' }}.
Proof with mautosolve.
  intros * [env_relΓ [? [env_relΓ']]] [].
  destruct_conjs.
  pose env_relΓ'.
  handle_per_ctx_env_irrel.
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
  intros * [env_relΓ [? [env_relΔ]]] HA [].
  destruct_conjs.
  pose env_relΓ.
  pose env_relΔ.
  assert {{ ⊨ Δ, A }} as [env_relΔA] by (eapply rel_ctx_extend; eauto; eexists; mauto).
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  match_by_head (per_ctx_env env_relΔA) invert_per_ctx_env.
  destruct_conjs.
  handle_per_ctx_env_irrel.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  invert_rel_typ_body_nouip.
  handle_per_univ_elem_irrel.
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
  intros * [env_relΓ'] [env_relΓ'' [? []]] [env_relΓ'''].
  destruct_conjs.
  pose env_relΓ'.
  pose env_relΓ''.
  handle_per_ctx_env_irrel.
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
  intros * [env_relΓ' [? [env_relΓ'']]] HA [] [env_relΓ].
  destruct_conjs.
  pose env_relΓ'.
  pose env_relΓ''.
  handle_per_ctx_env_irrel.
  assert {{ ⊨ Γ'', A }} as [env_relΓ''A] by (eapply rel_ctx_extend; eauto; eexists; eassumption).
  eexists_rel_sub.
  match_by_head (per_ctx_env env_relΓ''A) invert_per_ctx_env.
  handle_per_ctx_env_irrel.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  (on_all_hyp: destruct_rel_by_assumption env_relΓ'').
  destruct_by_head rel_typ.
  invert_rel_typ_body_nouip.
  destruct_by_head rel_exp.
  handle_per_univ_elem_irrel.
  econstructor...
Qed.

#[export]
Hint Resolve rel_sub_extend_compose : mctt.

Lemma rel_sub_p_extend : forall {Γ' M σ Γ A},
    {{ Γ' ⊨s σ : Γ }} ->
    {{ Γ' ⊨ M : A[σ] }} ->
    {{ Γ' ⊨s Wk ∘ (σ ,, M) ≈ σ : Γ }}.
Proof with mautosolve.
  intros * [env_relΓ'] [].
  destruct_conjs.
  pose env_relΓ'.
  handle_per_ctx_env_irrel.
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
  intros * [env_relΓ' [? [env_relΓA]]].
  destruct_conjs.
  pose env_relΓ'.
  inversion_by_head (per_ctx_env env_relΓA); subst.
  rename tail_rel into env_relΓ.
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  econstructor...
Qed.

#[export]
Hint Resolve rel_sub_extend : mctt.

Lemma rel_sub_sym : forall {Γ σ σ' Δ},
    {{ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ Γ ⊨s σ' ≈ σ : Δ }}.
Proof with mautosolve.
  intros * [env_relΓ].
  destruct_conjs.
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
  intros * [env_relΓ] [].
  destruct_conjs.
  pose env_relΓ.
  handle_per_ctx_env_irrel.
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
  intros * [? [? [env_relΔ]]] [].
  destruct_conjs.
  pose env_relΔ.
  handle_per_ctx_env_irrel.
  assert {{ EF Δ' ≈≈ Δ' ∈ per_ctx_env ↘ env_relΔ }} by (etransitivity; [symmetry |]; eassumption).
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
