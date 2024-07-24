From Coq Require Import Morphisms_Relations.
From Mcltt Require Import Base LibTactics.
From Mcltt.Core Require Import Completeness.LogicalRelation SystemOpt.
Import Domain_Notations.

Lemma valid_lookup : forall {Γ x A env_rel}
                        (equiv_Γ_Γ : {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }}),
    {{ #x : A ∈ Γ }} ->
    exists i,
    forall p p' (equiv_p_p' : {{ Dom p ≈ p' ∈ env_rel }}),
    exists elem_rel,
      rel_typ i A p A p' elem_rel /\ rel_exp {{{ #x }}} p {{{ #x }}} p' elem_rel.
Proof with solve [split; mauto].
  intros * ? HxinΓ.
  assert {{ #x : A ∈ Γ }} as HxinΓ' by mauto.
  remember Γ as Δ eqn:HΔΓ in HxinΓ', equiv_Γ_Γ at 2. clear HΔΓ. rename equiv_Γ_Γ into equiv_Γ_Δ.
  remember A as A' eqn:HAA' in HxinΓ' |- * at 2. clear HAA'.
  gen Δ A' env_rel.
  induction HxinΓ; intros * equiv_Γ_Δ HxinΓ0; inversion HxinΓ0; subst; clear HxinΓ0; inversion_clear equiv_Γ_Δ; subst;
    [| specialize (IHHxinΓ _ _ _ equiv_Γ_Γ' H0) as [j ?]; destruct_conjs];
    apply_relation_equivalence;
    eexists; intros ? ? [];
    (on_all_hyp: destruct_rel_by_assumption tail_rel); destruct_conjs;
    eexists.
  - idtac...
  - destruct_by_head rel_typ.
    destruct_by_head rel_exp.
    dir_inversion_by_head eval_exp; subst...
Qed.

Lemma valid_exp_var : forall {Γ x A},
    {{ ⊨ Γ }} ->
    {{ #x : A ∈ Γ }} ->
    {{ Γ ⊨ #x : A }}.
Proof.
  intros * [? equiv_Γ_Γ] ?.
  unshelve epose proof (valid_lookup equiv_Γ_Γ _) as []; shelve_unifiable; [eassumption |].
  eexists_rel_exp; eassumption.
Qed.

#[export]
Hint Resolve valid_exp_var : mcltt.

Lemma rel_exp_var_0_sub : forall {Γ M σ Δ A},
  {{ Γ ⊨s σ : Δ }} ->
  {{ Γ ⊨ M : A[σ] }} ->
  {{ Γ ⊨ #0[σ ,, M] ≈ M : A[σ] }}.
Proof with mautosolve.
  intros * [env_relΓ [? [env_relΔ]]] [].
  destruct_conjs.
  pose env_relΓ.
  handle_per_ctx_env_irrel.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  dir_inversion_by_head eval_exp; subst.
  functional_eval_rewrite_clear.
  eexists.
  split...
Qed.

#[export]
Hint Resolve rel_exp_var_0_sub : mcltt.

Lemma rel_exp_var_S_sub : forall {Γ M σ Δ A x B},
  {{ Γ ⊨s σ : Δ }} ->
  {{ Γ ⊨ M : A[σ] }} ->
  {{ #x : B ∈ Δ }} ->
  {{ Γ ⊨ #(S x)[σ ,, M] ≈ #x[σ] : B[σ] }}.
Proof with mautosolve.
  intros * [env_relΓ [? [env_relΔ]]] [] HxinΓ.
  destruct_conjs.
  pose env_relΓ.
  handle_per_ctx_env_irrel.
  unshelve epose proof (valid_lookup _ HxinΓ); shelve_unifiable; [eassumption |].
  destruct_conjs.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  dir_inversion_by_head eval_exp; subst.
  functional_eval_rewrite_clear.
  eexists.
  split...
Qed.

#[export]
Hint Resolve rel_exp_var_S_sub : mcltt.

Lemma rel_exp_var_weaken : forall {Γ B x A},
    {{ ⊨ Γ , B }} ->
    {{ #x : A ∈ Γ }} ->
    {{ Γ , B ⊨ #x[Wk] ≈ #(S x) : A[Wk] }}.
Proof with mautosolve.
  intros * [env_relΓB] HxinΓ.
  inversion_by_head (per_ctx_env env_relΓB); subst.
  unshelve epose proof (valid_lookup _ HxinΓ); shelve_unifiable; [eassumption |].
  destruct_conjs.
  eexists_rel_exp.
  apply_relation_equivalence.
  intros.
  destruct_conjs.
  rename tail_rel into env_relΓ.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  dir_inversion_by_head eval_exp; subst.
  eexists.
  split...
Qed.

#[export]
Hint Resolve rel_exp_var_weaken : mcltt.
