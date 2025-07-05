From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Soundness Require Import LogicalRelation.
Import Domain_Notations.

Lemma glu_rel_exp_subtyp : forall {Γ M A A' i},
    {{ Γ ⊩ M : A }} ->
    {{ Γ ⊩ A' : Type@i }} ->
    {{ Γ ⊢ A ⊆ A' }} ->
    {{ Γ ⊩ M : A' }}.
Proof.
  intros * [] HA' [env_relΓ [? [k]]]%completeness_fundamental_subtyp.
  destruct_conjs.
  invert_glu_rel_exp HA'.
  econstructor; split; [eassumption |].
  exists (max i k); intros.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  handle_functional_glu_univ_elem.
  assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (eapply glu_ctx_env_per_env; mauto).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  handle_per_univ_elem_irrel.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  eapply mk_glu_rel_exp_with_sub''; intuition mauto using per_univ_elem_cumu_max_left, per_univ_elem_cumu_max_right.
  eapply glu_univ_elem_per_subtyp_trm_conv; mauto.
  assert (i <= max i k) by lia.
  eapply glu_univ_elem_typ_cumu_ge; revgoals; mauto.
Qed.

#[export]
Hint Resolve glu_rel_exp_subtyp : mctt.

Lemma glu_rel_sub_subtyp : forall {Γ σ Δ Δ'},
    {{ Γ ⊩s σ : Δ }} ->
    {{ ⊩ Δ' }} ->
    {{ ⊢ Δ ⊆ Δ' }} ->
    {{ Γ ⊩s σ : Δ' }}.
Proof.
  intros * [] [] Hsubtyp.
  destruct_conjs.
  econstructor; eexists; repeat split; [eassumption | eassumption |].
  intros.
  destruct_glu_rel_sub_with_sub.
  econstructor; mauto.
  eapply glu_ctx_env_subtyp_sub_if; mauto.
Qed.

#[export]
Hint Resolve glu_rel_sub_subtyp : mctt.


#[local]
Lemma glu_rel_exp_conv' : forall {Γ M A A' i},
    {{ Γ ⊩ M : A }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }} -> (** proof trick, will discharge. see the next lemma. *)
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊩ M : A' }}.
Proof.
  intros * [? [? [k ?]]] [env_relΓ [? [? ?]]]%completeness_fundamental_exp_eq ?.
  econstructor; split; [eassumption |].
  exists (max i k); intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 4.

  destruct_glu_rel_exp_with_sub.
  assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (eapply glu_ctx_env_per_env; mauto).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  simplify_evals.
  destruct_by_head rel_exp.
  saturate_refl.
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem_nouip H).
  apply_equiv_left.
  destruct_all.
  handle_per_univ_elem_irrel.
  assert (i <= max i k) by lia.
  assert (k <= max i k) by lia.
  assert {{ Δ ⊢ A'[σ] ≈ A[σ] : Type@(max i k) }} by mauto 4.
  eapply mk_glu_rel_exp_with_sub''; intuition mauto using per_univ_elem_cumu_max_left, per_univ_elem_cumu_max_right.
  bulky_rewrite.
  eapply glu_univ_elem_exp_cumu_ge; try eassumption.
  eapply glu_univ_elem_resp_per_univ; eauto.
  symmetry. mauto.
Qed.

Lemma glu_rel_exp_conv : forall {Γ M A A' i},
    {{ Γ ⊩ M : A }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊩ M : A' }}.
Proof.
  eauto using glu_rel_exp_conv'.
Qed.

#[export]
Hint Resolve glu_rel_exp_conv : mctt.

Add Parametric Morphism i Γ M : (glu_rel_exp Γ M)
    with signature (wf_exp_eq Γ {{{Type@i}}}) ==> iff as foo.
Proof.
  split; mauto 3.
Qed.


Lemma glu_rel_sub_conv : forall {Γ σ Δ Δ'},
    {{ Γ ⊩s σ : Δ }} ->
    {{ ⊩ Δ' }} ->
    {{ ⊢ Δ ≈ Δ' }} ->
    {{ Γ ⊩s σ : Δ' }}.
Proof.
  mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_sub_conv : mctt.
