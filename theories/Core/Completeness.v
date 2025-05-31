From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Export FundamentalTheorem.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic Require Export NbE.
From Mctt.Core.Syntactic Require Export SystemOpt.
Import Domain_Notations.

Theorem completeness : forall {Γ M M' A},
  {{ Γ ⊢ M ≈ M' : A }} ->
  exists W, nbe Γ M A W /\ nbe Γ M' A W.
Proof with mautosolve.
  intros * [env_relΓ]%completeness_fundamental_exp_eq.
  destruct_conjs.
  assert (exists p p', initial_env Γ p /\ initial_env Γ p' /\ {{ Dom p ≈ p' ∈ env_relΓ }}) as [p] by (eauto using per_ctx_then_per_env_initial_env).
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  functional_eval_rewrite_clear.
  destruct_by_head rel_exp.
  unshelve epose proof (per_elem_then_per_top _ _ (length Γ)) as [? []]; shelve_unifiable...
Qed.

Lemma completeness_ty : forall {Γ i A A'},
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    exists W, nbe_ty Γ A W /\ nbe_ty Γ A' W.
Proof.
  intros * [? [?%nbe_type_to_nbe_ty ?%nbe_type_to_nbe_ty]]%completeness.
  mauto 3.
Qed.
