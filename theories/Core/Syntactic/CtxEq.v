From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export CtxSub.
Import Syntax_Notations.

Lemma ctx_eq_refl : forall {Δ Γ}, {{ Δ ⊢ Γ }} -> {{ Δ ⊢ Γ ≈ Γ }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve ctx_eq_refl : mctt.

Lemma ctx_eq_sym : forall {Δ Γ Γ'}, {{ Δ ⊢ Γ ≈ Γ' }} -> {{ Δ ⊢ Γ' ≈ Γ }}.
Proof.
  intros.
  symmetry.
  eassumption.
Qed.

#[export]
Hint Resolve ctx_eq_sym : mctt.

Lemma ctxeq_exp : forall {Δ Γ Γ1 M A}, {{ Δ ⊢ Γ ≈ Γ1 }} -> {{ Δ ;; Γ ⊢ M : A }} -> {{ Δ ;; Γ1 ⊢ M : A }}.
Proof. mauto. Qed.

Lemma ctxeq_exp_eq : forall {Δ Γ Γ1 M M' A}, {{ Δ ⊢ Γ ≈ Γ1 }} -> {{ Δ ;; Γ ⊢ M ≈ M' : A }} -> {{ Δ ;; Γ1 ⊢ M ≈ M' : A }}.
Proof. mauto. Qed.

Lemma ctxeq_sub : forall {Δ Γ Γ1 σ Γ'}, {{ Δ ⊢ Γ ≈ Γ1 }} -> {{ Δ ;; Γ ⊢s σ : Γ' }} -> {{ Δ ;; Γ1 ⊢s σ : Γ' }}.
Proof. mauto. Qed.

Lemma ctxeq_sub_eq : forall {Δ Γ Γ1 σ σ' Γ'}, {{ Δ ⊢ Γ ≈ Γ1 }} -> {{ Δ ;; Γ ⊢s σ ≈ σ' : Γ' }} -> {{ Δ ;; Γ1 ⊢s σ ≈ σ' : Γ' }}.
Proof. mauto. Qed.

Lemma ctxeq_subtyp : forall {Δ Γ Γ1 A B}, {{ Δ ⊢ Γ ≈ Γ1 }} -> {{ Δ ;; Γ ⊢ A ⊆ B }} -> {{ Δ ;; Γ1 ⊢ A ⊆ B }}.
Proof. mauto. Qed.

#[export]
Hint Resolve ctxeq_exp ctxeq_exp_eq ctxeq_sub ctxeq_sub_eq ctxeq_subtyp : mctt.


Lemma ctx_eq_trans : forall {Δ Γ0 Γ1 Γ2}, {{ Δ ⊢ Γ0 ≈ Γ1 }} -> {{ Δ ⊢ Γ1 ≈ Γ2 }} -> {{ Δ ⊢ Γ0 ≈ Γ2 }}.
Proof with mautosolve.
  intros * HΓ01.
  gen Γ2.
  induction HΓ01 as [|? Γ0 ? i01 A0 A1]; mauto.
  inversion_clear 1 as [|? ? Γ2' i12 ? A2].
  clear Γ2; rename Γ2' into Γ2.
  set (i := max i01 i12).
  assert {{ Δ ;; Γ0 ⊢ A0 : Type@i }} by mauto using lift_exp_max_left.
  assert {{ Δ ;; Γ2 ⊢ A2 : Type@i }} by mauto using lift_exp_max_right.
  assert {{ Δ ;; Γ0 ⊢ A0 ≈ A1 : Type@i }} by mauto using lift_exp_eq_max_left.
  assert {{ Δ ;; Γ2 ⊢ A1 ≈ A2 : Type@i }} by mauto using lift_exp_eq_max_right.
  assert {{ Δ ⊢ Γ0 ≈ Γ2 }} by mauto.
  assert {{ Δ ;; Γ0 ⊢ A0 ≈ A2 : Type@i }} by mauto.
  econstructor...
Qed.

#[export]
Hint Resolve ctx_eq_trans : mctt.

#[export]
Instance wf_ctx_PER Δ : PER (wf_ctx_eq Δ).
Proof.
  split.
  - eauto using ctx_eq_sym.
  - eauto using ctx_eq_trans.
Qed.


Add Parametric Morphism Δ : (wf_exp Δ)
  with signature (wf_ctx_eq Δ) ==> eq ==> eq ==> iff as ctxeq_exp_morphism.
Proof.
  intros. split; mauto 3.
Qed.


Add Parametric Morphism Δ : (wf_exp_eq Δ)
  with signature (wf_ctx_eq Δ) ==> eq ==> eq ==> eq ==> iff as ctxeq_exp_eq_morphism.
Proof.
  intros. split; mauto 3.
Qed.


Add Parametric Morphism Δ : (wf_sub Δ)
  with signature (wf_ctx_eq Δ) ==> eq ==> eq ==> iff as ctxeq_sub_morphism.
Proof.
  intros. split; mauto 3.
Qed.


Add Parametric Morphism Δ : (wf_sub_eq Δ)
  with signature (wf_ctx_eq Δ) ==> eq ==> eq ==> eq ==> iff as ctxeq_sub_eq_morphism.
Proof.
  intros. split; mauto 3.
Qed.


Add Parametric Morphism Δ : (wf_subtyp Δ)
  with signature (wf_ctx_eq Δ) ==> eq ==> eq ==> iff as ctxeq_subtyp_morphism.
Proof.
  intros. split; mauto 3.
Qed.
