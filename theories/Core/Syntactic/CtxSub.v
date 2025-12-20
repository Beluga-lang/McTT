From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export System.
Import Syntax_Notations.

Lemma ctx_sub_refl : forall {Δ Γ},
    {{ Δ ⊢ Γ }} ->
    {{ Δ ⊢ Γ ⊆ Γ }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve ctx_sub_refl : mctt.

Module ctxsub_judg.
  #[local]
  Ltac gen_ctxsub_helper_IH ctxsub_exp_helper ctxsub_exp_eq_helper ctxsub_sub_helper ctxsub_sub_eq_helper ctxsub_subtyp_helper H :=
  match type of H with
  | {{ ^?Δ ;; ^?Γ ⊢ ^?M : ^?A }} => pose proof ctxsub_exp_helper _ _ _ _ H
  | {{ ^?Δ ;; ^?Γ ⊢ ^?M ≈ ^?N : ^?A }} => pose proof ctxsub_exp_eq_helper _ _ _ _ _ H
  | {{ ^?Δ ;; ^?Γ ⊢s ^?σ : ^?Γ' }} => pose proof ctxsub_sub_helper _ _ _ _ H
  | {{ ^?Δ ;; ^?Γ ⊢s ^?σ ≈ ^?τ : ^?Γ' }} => pose proof ctxsub_sub_eq_helper _ _ _ _ _ H
  | {{ ^?Δ ;; ^?Γ ⊢ ^?M ⊆ ^?M' }} => pose proof ctxsub_subtyp_helper _ _ _ _ H
  end.

  #[local]
  Lemma ctxsub_exp_helper : forall {Δ Γ M A}, {{ Δ ;; Γ ⊢ M : A }} -> forall {Γ1}, {{ Δ ⊢ Γ1 ⊆ Γ }} -> {{ Δ ;; Γ1 ⊢ M : A }}
  with
  ctxsub_exp_eq_helper : forall {Δ Γ M M' A}, {{ Δ ;; Γ ⊢ M ≈ M' : A }} -> forall {Γ1}, {{ Δ ⊢ Γ1 ⊆ Γ }} -> {{ Δ ;; Γ1 ⊢ M ≈ M' : A }}
  with
  ctxsub_sub_helper : forall {Δ Γ Γ' σ}, {{ Δ ;; Γ ⊢s σ : Γ' }} -> forall {Γ1}, {{ Δ ⊢ Γ1 ⊆ Γ }} -> {{ Δ ;; Γ1 ⊢s σ : Γ' }}
  with
  ctxsub_sub_eq_helper : forall {Δ Γ Γ' σ σ'}, {{ Δ ;; Γ ⊢s σ ≈ σ' : Γ' }} -> forall {Γ1}, {{ Δ ⊢ Γ1 ⊆ Γ }} -> {{ Δ ;; Γ1 ⊢s σ ≈ σ' : Γ' }}
  with
  ctxsub_subtyp_helper : forall {Δ Γ M M'}, {{ Δ ;; Γ ⊢ M ⊆ M' }} -> forall {Γ1}, {{ Δ ⊢ Γ1 ⊆ Γ }} -> {{ Δ ;; Γ1 ⊢ M ⊆ M' }}.
  Proof with mautosolve.
    all: inversion_clear 1;
      (on_all_hyp: gen_ctxsub_helper_IH ctxsub_exp_helper ctxsub_exp_eq_helper ctxsub_sub_helper ctxsub_sub_eq_helper ctxsub_subtyp_helper);
      clear ctxsub_exp_helper ctxsub_exp_eq_helper ctxsub_sub_helper ctxsub_sub_eq_helper ctxsub_subtyp_helper;
      intros * HΓ1Γ; destruct (presup_ctx_sub HΓ1Γ); mauto 4;
      try (rename B into C); try (rename B' into C'); try (rename A0 into B); try (rename A' into B').
    (** ctxsub_exp_helper & ctxsub_exp_eq_helper recursion cases *)
    1,12-15: assert {{ Δ ⊢ Γ1, ℕ ⊆ Γ, ℕ }} by (econstructor; mautosolve);
    assert {{ Δ ;; Γ1, ℕ ⊢ B : Type@i }} by eauto; econstructor...
    (** ctxsub_exp_helper & ctxsub_exp_eq_helper function cases *)
    1-3,11-17: assert {{ Δ ;; Γ1 ⊢ B : Type@i }} by eauto; assert {{ Δ ⊢ Γ1, B ⊆ Γ, B }} by mauto;
    try econstructor...
    (** equality type case *)
    6,15:idtac...

    (** ctxsub_exp_helper & ctxsub_exp_eq_helper variable cases *)
    5,16: assert (exists B, {{ #x : B ∈ Γ1 }} /\ {{ Δ ;; Γ1 ⊢ B ⊆ A }}); destruct_conjs; mautosolve 4.
    (** ctxsub_sub_helper & ctxsub_sub_eq_helper weakening cases *)
    16,17: inversion_clear HΓ1Γ; econstructor; mautosolve 4.

    (** eqrec related cases *)
    5,13-14: assert {{ Δ ⊢ Γ1, B ⊆ Γ, B }} by mauto;
      assert {{ Δ ;; Γ, B ⊢s Wk : Γ }} by mauto 3;
      assert {{ Δ ;; Γ, B ⊢ B[Wk] : Type@i }} by mauto 3;
      assert {{ Δ ;; Γ, B, B[Wk] ⊢s Wk : Γ, B }} by mauto 4;
      assert {{ Δ ;; Γ, B, B[Wk] ⊢s Wk∘Wk : Γ }} by mauto 3;
      assert {{ Δ ;; Γ1, B ⊢s Wk : Γ1 }} by mauto 3;
      assert {{ Δ ;; Γ1, B ⊢ B[Wk] : Type@i }} by mauto 3;
      assert {{ Δ ;; Γ1 , B, B[Wk] ⊢s Wk : Γ1, B }} by mauto 4;
      assert {{ Δ ;; Γ1 , B, B[Wk] ⊢s Wk∘Wk : Γ1 }} by mauto 3;
      assert {{ Δ ;; Γ1, B, B[Wk] ⊢ B[Wk∘Wk] : Type@i }} by mauto 3;
      assert {{ Δ ;; Γ1, B, B[Wk] ⊢ B[Wk∘Wk] : Type@i }} by mauto 3;
      assert {{ Δ ⊢ Γ1, B, B[Wk] ⊆ Γ, B, B[Wk] }} by (econstructor; mauto 4);
      assert {{ Δ ;; Γ, B, B[Wk] ⊢ Eq B[Wk∘Wk] #1 #0 : Type@i }} by (econstructor; mauto 3; eapply wf_conv; mauto 4);
      assert {{ Δ ;; Γ1, B, B[Wk] ⊢ Eq B[Wk∘Wk] #1 #0 : Type@i }} by (econstructor; mauto 3; eapply wf_conv; mauto 4);
      assert {{ Δ ⊢ Γ1, B, B[Wk], Eq B[Wk∘Wk] #1 #0 ⊆ Γ, B, B[Wk], Eq B[Wk∘Wk] #1 #0 }} by mauto 3;
      econstructor; mauto 2.

    (* sigma type case *)
    1-11:
      match goal with
      | _ : context [ {{{ ^?Γ , ^?A }}} ] , _ : {{ ^?Δ ⊢ ^?Γ1 ⊆ ^?Γ }} |- _ =>
        assert {{ Δ ⊢ Γ1, A ⊆ Γ, A }} by (econstructor; mautosolve 3)
      end; econstructor; mauto 3.

    - (** ctxsub_exp_eq_helper variable case *)
      inversion_clear HΓ1Γ as [|? Γ2 ? ? C'].
      assert (exists D, {{ #x : D ∈ Γ2 }} /\ {{ Δ ;; Γ2 ⊢ D ⊆ B }}) as [D [i0 ?]] by mauto.
      destruct_conjs.
      assert {{ Δ ⊢ Γ2, C' }} by mauto.
      assert {{ Δ ;; Γ2, C' ⊢ D[Wk] ⊆ B[Wk] }}...
    - eapply wf_subtyp_pi with (i := i); firstorder mauto 4.
    - eapply wf_subtyp_sigma with (i := i); firstorder mauto 4.
  Qed.

  Corollary ctxsub_exp : forall {Δ Γ Γ1 M A}, {{ Δ ⊢ Γ1 ⊆ Γ }} -> {{ Δ ;; Γ ⊢ M : A }} -> {{ Δ ;; Γ1 ⊢ M : A }}.
  Proof.
    eauto using ctxsub_exp_helper.
  Qed.

  Corollary ctxsub_exp_eq : forall {Δ Γ Γ1 M M' A}, {{ Δ ⊢ Γ1 ⊆ Γ }} -> {{ Δ ;; Γ ⊢ M ≈ M' : A }} -> {{ Δ ;; Γ1 ⊢ M ≈ M' : A }}.
  Proof.
    eauto using ctxsub_exp_eq_helper.
  Qed.

  Corollary ctxsub_sub : forall {Δ Γ Γ1 σ Γ'}, {{ Δ ⊢ Γ1 ⊆ Γ }} -> {{ Δ ;; Γ ⊢s σ : Γ' }} -> {{ Δ ;; Γ1 ⊢s σ : Γ' }}.
  Proof.
    eauto using ctxsub_sub_helper.
  Qed.

  Corollary ctxsub_sub_eq : forall {Δ Γ Γ1 σ σ' Γ'}, {{ Δ ⊢ Γ1 ⊆ Γ }} -> {{ Δ ;; Γ ⊢s σ ≈ σ' : Γ' }} -> {{ Δ ;; Γ1 ⊢s σ ≈ σ' : Γ' }}.
  Proof.
    eauto using ctxsub_sub_eq_helper.
  Qed.

  Corollary ctxsub_subtyp : forall {Δ Γ Γ1 A B}, {{ Δ ⊢ Γ1 ⊆ Γ }} -> {{ Δ ;; Γ ⊢ A ⊆ B }} -> {{ Δ ;; Γ1 ⊢ A ⊆ B }}.
  Proof.
    eauto using ctxsub_subtyp_helper.
  Qed.

  #[export]
  Hint Resolve ctxsub_exp ctxsub_exp_eq ctxsub_sub ctxsub_sub_eq ctxsub_subtyp : mctt.
End ctxsub_judg.

Export ctxsub_judg.

Lemma wf_ctx_sub_trans : forall Δ Γ0 Γ1,
    {{ Δ ⊢ Γ0 ⊆ Γ1 }} ->
    forall  Γ2,
    {{ Δ ⊢ Γ1 ⊆ Γ2 }} ->
    {{ Δ ⊢ Γ0 ⊆ Γ2 }}.
Proof.
  induction 1; intros; progressive_inversion; [constructor; auto|].
  eapply wf_ctx_sub_extend with (i := max i i0);
    mauto 3 using lift_exp_max_left, lift_exp_max_right.
Qed.

#[export]
 Hint Resolve wf_ctx_sub_trans : mctt.

#[export]
Instance wf_ctx_sub_trans_ins Δ : Transitive (wf_ctx_sub Δ).
Proof. eauto using wf_ctx_sub_trans. Qed.

Add Parametric Morphism Δ : (wf_exp Δ)
  with signature (wf_ctx_sub Δ) --> eq ==> eq ==> Basics.impl as ctxsub_exp_morphism.
Proof.
  cbv. intros. mauto 3.
Qed.

Add Parametric Morphism Δ : (wf_exp_eq Δ)
  with signature (wf_ctx_sub Δ) --> eq ==> eq ==> eq ==> Basics.impl as ctxsub_exp_eq_morphism.
Proof.
  cbv. intros. mauto 3.
Qed.

Add Parametric Morphism Δ : (wf_sub Δ)
  with signature (wf_ctx_sub Δ) --> eq ==> eq ==> Basics.impl as ctxsub_sub_morphism.
Proof.
  cbv. intros. mauto 3.
Qed.

Add Parametric Morphism Δ : (wf_sub_eq Δ)
  with signature (wf_ctx_sub Δ) --> eq ==> eq ==> eq ==> Basics.impl as ctxsub_sub_eq_morphism.
Proof.
  cbv. intros. mauto 3.
Qed.

Add Parametric Morphism Δ : (wf_subtyp Δ)
  with signature (wf_ctx_sub Δ) --> eq ==> eq ==> Basics.impl as ctxsub_subtyp_morphism.
Proof.
  cbv. intros. mauto 3.
Qed.
