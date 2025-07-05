From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export System.
Import Syntax_Notations.

Lemma ctx_sub_refl : forall {Γ},
    {{ ⊢ Γ }} ->
    {{ ⊢ Γ ⊆ Γ }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve ctx_sub_refl : mctt.

Module ctxsub_judg.
  #[local]
  Ltac gen_ctxsub_helper_IH ctxsub_exp_helper ctxsub_exp_eq_helper ctxsub_sub_helper ctxsub_sub_eq_helper ctxsub_subtyp_helper H :=
  match type of H with
  | {{ ^?Γ ⊢ ^?M : ^?A }} => pose proof ctxsub_exp_helper _ _ _ H
  | {{ ^?Γ ⊢ ^?M ≈ ^?N : ^?A }} => pose proof ctxsub_exp_eq_helper _ _ _ _ H
  | {{ ^?Γ ⊢s ^?σ : ^?Δ }} => pose proof ctxsub_sub_helper _ _ _ H
  | {{ ^?Γ ⊢s ^?σ ≈ ^?τ : ^?Δ }} => pose proof ctxsub_sub_eq_helper _ _ _ _ H
  | {{ ^?Γ ⊢ ^?M ⊆ ^?M' }} => pose proof ctxsub_subtyp_helper _ _ _ H
  end.

  #[local]
  Lemma ctxsub_exp_helper : forall {Γ M A}, {{ Γ ⊢ M : A }} -> forall {Δ}, {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢ M : A }}
  with
  ctxsub_exp_eq_helper : forall {Γ M M' A}, {{ Γ ⊢ M ≈ M' : A }} -> forall {Δ}, {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢ M ≈ M' : A }}
  with
  ctxsub_sub_helper : forall {Γ Γ' σ}, {{ Γ ⊢s σ : Γ' }} -> forall {Δ}, {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢s σ : Γ' }}
  with
  ctxsub_sub_eq_helper : forall {Γ Γ' σ σ'}, {{ Γ ⊢s σ ≈ σ' : Γ' }} -> forall {Δ}, {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢s σ ≈ σ' : Γ' }}
  with
  ctxsub_subtyp_helper : forall {Γ M M'}, {{ Γ ⊢ M ⊆ M' }} -> forall {Δ}, {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢ M ⊆ M' }}.
  Proof with mautosolve.
    all: inversion_clear 1;
      (on_all_hyp: gen_ctxsub_helper_IH ctxsub_exp_helper ctxsub_exp_eq_helper ctxsub_sub_helper ctxsub_sub_eq_helper ctxsub_subtyp_helper);
      clear ctxsub_exp_helper ctxsub_exp_eq_helper ctxsub_sub_helper ctxsub_sub_eq_helper ctxsub_subtyp_helper;
      intros * HΓΔ; destruct (presup_ctx_sub HΓΔ); mauto 4;
      try (rename B into C); try (rename B' into C'); try (rename A0 into B); try (rename A' into B').
    (** ctxsub_exp_helper & ctxsub_exp_eq_helper recursion cases *)
    1,8-10: assert {{ ⊢ Δ, ℕ ⊆ Γ, ℕ }} by (econstructor; mautosolve);
    assert {{ Δ, ℕ ⊢ B : Type@i }} by eauto; econstructor...
    (** ctxsub_exp_helper & ctxsub_exp_eq_helper function cases *)
    1-3,7-11: assert {{ Δ ⊢ B : Type@i }} by eauto; assert {{ ⊢ Δ, B ⊆ Γ, B }} by mauto;
    try econstructor...
    (** equality type case *)
    2,4:idtac...

    (** ctxsub_exp_helper & ctxsub_exp_eq_helper variable cases *)
    1,5: assert (exists B, {{ #x : B ∈ Δ }} /\ {{ Δ ⊢ B ⊆ A }}); destruct_conjs; mautosolve 4.
    (** ctxsub_sub_helper & ctxsub_sub_eq_helper weakening cases *)
    5,6: inversion_clear HΓΔ; econstructor; mautosolve 4.

    (** eqrec related cases *)
    1-3: assert {{ ⊢ Δ, B ⊆ Γ, B }} by mauto;
      assert {{ Γ, B ⊢s Wk : Γ }} by mauto 3;
      assert {{ Γ, B ⊢ B[Wk] : Type@i }} by mauto 3;
      assert {{ Γ, B, B[Wk] ⊢s Wk : Γ, B }} by mauto 4;
      assert {{ Γ, B, B[Wk] ⊢s Wk∘Wk : Γ }} by mauto 3;
      assert {{ Δ, B ⊢s Wk : Δ }} by mauto 3;
      assert {{ Δ, B ⊢ B[Wk] : Type@i }} by mauto 3;
      assert {{ Δ, B, B[Wk] ⊢s Wk : Δ, B }} by mauto 4;
      assert {{ Δ, B, B[Wk] ⊢s Wk∘Wk : Δ }} by mauto 3;
      assert {{ Δ, B, B[Wk] ⊢ B[Wk∘Wk] : Type@i }} by mauto 3;
      assert {{ Δ, B, B[Wk] ⊢ B[Wk∘Wk] : Type@i }} by mauto 3;
      assert {{ ⊢ Δ, B, B[Wk] ⊆ Γ, B, B[Wk] }} by (econstructor; mauto 4);
      assert {{ Γ, B, B[Wk] ⊢ Eq B[Wk∘Wk] #1 #0 : Type@i }} by (econstructor; mauto 3; eapply wf_conv; mauto 4);
      assert {{ Δ, B, B[Wk] ⊢ Eq B[Wk∘Wk] #1 #0 : Type@i }} by (econstructor; mauto 3; eapply wf_conv; mauto 4);
      assert {{ ⊢ Δ, B, B[Wk], Eq B[Wk∘Wk] #1 #0 ⊆ Γ, B, B[Wk], Eq B[Wk∘Wk] #1 #0 }} by mauto 3;
      econstructor; mauto 2.

    - (** ctxsub_exp_eq_helper variable case *)
      inversion_clear HΓΔ as [|Δ0 ? ? C'].
      assert (exists D, {{ #x : D ∈ Δ0 }} /\ {{ Δ0 ⊢ D ⊆ B }}) as [D [i0 ?]] by mauto.
      destruct_conjs.
      assert {{ ⊢ Δ0, C' }} by mauto.
      assert {{ Δ0, C' ⊢ D[Wk] ⊆ B[Wk] }}...
    - eapply wf_subtyp_pi with (i := i); firstorder mauto 4.
  Qed.

  Corollary ctxsub_exp : forall {Γ Δ M A}, {{ ⊢ Δ ⊆ Γ }} -> {{ Γ ⊢ M : A }} -> {{ Δ ⊢ M : A }}.
  Proof.
    eauto using ctxsub_exp_helper.
  Qed.

  Corollary ctxsub_exp_eq : forall {Γ Δ M M' A}, {{ ⊢ Δ ⊆ Γ }} -> {{ Γ ⊢ M ≈ M' : A }} -> {{ Δ ⊢ M ≈ M' : A }}.
  Proof.
    eauto using ctxsub_exp_eq_helper.
  Qed.

  Corollary ctxsub_sub : forall {Γ Δ σ Γ'}, {{ ⊢ Δ ⊆ Γ }} -> {{ Γ ⊢s σ : Γ' }} -> {{ Δ ⊢s σ : Γ' }}.
  Proof.
    eauto using ctxsub_sub_helper.
  Qed.

  Corollary ctxsub_sub_eq : forall {Γ Δ σ σ' Γ'}, {{ ⊢ Δ ⊆ Γ }} -> {{ Γ ⊢s σ ≈ σ' : Γ' }} -> {{ Δ ⊢s σ ≈ σ' : Γ' }}.
  Proof.
    eauto using ctxsub_sub_eq_helper.
  Qed.

  Corollary ctxsub_subtyp : forall {Γ Δ A B}, {{ ⊢ Δ ⊆ Γ }} -> {{ Γ ⊢ A ⊆ B }} -> {{ Δ ⊢ A ⊆ B }}.
  Proof.
    eauto using ctxsub_subtyp_helper.
  Qed.

  #[export]
  Hint Resolve ctxsub_exp ctxsub_exp_eq ctxsub_sub ctxsub_sub_eq ctxsub_subtyp : mctt.
End ctxsub_judg.

Export ctxsub_judg.

Lemma wf_ctx_sub_trans : forall Γ0 Γ1,
    {{ ⊢ Γ0 ⊆ Γ1 }} ->
    forall  Γ2,
    {{ ⊢ Γ1 ⊆ Γ2 }} ->
    {{ ⊢ Γ0 ⊆ Γ2 }}.
Proof.
  induction 1; intros; progressive_inversion; [constructor |].
  eapply wf_ctx_sub_extend with (i := max i i0);
    mauto 3 using lift_exp_max_left, lift_exp_max_right.
Qed.

#[export]
 Hint Resolve wf_ctx_sub_trans : mctt.

#[export]
Instance wf_ctx_sub_trans_ins : Transitive wf_ctx_sub.
Proof. eauto using wf_ctx_sub_trans. Qed.

Add Parametric Morphism : wf_exp
  with signature wf_ctx_sub --> eq ==> eq ==> Basics.impl as ctxsub_exp_morphism.
Proof.
  cbv. intros. mauto 3.
Qed.

Add Parametric Morphism : wf_exp_eq
  with signature wf_ctx_sub --> eq ==> eq ==> eq ==> Basics.impl as ctxsub_exp_eq_morphism.
Proof.
  cbv. intros. mauto 3.
Qed.

Add Parametric Morphism : wf_sub
  with signature wf_ctx_sub --> eq ==> eq ==> Basics.impl as ctxsub_sub_morphism.
Proof.
  cbv. intros. mauto 3.
Qed.

Add Parametric Morphism : wf_sub_eq
  with signature wf_ctx_sub --> eq ==> eq ==> eq ==> Basics.impl as ctxsub_sub_eq_morphism.
Proof.
  cbv. intros. mauto 3.
Qed.

Add Parametric Morphism : wf_subtyp
  with signature wf_ctx_sub --> eq ==> eq ==> Basics.impl as ctxsub_subtyp_morphism.
Proof.
  cbv. intros. mauto 3.
Qed.
