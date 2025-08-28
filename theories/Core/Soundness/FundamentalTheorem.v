From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Soundness Require Import
  ContextCases
  FunctionCases
  PairCases
  NatCases
  SubstitutionCases
  SubtypingCases
  TermStructureCases
  UniverseCases
  EqualityCases.
From Mctt.Core.Soundness Require Export LogicalRelation.
Import Domain_Notations.

Section soundness_fundamental.
  Theorem soundness_fundamental :
    (forall Γ, {{ ⊢ Γ }} -> {{ ⊩ Γ }}) /\
      (forall Γ A M, {{ Γ ⊢ M : A }} -> {{ Γ ⊩ M : A }}) /\
      (forall Γ Δ σ, {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊩s σ : Δ }}).
  Proof.
    apply syntactic_wf_mut_ind'; mauto 3.
  Qed.

  #[local]
  Ltac solve_it := pose proof soundness_fundamental; firstorder.

  Theorem soundness_fundamental_ctx : forall Γ, {{ ⊢ Γ }} -> {{ ⊩ Γ }}.
  Proof. solve_it. Qed.

  Theorem soundness_fundamental_exp : forall Γ M A, {{ Γ ⊢ M : A }} -> {{ Γ ⊩ M : A }}.
  Proof. solve_it. Qed.

  Theorem soundness_fundamental_sub : forall Γ σ Δ, {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊩s σ : Δ }}.
  Proof. solve_it. Qed.
End soundness_fundamental.
