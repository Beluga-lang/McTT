From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations.

Generalizable All Variables.

Reserved Notation "Γ ⊢w σ : Δ" (in custom judg at level 80, Γ custom exp, σ custom exp, Δ custom exp).

Inductive weakening : ctx -> sub -> ctx -> Prop :=
| wk_id :
  `( {{ Γ ⊢s σ ≈ Id : Δ }} ->
     {{ Γ ⊢w σ : Δ }} )
| wk_p :
  `( {{ Γ ⊢w τ : Δ', A }} ->
     {{ ⊢ Δ' ⊆ Δ }} ->
     {{ Γ ⊢s σ ≈ Wk ∘ τ : Δ }} ->
     {{ Γ ⊢w σ : Δ }} )
where "Γ ⊢w σ : Δ" := (weakening Γ σ Δ) (in custom judg) : type_scope.

#[export]
Hint Constructors weakening : mctt.
