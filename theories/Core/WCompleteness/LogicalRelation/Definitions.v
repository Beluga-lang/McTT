From Coq Require Import Relations.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export WPER.
Import Domain_Notations.

Inductive rel_exp M ρ M' ρ' (R : relation domain) : Prop :=
| mk_rel_exp : forall m m', {{ ⟦ M ⟧ ρ ↘ m }} -> {{ ⟦ M' ⟧ ρ' ↘ m' }} -> {{ Dom m ≈≈ m' ∈ R }} -> rel_exp M ρ M' ρ' R.
#[global]
Arguments mk_rel_exp {_ _ _ _ _}.
#[export]
Hint Constructors rel_exp : mctt.

Definition rel_exp_under_ctx Γ A M M' :=
  exists env_rel (_ : {{ EF Γ ≈≈ Γ ∈ per_ctx_env ↘ env_rel }}) i,
  forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈≈ ρ' ∈ env_rel }}),
  exists (elem_rel : relation domain),
     rel_typ i A ρ A ρ' elem_rel /\ rel_exp M ρ M' ρ' elem_rel.

Definition valid_exp_under_ctx Γ A M := rel_exp_under_ctx Γ A M M.
#[global]
Arguments valid_exp_under_ctx _ _ _ /.
#[export]
Hint Transparent valid_exp_under_ctx : mctt.
#[export]
Hint Unfold valid_exp_under_ctx : mctt.

Inductive rel_sub σ ρ σ' ρ' (R : relation env) : Prop :=
| mk_rel_sub : forall ρσ ρ'σ', {{ ⟦ σ ⟧s ρ ↘ ρσ }} -> {{ ⟦ σ' ⟧s ρ' ↘ ρ'σ' }} -> {{ Dom ρσ ≈≈ ρ'σ' ∈ R }} -> rel_sub σ ρ σ' ρ' R.
#[global]
Arguments mk_rel_sub {_ _ _ _ _ _}.
#[export]
Hint Constructors rel_sub : mctt.

Definition rel_sub_under_ctx Γ Δ σ σ' :=
  exists env_rel (_ : {{ EF Γ ≈≈ Γ ∈ per_ctx_env ↘ env_rel }})
     env_rel' (_ : {{ EF Δ ≈≈ Δ ∈ per_ctx_env ↘ env_rel' }}),
  forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈≈ ρ' ∈ env_rel }}),
    rel_sub σ ρ σ' ρ' env_rel'.

Definition valid_sub_under_ctx Γ Δ σ := rel_sub_under_ctx Γ Δ σ σ.
#[global]
Arguments valid_sub_under_ctx _ _ _ /.
#[export]
Hint Transparent valid_sub_under_ctx : mctt.
#[export]
Hint Unfold valid_sub_under_ctx : mctt.

Definition subtyp_under_ctx Γ M M' :=
  exists env_rel (_ : {{ EF Γ ≈≈ Γ ∈ per_ctx_env ↘ env_rel }}) i,
  forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈≈ ρ' ∈ env_rel }}),
    exists R R', rel_typ i M ρ M ρ' R /\ rel_typ i M' ρ M' ρ' R' /\ rel_exp M ρ M' ρ' (per_subtyp i).

Notation "⊨ Γ ≈ Γ'" := (per_ctx Γ Γ')  (in custom judg at level 80, Γ custom exp, Γ' custom exp).
Notation "⊨ Γ" := (valid_ctx Γ) (in custom judg at level 80, Γ custom exp).
Notation "Γ ⊨ M ≈ M' : A" := (rel_exp_under_ctx Γ A M M') (in custom judg at level 80, Γ custom exp, M custom exp, M' custom exp, A custom exp).
Notation "Γ ⊨ M ⊆ M'" := (subtyp_under_ctx Γ M M') (in custom judg at level 80, Γ custom exp, M custom exp, M' custom exp).
Notation "Γ ⊨ M : A" := (valid_exp_under_ctx Γ A M) (in custom judg at level 80, Γ custom exp, M custom exp, A custom exp).
Notation "Γ ⊨s σ ≈ σ' : Δ" := (rel_sub_under_ctx Γ Δ σ σ') (in custom judg at level 80, Γ custom exp, σ custom exp, σ' custom exp, Δ custom exp).
Notation "Γ ⊨s σ : Δ" := (valid_sub_under_ctx Γ Δ σ) (in custom judg at level 80, Γ custom exp, σ custom exp, Δ custom exp).
