From Coq Require Import List String Classes.RelationClasses Setoid Morphisms.
From stdpp Require Import base.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Syntax.
Import Syntax_Notations.

(* TODO: better notation to replace Δ ;; Γ *)
Reserved Notation "⊢ Δ ;; Γ" (in custom judg at level 80, Γ custom exp, Δ custom exp).
Reserved Notation "⊢ Δ " (in custom judg at level 80, Δ custom exp).
Reserved Notation "⊢ Δ ;; Γ ≈ Δ' ;; Γ'" (in custom judg at level 80, Δ custom exp, Γ custom exp, Δ' custom exp, Γ' custom exp).
Reserved Notation "Δ ;; Γ ⊢ M ≈ M' : A" (in custom judg at level 80, Δ custom exp, Γ custom exp, M custom exp, M' custom exp, A custom exp).
Reserved Notation "Δ ;; Γ ⊢ M : A" (in custom judg at level 80, Δ custom exp, Γ custom exp, M custom exp, A custom exp).
Reserved Notation "Δ ;; Γ ⊢s σ : Γ'" (in custom judg at level 80, Δ custom exp, Γ custom exp, σ custom exp, Γ' custom exp).
Reserved Notation "Δ ;; Γ ⊢s σ ≈ σ' : Γ'" (in custom judg at level 80, Δ custom exp, Γ custom exp, σ custom exp, σ' custom exp, Γ' custom exp).
Reserved Notation "⊢ Δ ;; Γ ⊆ Δ' ;; Γ'" (in custom judg at level 80, Δ custom exp, Γ custom exp, Δ' custom exp, Γ' custom exp).
Reserved Notation "Δ ;; Γ ⊢ A ⊆ A'" (in custom judg at level 80, Δ custom exp, Γ custom exp, A custom exp, A' custom exp).
Reserved Notation "'#' x : A ∈ Γ" (in custom judg at level 80, x constr at level 0, A custom exp, Γ custom exp at level 50).
(* TODO: better notation to distinguish string from nat *)
Reserved Notation "'`#' x := [ M ] :: A ∈ Δ" (in custom judg at level 80, x constr at level 0, M custom exp, A custom exp, Δ custom exp at level 50).
(* Reserved Notation "'#' x := ∅ :: A ∈ Γ" (in custom judg at level 80, x constr at level 0, A custom exp, Γ custom exp at level 50). *)

Generalizable All Variables.

Inductive ctx_lookup : nat -> typ -> ctx -> Prop :=
  | here : `({{ #0 : A[Wk] ∈ Γ, A }})
  | there : `({{ #n : A ∈ Γ }} -> {{ #(S n) : A[Wk] ∈ Γ, B }})
where "'#' x : A ∈ Γ" := (ctx_lookup x A Γ) (in custom judg) : type_scope.

(* We do not need weaken here because everything is named *)
Inductive gctx_lookup : string -> option exp -> typ -> gctx -> Prop :=
  | ghere : `({{ `#x := [ M ] :: A ∈ Γ, x := [ M ] :: A }})
  | gthere : `(x <> y -> {{ `#y := [ M ] :: A ∈ Γ }} -> {{ `#y := [ M ] :: A ∈ Γ, x := [ N ] :: B }})
where "'`#' x := [ M ] :: A ∈ Δ" := (gctx_lookup x M A Δ) (in custom judg) : type_scope.

(* TODO: check the signature of each judgment *)
Inductive wf_gctx : gctx -> Prop :=
| wf_gctx_empty : {{ ⊢ ⋅ }}
| wf_gctx_extend :
  `( {{ ⊢ Δ }} ->
     {{ Δ ;; ⋅ ⊢ A : Type@i }} ->
     {{ Δ ;; ⋅ ⊢ M : A }} ->
     x ∉ gctx_dom Δ ->
     {{ ⊢ Δ , x := M :: A }} )
| wf_gctx_extend_ax :
  `( {{ ⊢ Δ }} ->
     {{ Δ ;; ⋅ ⊢ A : Type@i }} ->
     x ∉ gctx_dom Δ ->
     {{ ⊢ Δ , x := ∅ :: A }} )
(* TODO: add a case for axiom def *)
where "⊢ Δ " := (wf_gctx Δ) (in custom judg) : type_scope

with wf_ctx : gctx -> ctx -> Prop :=
| wf_ctx_empty : 
  `( {{ ⊢ Δ }} ->
     {{ ⊢ Δ ;; ⋅ }} )
| wf_ctx_extend :
  `( {{ ⊢ Δ ;; Γ }} ->
     {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ ⊢ Δ ;; Γ, A }} )
where "⊢ Δ ;; Γ" := (wf_ctx Δ Γ) (in custom judg) : type_scope

(* with wf_gctx_sub  *)

with wf_ctx_sub : gctx -> ctx -> gctx -> ctx -> Prop :=
| wf_ctx_sub_empty : 
  `( 
      (* TODO: check this, shall we force syntactic equality of two gctx? *)
      {{ ⊢ Δ ;; ⋅ ⊆ Δ ;; ⋅ }} )
| wf_ctx_sub_extend :
  `( {{ ⊢ Δ ;; Γ ⊆ Δ' ;; Γ' }} ->
     {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ' ;; Γ' ⊢ A' : Type@i }} ->
     {{ Δ ;; Γ ⊢ A ⊆ A' }} ->
     {{ ⊢ Δ ;; Γ, A ⊆ Δ' ;; Γ', A' }} )
where "⊢ Δ ;; Γ ⊆ Δ' ;; Γ'" := (wf_ctx_sub Δ Γ Δ' Γ') (in custom judg) : type_scope

with wf_exp : gctx -> ctx -> typ -> exp -> Prop :=
| wf_typ :
  `( {{ ⊢ Δ ;; Γ }} ->
     {{ Δ ;; Γ ⊢ Type@i : Type@(S i) }} )
| wf_nat :
  `( {{ ⊢ Δ ;; Γ }} ->
     {{ Δ ;; Γ ⊢ ℕ : Type@0 }} )
| wf_zero :
  `( {{ ⊢ Δ ;; Γ }} ->
     {{ Δ ;; Γ ⊢ zero : ℕ }} )
| wf_succ :
  `( {{ Δ ;; Γ ⊢ M : ℕ }} ->
     {{ Δ ;; Γ ⊢ succ M : ℕ }} )

| wf_natrec :
  `( {{ Δ ;; Γ, ℕ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ ⊢ MZ : A[Id,,zero] }} ->
     {{ Δ ;; Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
     {{ Δ ;; Γ ⊢ M : ℕ }} ->
     {{ Δ ;; Γ ⊢ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] }} )

| wf_pi :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ B : Type@i }} ->
     {{ Δ ;; Γ ⊢ Π A B : Type@i }} )
| wf_fn :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ M : B }} ->
     {{ Δ ;; Γ ⊢ λ A M : Π A B }} )
| wf_app :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ B : Type@i }} ->
     {{ Δ ;; Γ ⊢ M : Π A B }} ->
     {{ Δ ;; Γ ⊢ N : A }} ->
     {{ Δ ;; Γ ⊢ M N : B[Id,,N] }} )

| wf_sigma :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ B : Type@i }} ->
     {{ Δ ;; Γ ⊢ Σ A B : Type@i }} )
| wf_pair :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ B : Type@i }} ->
     {{ Δ ;; Γ ⊢ M : A }} ->
     {{ Δ ;; Γ ⊢ N : B[Id,,M] }} ->
     {{ Δ ;; Γ ⊢ ⟨ M : A ; N : B ⟩ : Σ A B }} )
| wf_fst :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ B : Type@i }} ->
     {{ Δ ;; Γ ⊢ M : Σ A B }} ->
     {{ Δ ;; Γ ⊢ fst M : A }} )
| wf_snd :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ B : Type@i }} ->
     {{ Δ ;; Γ ⊢ M : Σ A B }} ->
     {{ Δ ;; Γ ⊢ snd M : B[Id,,fst M] }} )

| wf_vlookup :
  `( {{ ⊢ Δ ;; Γ }} ->
     {{ #x : A ∈ Γ }} ->
     {{ Δ ;; Γ ⊢ #x : A }} )
| wf_gvlookup :
  `( {{ ⊢ Δ ;; Γ }} ->
     {{ `#x := [ M ] :: A ∈ Δ }} ->
     {{ Δ ;; Γ ⊢ `#x : A }} )

| wf_eq :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ ⊢ M : A }} ->
     {{ Δ ;; Γ ⊢ N : A }} ->
     {{ Δ ;; Γ ⊢ Eq A M N : Type@i }})
| wf_refl : 
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ ⊢ M : A }} ->
     {{ Δ ;; Γ ⊢ refl A M : Eq A M M }})
| wf_eqrec :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ ⊢ M1 : A }} ->
     {{ Δ ;; Γ ⊢ M2 : A }} ->
     {{ Δ ;; Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢ B : Type@j }} ->
     {{ Δ ;; Γ, A ⊢ BR : B[Id,,#0,,refl A[Wk] #0] }} ->
     {{ Δ ;; Γ ⊢ N : Eq A M1 M2 }} ->
     {{ Δ ;; Γ ⊢ eqrec N as Eq A M1 M2 return B | refl -> BR end : B[Id,,M1,,M2,,N] }} )

| wf_exp_sub :
  `( 
     {{ Δ ;; Γ ⊢s σ : Γ' }} ->
     {{ Δ ;; Γ' ⊢ M : A }} ->
     {{ Δ ;; Γ ⊢ M[σ] : A[σ] }} )
| wf_exp_subtyp :
  `( {{ Δ ;; Γ ⊢ M : A }} ->
    (** We have this extra argument for soundness.
      Note that we need to keep it asymmetric:
      only [A'] is checked. If we check A as well,
      we cannot even construct something like
      [{{ Γ ⊢ Type@0[Wk] : Type@1 }}] with the current
      rules. Under the symmetric rule, the example requires
      [{{ Γ ⊢ Type@1[Wk] : Type@2 }}] to apply [wf_exp_sub],
      which requires [{{ Γ ⊢ Type@2[Wk] : Type@3 }}], and so on.
    *)
    {{ Δ ;; Γ ⊢ A' : Type@i }} ->
    {{ Δ ;; Γ ⊢ A ⊆ A' }} ->
    {{ Δ ;; Γ ⊢ M : A' }} )

where "Δ ;; Γ ⊢ M : A" := (wf_exp Δ Γ A M) (in custom judg) : type_scope


with wf_sub : gctx -> ctx -> ctx -> sub -> Prop :=
| wf_sub_id :
  `( {{ ⊢ Δ ;; Γ }} ->
     {{ Δ ;; Γ ⊢s Id : Γ }} )
| wf_sub_weaken :
  `( {{ ⊢ Δ ;; Γ, A }} ->
     {{ Δ ;; Γ, A ⊢s Wk : Γ }} )
| wf_sub_compose :
  `( {{ Δ ;; Γ1 ⊢s σ2 : Γ2 }} ->
     {{ Δ ;; Γ2 ⊢s σ1 : Γ3 }} ->
     {{ Δ ;; Γ1 ⊢s σ1∘σ2 : Γ3 }} )
| wf_sub_extend :
  `( {{ Δ ;; Γ ⊢s σ : Γ' }} ->
     {{ Δ ;; Γ' ⊢ A : Type@i }} ->
     {{ Δ ;; Γ ⊢ M : A[σ] }} ->
     {{ Δ ;; Γ ⊢s σ,,M : Γ', A }} )
| wf_sub_subtyp :
  `( {{ Δ ;; Γ1 ⊢s σ : Γ2 }} ->
     (** As in [wf_exp_subtyp], this extra argument is
         for soundness. We don't need to keep it asymmetric,
         but do so to match with [wf_exp_subtyp].
      *)
     {{ ⊢ Δ ;; Γ3 }} ->
     {{ ⊢ Δ ;; Γ2 ⊆ Δ ;; Γ3 }} ->
     {{ Δ ;; Γ1 ⊢s σ : Γ3 }} )
where "Δ ;; Γ ⊢s σ : Γ' " := (wf_sub Δ Γ Γ' σ) (in custom judg) : type_scope

with wf_exp_eq : gctx -> ctx -> typ -> exp -> exp -> Prop :=
| wf_exp_eq_typ_sub :
  `( {{ Δ ;; Γ ⊢s σ : Γ' }} ->
     {{ Δ ;; Γ ⊢ Type@i[σ] ≈ Type@i : Type@(S i) }} )

| wf_exp_eq_nat_sub :
  `( {{ Δ ;; Γ ⊢s σ : Γ' }} ->
     {{ Δ ;; Γ ⊢ ℕ[σ] ≈ ℕ : Type@0 }} )
| wf_exp_eq_zero_sub :
  `( {{ Δ ;; Γ ⊢s σ : Γ' }} ->
     {{ Δ ;; Γ ⊢ zero[σ] ≈ zero : ℕ }} )
| wf_exp_eq_succ_sub :
  `( {{ Δ ;; Γ ⊢s σ : Γ' }} ->
     {{ Δ ;; Γ ⊢ M : ℕ }} ->
     {{ Δ ;; Γ ⊢ (succ M)[σ] ≈ succ (M[σ]) : ℕ }} )
| wf_exp_eq_succ_cong :
  `( {{ Δ ;; Γ ⊢ M ≈ M' : ℕ }} ->
     {{ Δ ;; Γ ⊢ succ M ≈ succ M' : ℕ }} )
| wf_exp_eq_natrec_cong :
  `( {{ Δ ;; Γ, ℕ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ, ℕ ⊢ A ≈ A' : Type@i }} ->
     {{ Δ ;; Γ ⊢ MZ ≈ MZ' : A[Id,,zero] }} ->
     {{ Δ ;; Γ, ℕ, A ⊢ MS ≈ MS' : A[Wk∘Wk,,succ #1] }} ->
     {{ Δ ;; Γ ⊢ M ≈ M' : ℕ }} ->
     {{ Δ ;; Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M] }} )
| wf_exp_eq_natrec_sub :
  `( {{ Δ ;; Γ ⊢s σ : Γ' }} ->
     {{ Δ ;; Γ, ℕ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ ⊢ MZ : A[Id,,zero] }} ->
     {{ Δ ;; Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
     {{ Δ ;; Γ ⊢ M : ℕ }} ->
     {{ Δ ;; Γ ⊢ rec M return A | zero -> MZ | succ -> MS end[σ] ≈ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M[σ]] }} )
| wf_exp_eq_nat_beta_zero :
  `( {{ Δ ;; Γ, ℕ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ ⊢ MZ : A[Id,,zero] }} ->
     {{ Δ ;; Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
     {{ Δ ;; Γ ⊢ rec zero return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id,,zero] }} )
| wf_exp_eq_nat_beta_succ :
  `( {{ Δ ;; Γ, ℕ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ ⊢ MZ : A[Id,,zero] }} ->
     {{ Δ ;; Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
     {{ Δ ;; Γ ⊢ M : ℕ }} ->
     {{ Δ ;; Γ ⊢ rec succ M return A | zero -> MZ | succ -> MS end ≈ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] : A[Id,,succ M] }} )

| wf_exp_eq_pi_sub :
  `( {{ Δ ;; Γ ⊢s σ : Γ' }} ->
     {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ B : Type@i }} ->
     {{ Δ ;; Γ ⊢ (Π A B)[σ] ≈ Π A[σ] B[q σ] : Type@i }} )
| wf_exp_eq_pi_cong :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ ⊢ A ≈ A' : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ B ≈ B' : Type@i }} ->
     {{ Δ ;; Γ ⊢ Π A B ≈ Π A' B' : Type@i }} )
| wf_exp_eq_fn_cong :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ ⊢ A ≈ A' : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ M ≈ M' : B }} ->
     {{ Δ ;; Γ ⊢ λ A M ≈ λ A' M' : Π A B }} )
| wf_exp_eq_fn_sub :
  `( {{ Δ ;; Γ ⊢s σ : Γ' }} ->
     {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ M : B }} ->
     {{ Δ ;; Γ ⊢ (λ A M)[σ] ≈ λ A[σ] M[q σ] : (Π A B)[σ] }} )
| wf_exp_eq_app_cong :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ B : Type@i }} ->
     {{ Δ ;; Γ ⊢ M ≈ M' : Π A B }} ->
     {{ Δ ;; Γ ⊢ N ≈ N' : A }} ->
     {{ Δ ;; Γ ⊢ M N ≈ M' N' : B[Id,,N] }} )
| wf_exp_eq_app_sub :
  `( {{ Δ ;; Γ ⊢s σ : Γ' }} ->
     {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ B : Type@i }} ->
     {{ Δ ;; Γ ⊢ M : Π A B }} ->
     {{ Δ ;; Γ ⊢ N : A }} ->
     {{ Δ ;; Γ ⊢ (M N)[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }} )
| wf_exp_eq_pi_beta :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ B : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ M : B }} ->
     {{ Δ ;; Γ ⊢ N : A }} ->
     {{ Δ ;; Γ ⊢ (λ A M) N ≈ M[Id,,N] : B[Id,,N] }} )
| wf_exp_eq_pi_eta :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ B : Type@i }} ->
     {{ Δ ;; Γ ⊢ M : Π A B }} ->
     {{ Δ ;; Γ ⊢ M ≈ λ A (M[Wk] #0) : Π A B }} )

| wf_exp_eq_sigma_sub :
  `( {{ Δ ;; Γ ⊢s σ : Γ' }} ->
     {{ Δ ;; Γ' ⊢ A : Type@i }} ->
     {{ Δ ;; Γ', A ⊢ B : Type@i }} ->
     {{ Δ ;; Γ ⊢ (Σ A B)[σ] ≈ Σ A[σ] B[q σ] : Type@i }} )
| wf_exp_eq_sigma_cong :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ ⊢ A ≈ A' : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ B ≈ B' : Type@i }} ->
     {{ Δ ;; Γ ⊢ Σ A B ≈ Σ A' B' : Type@i }} )
| wf_exp_eq_pair_cong :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ ⊢ A ≈ A' : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ B ≈ B' : Type@i }} ->
     {{ Δ ;; Γ ⊢ M ≈ M' : A }} ->
     {{ Δ ;; Γ ⊢ N ≈ N' : B[Id,,M] }} ->
     {{ Δ ;; Γ ⊢ ⟨ M : A ; N : B ⟩ ≈ ⟨ M' : A' ; N' : B' ⟩ : Σ A B }} )
| wf_exp_eq_pair_sub :
  `( {{ Δ ;; Γ ⊢s σ : Γ' }} ->
     {{ Δ ;; Γ' ⊢ A : Type@i }} ->
     {{ Δ ;; Γ', A ⊢ B : Type@i }} ->
     {{ Δ ;; Γ' ⊢ M : A }} ->
     {{ Δ ;; Γ' ⊢ N : B[Id,,M] }} ->
     {{ Δ ;; Γ ⊢ ⟨ M : A ; N : B ⟩[σ] ≈ ⟨ M[σ] : A[σ] ; N[σ] : B[q σ] ⟩ : (Σ A B)[σ] }} )
| wf_exp_eq_fst_cong :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ B : Type@i }} ->
     {{ Δ ;; Γ ⊢ M ≈ M' : Σ A B }} ->
     {{ Δ ;; Γ ⊢ fst M ≈ fst M' : A }} )
| wf_exp_eq_fst_sub :
  `( {{ Δ ;; Γ ⊢s σ : Γ' }} ->
     {{ Δ ;; Γ' ⊢ A : Type@i }} ->
     {{ Δ ;; Γ', A ⊢ B : Type@i }} ->
     {{ Δ ;; Γ' ⊢ M : Σ A B }} ->
     {{ Δ ;; Γ ⊢ (fst M)[σ] ≈ fst (M[σ]) : A[σ] }} )
| wf_exp_eq_snd_cong :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ B : Type@i }} ->
     {{ Δ ;; Γ ⊢ M ≈ M' : Σ A B }} ->
     {{ Δ ;; Γ ⊢ snd M ≈ snd M' : B[Id,,fst M] }} )
| wf_exp_eq_snd_sub :
  `( {{ Δ ;; Γ ⊢s σ : Γ' }} ->
     {{ Δ ;; Γ' ⊢ A : Type@i }} ->
     {{ Δ ;; Γ', A ⊢ B : Type@i }} ->
     {{ Δ ;; Γ' ⊢ M : Σ A B }} ->
     {{ Δ ;; Γ ⊢ (snd M)[σ] ≈ snd (M[σ]) : B[σ,,fst (M[σ])] }} )
| wf_exp_eq_fst_beta :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ B : Type@i }} ->
     {{ Δ ;; Γ ⊢ M : A }} ->
     {{ Δ ;; Γ ⊢ N : B[Id,,M] }} ->
     {{ Δ ;; Γ ⊢ fst (⟨ M : A ; N : B⟩) ≈ M : A }} )
| wf_exp_eq_snd_beta :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ B : Type@i }} ->
     {{ Δ ;; Γ ⊢ M : A }} ->
     {{ Δ ;; Γ ⊢ N : B[Id,,M] }} ->
     {{ Δ ;; Γ ⊢ snd ⟨ M : A ; N : B ⟩ ≈ N : B[Id,,M] }} )
| wf_exp_eq_sigma_eta :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ B : Type@i }} ->
     {{ Δ ;; Γ ⊢ M : Σ A B }} ->
     {{ Δ ;; Γ ⊢ M ≈ ⟨ fst M : A ; snd M : B ⟩ : Σ A B }} )

| wf_exp_eq_eq_sub :
  `( {{ Δ ;; Γ ⊢s σ : Γ' }} ->
     {{ Δ ;; Γ' ⊢ A : Type@i }} ->
     {{ Δ ;; Γ' ⊢ M : A }} ->
     {{ Δ ;; Γ' ⊢ N : A }} ->
     {{ Δ ;; Γ ⊢ (Eq A M N)[σ] ≈ Eq A[σ] M[σ] N[σ] : Type@i }} )
| wf_exp_eq_refl_sub :
  `( {{ Δ ;; Γ ⊢s σ : Γ' }} ->
     {{ Δ ;; Γ' ⊢ A : Type@i }} ->
     {{ Δ ;; Γ' ⊢ M : A }} ->
     {{ Δ ;; Γ ⊢ (refl A M)[σ] ≈ refl A[σ] M[σ] : (Eq A M M)[σ] }} )
| wf_exp_eq_eqrec_sub :
  `( {{ Δ ;; Γ ⊢s σ : Γ' }} ->
     {{ Δ ;; Γ' ⊢ A : Type@i }} ->
     {{ Δ ;; Γ' ⊢ M1 : A }} ->
     {{ Δ ;; Γ' ⊢ M2 : A }} ->
     {{ Δ ;; Γ', A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢ B : Type@j }} ->
     {{ Δ ;; Γ', A ⊢ BR : B[Id,,#0,,refl A[Wk] #0] }} ->
     {{ Δ ;; Γ' ⊢ N : Eq A M1 M2 }} ->
     {{ Δ ;; Γ ⊢ eqrec N as Eq A M1 M2 return B | refl -> BR end[σ] 
               ≈ eqrec N[σ] as Eq A[σ] M1[σ] M2[σ] return B[q (q (q σ))] | refl -> BR[q σ] end
                 : B[σ,,M1[σ],,M2[σ],,N[σ]] }} )
| wf_exp_eq_eq_cong :
  `( {{ Δ ;; Γ ⊢ A ≈ A' : Type@i }} ->
     {{ Δ ;; Γ ⊢ M ≈ M' : A }} ->
     {{ Δ ;; Γ ⊢ N ≈ N' : A }} ->
     {{ Δ ;; Γ ⊢ Eq A M N ≈ Eq A' M' N' : Type@i }})
| wf_exp_eq_refl_cong :
  `( {{ Δ ;; Γ ⊢ A ≈ A' : Type@i }} ->
     {{ Δ ;; Γ ⊢ M ≈ M' : A }} ->
     {{ Δ ;; Γ ⊢ refl A M ≈ refl A' M' : Eq A M M }})
| wf_exp_eq_eqrec_cong :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ ⊢ M1 : A }} ->
     {{ Δ ;; Γ ⊢ M2 : A }} ->
     {{ Δ ;; Γ ⊢ A ≈ A' : Type@i }} ->
     {{ Δ ;; Γ ⊢ M1 ≈ M1' : A }} ->
     {{ Δ ;; Γ ⊢ M2 ≈ M2' : A }} ->
     {{ Δ ;; Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢ B ≈ B' : Type@j }} ->
     {{ Δ ;; Γ, A ⊢ BR ≈ BR' : B[Id,,#0,,refl A[Wk] #0] }} ->
     {{ Δ ;; Γ ⊢ N ≈ N' : Eq A M1 M2 }} ->
     {{ Δ ;; Γ ⊢ eqrec N as Eq A M1 M2 return B | refl -> BR end 
               ≈ eqrec N' as Eq A' M1' M2' return B' | refl -> BR' end
         : B[Id,,M1,,M2,,N] }} )
| wf_exp_eq_eqrec_beta :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ ⊢ M : A }} ->
     {{ Δ ;; Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢ B : Type@j }} ->
     {{ Δ ;; Γ, A ⊢ BR : B[Id,,#0,,refl A[Wk] #0] }} ->
     {{ Δ ;; Γ ⊢ eqrec refl A M as Eq A M M return B | refl -> BR end 
               ≈ BR[Id,,M]
         : B[Id,,M,,M,,refl A M] }} )

| wf_exp_eq_var :
  `( {{ ⊢ Δ ;; Γ }} ->
     {{ #x : A ∈ Γ }} ->
     {{ Δ ;; Γ ⊢ #x ≈ #x : A }} )
| wf_exp_eq_var_0_sub :
  `( {{ Δ ;; Γ ⊢s σ : Γ' }} ->
     {{ Δ ;; Γ' ⊢ A : Type@i }} ->
     {{ Δ ;; Γ ⊢ M : A[σ] }} ->
     {{ Δ ;; Γ ⊢ #0[σ,,M] ≈ M : A[σ] }} )
| wf_exp_eq_var_S_sub :
  `( {{ Δ ;; Γ ⊢s σ : Γ' }} ->
     {{ Δ ;; Γ' ⊢ A : Type@i }} ->
     {{ Δ ;; Γ ⊢ M : A[σ] }} ->
     {{ #x : B ∈ Γ' }} ->
     {{ Δ ;; Γ ⊢ #(S x)[σ,,M] ≈ #x[σ] : B[σ] }} )
| wf_exp_eq_var_weaken :
  `( {{ ⊢ Δ ;; Γ, B }} ->
     {{ #x : A ∈ Γ }} ->
     {{ Δ ;; Γ, B ⊢ #x[Wk] ≈ #(S x) : A[Wk] }} )
| wf_exp_eq_sub_cong :
  `( {{ Δ ;; Γ' ⊢ M ≈ M' : A }} ->
     {{ Δ ;; Γ ⊢s σ ≈ σ' : Γ' }} ->
     {{ Δ ;; Γ ⊢ M[σ] ≈ M'[σ'] : A[σ] }} )
| wf_exp_eq_sub_id :
  `( {{ Δ ;; Γ ⊢ M : A }} ->
     {{ Δ ;; Γ ⊢ M[Id] ≈ M : A }} )
| wf_exp_eq_sub_compose :
  `( {{ Δ ;; Γ ⊢s τ : Γ' }} ->
     {{ Δ ;; Γ' ⊢s σ : Γ'' }} ->
     {{ Δ ;; Γ'' ⊢ M : A }} ->
     {{ Δ ;; Γ ⊢ M[σ∘τ] ≈ M[σ][τ] : A[σ∘τ] }} )

| wf_exp_eq_delta :
  `( {{ ⊢ Δ ;; Γ }} ->
     {{ `#x := [ M ] :: A ∈ Δ }} ->
     (M = Some M') ->
     {{ Δ ;; Γ ⊢ `#x ≈ M' : A }} )
| wf_exp_eq_gvar_ax_refl :
  `( {{ ⊢ Δ ;; Γ }} ->
     {{ `#x := [ M ] :: A ∈ Δ }} ->
     (M = None) ->
     {{ Δ ;; Γ ⊢ `#x ≈ `#x : A }} )

| wf_exp_eq_subtyp :
  `( {{ Δ ;; Γ ⊢ M ≈ M' : A }} ->
     {{ Δ ;; Γ ⊢ A' : Type@i }} ->
     (** This extra argument is here to be consistent with
         [wf_exp_subtyp].
      *)
     {{ Δ ;; Γ ⊢ A ⊆ A' }} ->
     {{ Δ ;; Γ ⊢ M ≈ M' : A' }} )
| wf_exp_eq_sym :
  `( {{ Δ ;; Γ ⊢ M ≈ M' : A }} ->
     {{ Δ ;; Γ ⊢ M' ≈ M : A }} )
| wf_exp_eq_trans :
  `( {{ Δ ;; Γ ⊢ M ≈ M' : A }} ->
     {{ Δ ;; Γ ⊢ M' ≈ M'' : A }} ->
     {{ Δ ;; Γ ⊢ M ≈ M'' : A }} )

where "Δ ;; Γ ⊢ M ≈ M' : A" := (wf_exp_eq Δ Γ A M M') (in custom judg) : type_scope

with wf_sub_eq : gctx -> ctx -> ctx -> sub -> sub -> Prop :=
| wf_sub_eq_id :
  `( {{ ⊢ Δ ;; Γ }} ->
     {{ Δ ;; Γ ⊢s Id ≈ Id : Γ }} )
| wf_sub_eq_weaken :
  `( {{ ⊢ Δ ;; Γ, A }} ->
     {{ Δ ;; Γ, A ⊢s Wk ≈ Wk : Γ }} )
| wf_sub_eq_compose_cong :
  `( {{ Δ ;; Γ ⊢s τ ≈ τ' : Γ' }} ->
     {{ Δ ;; Γ' ⊢s σ ≈ σ' : Γ'' }} ->
     {{ Δ ;; Γ ⊢s σ∘τ ≈ σ'∘τ' : Γ'' }} )
| wf_sub_eq_extend_cong :
  `( {{ Δ ;; Γ ⊢s σ ≈ σ' : Γ' }} ->
     {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ ⊢ M ≈ M' : A[σ] }} ->
     {{ Δ ;; Γ ⊢s σ,,M ≈ σ',,M' : Γ', A }} )
| wf_sub_eq_id_compose_right :
  `( {{ Δ ;; Γ ⊢s σ : Γ' }} ->
     {{ Δ ;; Γ ⊢s Id∘σ ≈ σ : Γ' }} )
| wf_sub_eq_id_compose_left :
  `( {{ Δ ;; Γ ⊢s σ : Γ' }} ->
     {{ Δ ;; Γ ⊢s σ∘Id ≈ σ : Γ' }} )
| wf_sub_eq_compose_assoc :
  `( {{ Δ ;; Γ2 ⊢s σ : Γ1 }} ->
     {{ Δ ;; Γ3 ⊢s σ' : Γ2 }} ->
     {{ Δ ;; Γ4 ⊢s σ'' : Γ3 }} ->
     {{ Δ ;; Γ4 ⊢s (σ∘σ')∘σ'' ≈ σ∘(σ'∘σ'') : Γ1 }} )
| wf_sub_eq_extend_compose :
  `( {{ Δ ;; Γ' ⊢s σ : Γ'' }} ->
     {{ Δ ;; Γ'' ⊢ A : Type@i }} ->
     {{ Δ ;; Γ' ⊢ M : A[σ] }} ->
     {{ Δ ;; Γ ⊢s τ : Γ' }} ->
     {{ Δ ;; Γ ⊢s (σ,,M)∘τ ≈ (σ∘τ),,M[τ] : Γ'', A }} )
| wf_sub_eq_p_extend :
  `( {{ Δ ;; Γ' ⊢s σ : Γ }} ->
     {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ' ⊢ M : A[σ] }} ->
     {{ Δ ;; Γ' ⊢s Wk∘(σ,,M) ≈ σ : Γ }} )
| wf_sub_eq_extend :
  `( {{ Δ ;; Γ' ⊢s σ : Γ, A }} ->
     {{ Δ ;; Γ' ⊢s σ ≈ (Wk∘σ),,#0[σ] : Γ, A }} )
| wf_sub_eq_sym :
  `( {{ Δ ;; Γ ⊢s σ ≈ σ' : Γ' }} ->
     {{ Δ ;; Γ ⊢s σ' ≈ σ : Γ' }} )
| wf_sub_eq_trans :
  `( {{ Δ ;; Γ ⊢s σ ≈ σ' : Γ' }} ->
     {{ Δ ;; Γ ⊢s σ' ≈ σ'' : Γ' }} ->
     {{ Δ ;; Γ ⊢s σ ≈ σ'' : Γ' }} )
| wf_sub_eq_subtyp :
  `( {{ Δ ;; Γ ⊢s σ ≈ σ' : Γ' }} ->
     (** This extra argument is here to be consistent with
         [wf_sub_subtyp].
      *)
     {{ ⊢ Δ ;; Γ'' }} ->
     {{ ⊢ Δ ;; Γ' ⊆ Δ ;; Γ'' }} ->
     {{ Δ ;; Γ ⊢s σ ≈ σ' : Γ'' }} )
where "Δ ;; Γ ⊢s σ ≈ σ' : Γ'" := (wf_sub_eq Δ Γ Γ' σ σ') (in custom judg) : type_scope

with wf_subtyp : gctx -> ctx -> typ -> typ -> Prop :=
| wf_subtyp_refl :
  (** We need this extra argument in order to prove the lemmas
      in CtxSub.v independently. We can prove those and
      presupposition lemmas mutually dependently, but that would
      be more messy.

      The main point of this assumption gives presupposition for
      RHS directly so that we can remove the extra arguments in
      type checking rules immediately.
   *)
  `( {{ Δ ;; Γ ⊢ M' : Type@i }} ->
     {{ Δ ;; Γ ⊢ M ≈ M' : Type@i }} ->
     {{ Δ ;; Γ ⊢ M ⊆ M' }} )
| wf_subtyp_trans :
  `( {{ Δ ;; Γ ⊢ M ⊆ M' }} ->
     {{ Δ ;; Γ ⊢ M' ⊆ M'' }} ->
     {{ Δ ;; Γ ⊢ M ⊆ M'' }} )
| wf_subtyp_univ :
  `( {{ ⊢ Δ ;; Γ }} ->
     i < j ->
     {{ Δ ;; Γ ⊢ Type@i ⊆ Type@j }} )
| wf_subtyp_pi :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ ⊢ A' : Type@i }} ->
     {{ Δ ;; Γ ⊢ A ≈ A' : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ B : Type@i }} ->
     {{ Δ ;; Γ, A' ⊢ B' : Type@i }} ->
     {{ Δ ;; Γ, A' ⊢ B ⊆ B' }} ->
     {{ Δ ;; Γ ⊢ Π A B ⊆ Π A' B' }} )
| wf_subtyp_sigma :
  `( {{ Δ ;; Γ ⊢ A : Type@i }} ->
     {{ Δ ;; Γ ⊢ A' : Type@i }} ->
     {{ Δ ;; Γ ⊢ A ≈ A' : Type@i }} ->
     {{ Δ ;; Γ, A ⊢ B : Type@i }} ->
     {{ Δ ;; Γ, A' ⊢ B' : Type@i }} ->
     (* Although A and A' are equal, it may be more natural to
        use Γ, A ⊢ B ⊆ B'. but Γ, A' ⊢ B ⊆ B', on the other hand,
        can reuse some properties proved for the Π case *)
     {{ Δ ;; Γ, A' ⊢ B ⊆ B' }} ->
     {{ Δ ;; Γ ⊢ Σ A B ⊆ Σ A' B' }} )
where "Δ ;; Γ ⊢ A ⊆ A'" := (wf_subtyp Δ Γ A A') (in custom judg) : type_scope
.

Scheme 
wf_gctx_mut_ind := Induction for wf_gctx Sort Prop
with wf_ctx_mut_ind := Induction for wf_ctx Sort Prop
with wf_ctx_sub_mut_ind := Induction for wf_ctx_sub Sort Prop
with wf_exp_mut_ind := Induction for wf_exp Sort Prop
with wf_exp_eq_mut_ind := Induction for wf_exp_eq Sort Prop
with wf_sub_mut_ind := Induction for wf_sub Sort Prop
with wf_sub_eq_mut_ind := Induction for wf_sub_eq Sort Prop
with wf_subtyp_mut_ind := Induction for wf_subtyp Sort Prop.
Combined Scheme syntactic_wf_mut_ind from
  wf_gctx_mut_ind,
  wf_ctx_mut_ind,
  wf_ctx_sub_mut_ind,
  wf_exp_mut_ind,
  wf_exp_eq_mut_ind,
  wf_sub_mut_ind,
  wf_sub_eq_mut_ind,
  wf_subtyp_mut_ind.

Scheme wf_ctx_mut_ind' := Induction for wf_ctx Sort Prop
with wf_exp_mut_ind' := Induction for wf_exp Sort Prop
with wf_sub_mut_ind' := Induction for wf_sub Sort Prop.
Combined Scheme syntactic_wf_mut_ind' from
  wf_ctx_mut_ind',
  wf_exp_mut_ind',
  wf_sub_mut_ind'.

Inductive wf_ctx_eq : ctx -> ctx -> Prop :=
| wf_ctx_eq_empty : {{ ⊢ ⋅ ≈ ⋅ }}
| wf_ctx_eq_extend :
  `( {{ ⊢ Γ ≈ Δ }} ->
     {{ Γ ⊢ A : Type@i }} ->
     {{ Γ ⊢ A' : Type@i }} ->
     {{ Δ ⊢ A : Type@i }} ->
     {{ Δ ⊢ A' : Type@i }} ->
     {{ Γ ⊢ A ≈ A' : Type@i }} ->
     {{ Δ ⊢ A ≈ A' : Type@i }} ->
     {{ ⊢ Γ, A ≈ Δ, A' }} )
where "⊢ Γ ≈ Γ'" := (wf_ctx_eq Γ Γ') (in custom judg) : type_scope.

#[export]
Hint Constructors wf_ctx wf_ctx_eq wf_ctx_sub wf_exp wf_sub wf_exp_eq wf_sub_eq wf_subtyp ctx_lookup : mctt.

#[export]
Instance wf_exp_eq_PER Γ A : PER (wf_exp_eq Γ A).
Proof.
  split.
  - eauto using wf_exp_eq_sym.
  - eauto using wf_exp_eq_trans.
Qed.

#[export]
Instance wf_sub_eq_PER Γ Δ : PER (wf_sub_eq Γ Δ).
Proof.
  split.
  - eauto using wf_sub_eq_sym.
  - eauto using wf_sub_eq_trans.
Qed.

#[export]
Instance wf_ctx_eq_Symmetric : Symmetric wf_ctx_eq.
Proof.
  induction 1; mauto.
Qed.

#[export]
Instance wf_subtyp_Transitive Γ : Transitive (wf_subtyp Γ).
Proof.
  hnf; mauto.
Qed.

(** Immediate & Independent Presuppositions *)

Lemma presup_ctx_sub : forall {Γ Δ}, {{ ⊢ Γ ⊆ Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof with mautosolve.
  induction 1; destruct_pairs...
Qed.

#[export]
Hint Resolve presup_ctx_sub : mctt.

Lemma presup_ctx_sub_left : forall {Γ Δ}, {{ ⊢ Γ ⊆ Δ }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%presup_ctx_sub...
Qed.

#[export]
Hint Resolve presup_ctx_sub_left : mctt.

Lemma presup_ctx_sub_right : forall {Γ Δ}, {{ ⊢ Γ ⊆ Δ }} -> {{ ⊢ Δ }}.
Proof with easy.
  intros * ?%presup_ctx_sub...
Qed.

#[export]
Hint Resolve presup_ctx_sub_right : mctt.

Lemma presup_subtyp_right : forall {Γ A B}, {{ Γ ⊢ A ⊆ B }} -> exists i, {{ Γ ⊢ B : Type@i }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve presup_subtyp_right : mctt.

(** Subtyping Rules without Extra Arguments *)

Lemma wf_exp_subtyp' : forall Γ A A' M,
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ A ⊆ A' }} ->
    {{ Γ ⊢ M : A' }}.
Proof.
  intros.
  assert (exists i, {{ Γ ⊢ A' : Type@i }}) as [] by mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_exp_subtyp' : mctt.
#[export]
Remove Hints wf_exp_subtyp : mctt.

Lemma wf_sub_subtyp' : forall Γ Δ Δ' σ,
    {{ Γ ⊢s σ : Δ }} ->
    {{ ⊢ Δ ⊆ Δ' }} ->
    {{ Γ ⊢s σ : Δ' }}.
Proof.
  intros.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_sub_subtyp' : mctt.
#[export]
Remove Hints wf_sub_subtyp : mctt.

Lemma wf_exp_eq_subtyp' : forall Γ A A' M M',
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢ A ⊆ A' }} ->
    {{ Γ ⊢ M ≈ M' : A' }}.
Proof.
  intros.
  assert (exists i, {{ Γ ⊢ A' : Type@i }}) as [] by mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_exp_eq_subtyp' : mctt.
#[export]
Remove Hints wf_exp_eq_subtyp : mctt.

Lemma wf_sub_eq_subtyp' : forall Γ Δ Δ' σ σ',
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ ⊢ Δ ⊆ Δ' }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ' }}.
Proof.
  intros.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_sub_eq_subtyp' : mctt.
#[export]
Remove Hints wf_sub_eq_subtyp : mctt.

Add Parametric Morphism Γ T : (wf_exp_eq Γ T)
    with signature wf_exp_eq Γ T ==> eq ==> iff as wf_exp_eq_morphism_iff1.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism Γ T : (wf_exp_eq Γ T)
    with signature eq ==> wf_exp_eq Γ T ==> iff as wf_exp_eq_morphism_iff2.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism Γ Δ : (wf_sub_eq Γ Δ)
    with signature wf_sub_eq Γ Δ ==> eq ==> iff as wf_sub_eq_morphism_iff1.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism Γ Δ : (wf_sub_eq Γ Δ)
    with signature eq ==> wf_sub_eq Γ Δ ==> iff as wf_sub_eq_morphism_iff2.
Proof.
  split; mauto.
Qed.

#[export]
Hint Rewrite -> wf_exp_eq_typ_sub wf_exp_eq_nat_sub wf_exp_eq_eq_sub using mauto 3 : mctt.

#[export]
Hint Rewrite -> wf_sub_eq_id_compose_right wf_sub_eq_id_compose_left
                  wf_sub_eq_compose_assoc (* prefer right association *)
                  wf_sub_eq_p_extend using mauto 4 : mctt.

#[export]
Hint Rewrite -> wf_exp_eq_sub_id wf_exp_eq_pi_sub wf_exp_eq_sigma_sub using mauto 4 : mctt.

#[export]
Instance wf_exp_eq_per_elem Γ T : PERElem _ (wf_exp Γ T) (wf_exp_eq Γ T).
Proof.
  intros a Ha. mauto.
Qed.


#[export]
Instance wf_sub_eq_per_elem Γ Δ : PERElem _ (wf_sub Γ Δ) (wf_sub_eq Γ Δ).
Proof.
  intros a Ha. mauto.
Qed.
