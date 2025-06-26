From Mctt.Algorithmic.Subtyping Require Export Definitions.
From Mctt.Core Require Import Base.
Import Domain_Notations.

Reserved Notation "Γ '⊢a' M ⟹ A" (in custom judg at level 80, Γ custom exp, M custom exp, A custom nf).
Reserved Notation "Γ '⊢a' M ⟸ A" (in custom judg at level 80, Γ custom exp, M custom exp, A custom exp).

Generalizable All Variables.

Inductive alg_type_check : ctx -> typ -> exp -> Prop :=
| atc_ati :
  `( {{ Γ ⊢a M ⟹ A }} ->
     {{ Γ ⊢a A ⊆ B }} ->
     {{ Γ ⊢a M ⟸ B }} )
where "Γ '⊢a' M ⟸ A" := (alg_type_check Γ A M) (in custom judg) : type_scope
with alg_type_infer : ctx -> nf -> exp -> Prop :=
| ati_typ :
  `( {{ Γ ⊢a Type@i ⟹ Type@(S i) }} )
| ati_nat :
  `( {{ Γ ⊢a ℕ ⟹ Type@0 }} )
| ati_zero :
  `( {{ Γ ⊢a zero ⟹ ℕ }} )
| ati_succ :
  `( {{ Γ ⊢a M ⟸ ℕ }} ->
     {{ Γ ⊢a succ M ⟹ ℕ }} )
| ati_natrec :
  `( {{ Γ, ℕ ⊢a A ⟹ Type@i }} ->
     {{ Γ ⊢a MZ ⟸ A[Id,,zero] }} ->
     {{ Γ, ℕ, A ⊢a MS ⟸ A[Wk∘Wk,,succ #1] }} ->
     {{ Γ ⊢a M ⟸ ℕ }} ->
     nbe_ty Γ {{{ A[Id,,M] }}} B ->
     {{ Γ ⊢a rec M return A | zero -> MZ | succ -> MS end ⟹ B }} )
| ati_pi :
  `( {{ Γ ⊢a A ⟹ Type@i }} ->
     {{ Γ, A ⊢a B ⟹ Type@j }} ->
     {{ Γ ⊢a Π A B ⟹ Type@(max i j) }} )
| ati_fn :
  `( {{ Γ ⊢a A ⟹ Type@i }} ->
     {{ Γ, A ⊢a M ⟹ B }} ->
     nbe_ty Γ A C ->
     {{ Γ ⊢a λ A M ⟹ Π C B }} )
| ati_app :
  `( {{ Γ ⊢a M ⟹ Π A B }} ->
     {{ Γ ⊢a N ⟸ A }} ->
     nbe_ty Γ {{{ B[Id,,N] }}} C ->
     {{ Γ ⊢a M N ⟹ C }} )
| ati_eq :
  `( {{ Γ ⊢a A ⟹ Type@i }} ->
     {{ Γ ⊢a M1 ⟸ A }} ->
     {{ Γ ⊢a M2 ⟸ A }} ->
     {{ Γ ⊢a Eq A M1 M2 ⟹ Type@i }} )
| ati_refl :
  `( {{ Γ ⊢a A ⟹ Type@i }} ->
     {{ Γ ⊢a M ⟸ A }} ->
     nbe_ty Γ A C ->
     nbe Γ M A N ->
     {{ Γ ⊢a refl A M ⟹ Eq C N N }} )
| ati_eqrec :
  `( {{ Γ ⊢a A ⟹ Type@i }} ->
     {{ Γ ⊢a M1 ⟸ A }} ->
     {{ Γ ⊢a M2 ⟸ A }} ->
     {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢a B ⟹ Type@j }} ->
     {{ Γ, A ⊢a BR ⟸ B[Id,,#0,,refl A[Wk] #0] }} ->
     {{ Γ ⊢a N ⟸ Eq A M1 M2 }} ->
     nbe_ty Γ {{{ B[Id,,M1,,M2,,N] }}} C ->
     {{ Γ ⊢a eqrec N as Eq A M1 M2 return B | refl -> BR end ⟹ C }} )
| ati_vlookup :
  `( {{ #x : A ∈ Γ }} ->
     nbe_ty Γ A B ->
     {{ Γ ⊢a #x ⟹ B }} )
where "Γ '⊢a' M ⟹ A" := (alg_type_infer Γ A M) (in custom judg) : type_scope.

#[export]
Hint Constructors alg_type_check alg_type_infer : mctt.

Scheme alg_type_check_mut_ind := Induction for alg_type_check Sort Prop
with alg_type_infer_mut_ind := Induction for alg_type_infer Sort Prop.
Combined Scheme alg_type_mut_ind from
  alg_type_check_mut_ind,
  alg_type_infer_mut_ind.
