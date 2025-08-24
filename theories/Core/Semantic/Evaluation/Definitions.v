From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export Domain.
Import Domain_Notations.

Reserved Notation "'⟦' M '⟧' ρ '↘' r" (in custom judg at level 80, M custom exp at level 99, ρ custom domain at level 99, r custom domain at level 99).
Reserved Notation "'rec' m '⟦return' A | 'zero' -> MZ | 'succ' -> MS 'end⟧' ρ '↘' r" (in custom judg at level 80, m custom domain at level 99, A custom exp at level 99, MZ custom exp at level 99, MS custom exp at level 99, ρ custom domain at level 99, r custom domain at level 99).
Reserved Notation "'$|' m '&' n '|↘' r" (in custom judg at level 80, m custom domain at level 99, n custom domain at level 99, r custom domain at level 99).
Reserved Notation "'π₁' n ↘ r" (in custom judg at level 80, n custom domain at level 99, r custom domain at level 99).
Reserved Notation "'π₂' n ↘ r" (in custom judg at level 80, n custom domain at level 99, r custom domain at level 99).
Reserved Notation "'eqrec' n 'as' 'Eq' a m1 m2 '⟦return' B | 'refl' -> BR 'end⟧' ρ '↘' r" (in custom judg at level 80, n custom domain at level 99, a custom domain at level 30, m1 custom domain at level 35, m2 custom domain at level 40, B custom exp at level 99, BR custom exp at level 99, ρ custom domain at level 99, r custom domain at level 99).
Reserved Notation "'⟦' σ '⟧s' ρ '↘' ρσ" (in custom judg at level 80, σ custom exp at level 99, ρ custom domain at level 99, ρσ custom domain at level 99).

Generalizable All Variables.

Inductive eval_exp : exp -> env -> domain -> Prop :=
| eval_exp_typ :
  `( {{ ⟦ Type@i ⟧ ρ ↘ 𝕌@i }} )
| eval_exp_var :
  `( {{ ⟦ # x ⟧ ρ ↘ ^(ρ x) }} )
| eval_exp_nat :
  `( {{ ⟦ ℕ ⟧ ρ ↘ ℕ }} )
| eval_exp_zero :
  `( {{ ⟦ zero ⟧ ρ ↘ zero }} )
| eval_exp_succ :
  `( {{ ⟦ M ⟧ ρ ↘ m }} ->
     {{ ⟦ succ M ⟧ ρ ↘ succ m }} )
| eval_exp_natrec :
  `( {{ ⟦ M ⟧ ρ ↘ m }} ->
     {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} ->
     {{ ⟦ rec M return A | zero -> MZ | succ -> MS end ⟧ ρ ↘ r }} )
| eval_exp_pi :
  `( {{ ⟦ A ⟧ ρ ↘ a }} ->
     {{ ⟦ Π A B ⟧ ρ ↘ Π a ρ B }} )
| eval_exp_fn :
  `( {{ ⟦ λ A M ⟧ ρ ↘ λ ρ M }} )
| eval_exp_sigma :
  `( {{ ⟦ A ⟧ ρ ↘ a }} ->
     {{ ⟦ Σ A B ⟧ ρ ↘ Σ a ρ B }} )
| eval_exp_pair :
  `( {{ ⟦ M ⟧ ρ ↘ a }} ->
     {{ ⟦ N ⟧ ρ ↘ b }} ->
     {{ ⟦ ⟨ M ; N : B ⟩ ⟧ ρ ↘ ⟨ a ; b ⟩ }} )
| eval_exp_app :
  `( {{ ⟦ M ⟧ ρ ↘ m }} ->
     {{ ⟦ N ⟧ ρ ↘ n }} ->
     {{ $| m & n |↘ r }} ->
     {{ ⟦ M N ⟧ ρ ↘ r }} )
| eval_exp_eq :
  `( {{ ⟦ A ⟧ ρ ↘ a }} ->
     {{ ⟦ M1 ⟧ ρ ↘ m1 }} ->
     {{ ⟦ M2 ⟧ ρ ↘ m2 }} ->
     {{ ⟦ Eq A M1 M2 ⟧ ρ ↘ Eq a m1 m2 }} )
| eval_exp_refl :
  `( {{ ⟦ M ⟧ ρ ↘ m }} ->
     {{ ⟦ refl A M ⟧ ρ ↘ refl m }} )
| eval_exp_eqrec :
  `( {{ ⟦ A ⟧ ρ ↘ a }} ->
     {{ ⟦ M1 ⟧ ρ ↘ m1 }} ->
     {{ ⟦ M2 ⟧ ρ ↘ m2 }} ->
     {{ ⟦ N ⟧ ρ ↘ n }} ->
     {{ eqrec n as Eq a m1 m2 ⟦return B | refl -> BR end⟧ ρ ↘ r }} ->
     {{ ⟦ eqrec N as Eq A M1 M2 return B | refl -> BR end ⟧ ρ ↘ r }} )
| eval_exp_sub :
  `( {{ ⟦ σ ⟧s ρ ↘ ρ' }} ->
     {{ ⟦ M ⟧ ρ' ↘ m }} ->
     {{ ⟦ M[σ] ⟧ ρ ↘ m }} )
where "'⟦' e '⟧' ρ '↘' r" := (eval_exp e ρ r) (in custom judg)
with eval_natrec : exp -> exp -> exp -> domain -> env -> domain -> Prop :=
| eval_natrec_zero :
  `( {{ ⟦ MZ ⟧ ρ ↘ mz }} ->
     {{ rec zero ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ mz }} )
| eval_natrec_succ :
  `( {{ rec b ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} ->
     {{ ⟦ MS ⟧ ρ ↦ b ↦ r ↘ ms }} ->
     {{ rec succ b ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ ms }} )
| eval_natrec_neut :
  `( {{ ⟦ MZ ⟧ ρ ↘ mz }} ->
     {{ ⟦ A ⟧ ρ ↦ ⇑ b m ↘ a }} ->
     {{ rec ⇑ b m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ ⇑ a (rec m under ρ return A | zero -> mz | succ -> MS end) }} )
where "'rec' m '⟦return' A | 'zero' -> MZ | 'succ' -> MS 'end⟧' ρ '↘' r" := (eval_natrec A MZ MS m ρ r) (in custom judg)
with eval_app : domain -> domain -> domain -> Prop :=
| eval_app_fn :
  `( {{ ⟦ M ⟧ ρ ↦ n ↘ m }} ->
     {{ $| λ ρ M & n |↘ m }} )
| eval_app_neut :
  `( {{ ⟦ B ⟧ ρ ↦ n ↘ b }} ->
     {{ $| ⇑ (Π a ρ B) m & n |↘ ⇑ b (m (⇓ a n)) }} )
where "'$|' m '&' n '|↘' r" := (eval_app m n r) (in custom judg)
with fst_app : domain -> domain -> Prop :=
| fst_app_pair :
  `( {{ π₁ ⟨ a ; b ⟩ ↘ a }} )
| fst_app_neut : 
  `( {{ π₁ ⇑ (Σ a ρ B) m ↘ ⇑ a (fst m) }} )
where "'π₁' n '↘' r" := (fst_app n r) (in custom judg)
with snd_app : domain -> domain -> Prop :=
| snd_app_pair :
  `( {{ π₂ ⟨ a ; b ⟩ ↘ b }} )
| snd_app_neut : 
  `( {{ ⟦ B ⟧ ρ ↦ ⇑ a (fst m) ↘ b }} ->
     {{ π₂ ⇑ (Σ a ρ B) m ↘ ⇑ b (snd m) }} )
where "'π₂' n '↘' r" := (snd_app n r) (in custom judg)
with eval_eqrec : domain -> exp -> exp -> domain -> domain -> domain -> env -> domain -> Prop :=
| eval_eqrec_refl :
  `( {{ ⟦ BR ⟧ ρ ↦ n ↘ br }} ->
     {{ eqrec refl n as Eq a m1 m2 ⟦return B | refl -> BR end⟧ ρ ↘ br }} )
| eval_eqrec_neut :
  `( {{ ⟦ B ⟧ ρ ↦ m1 ↦ m2 ↦ ⇑ c n ↘ b }} ->
     {{ eqrec ⇑ c n as Eq a m1 m2 ⟦return B | refl -> BR end⟧ ρ ↘ ⇑ b (eqrec n under ρ as Eq a m1 m2 return B | refl -> BR end) }} )
where "'eqrec' n 'as' 'Eq' a m1 m2 '⟦return' B | 'refl' -> BR 'end⟧' ρ '↘' r" := (eval_eqrec a B BR m1 m2 n ρ r) (in custom judg)
with eval_sub : sub -> env -> env -> Prop :=
| eval_sub_id :
  `( {{ ⟦ Id ⟧s ρ ↘ ρ }} )
| eval_sub_weaken :
  `( {{ ⟦ Wk ⟧s ρ ↘ ρ ↯ }} )
| eval_sub_extend :
  `( {{ ⟦ σ ⟧s ρ ↘ ρσ }} ->
     {{ ⟦ M ⟧ ρ ↘ m }} ->
     {{ ⟦ σ ,, M ⟧s ρ ↘ ρσ ↦ m }} )
| eval_sub_compose :
  `( {{ ⟦ τ ⟧s ρ ↘ ρτ }} ->
     {{ ⟦ σ ⟧s ρτ ↘ ρτσ }} ->
     {{ ⟦ σ ∘ τ ⟧s ρ ↘ ρτσ }} )
where "'⟦' σ '⟧s' ρ '↘' ρσ" := (eval_sub σ ρ ρσ) (in custom judg)
.

Scheme eval_exp_mut_ind := Induction for eval_exp Sort Prop
with eval_natrec_mut_ind := Induction for eval_natrec Sort Prop
with eval_app_mut_ind := Induction for eval_app Sort Prop
with eval_eqrec_mut_ind := Induction for eval_eqrec Sort Prop
with eval_sub_mut_ind := Induction for eval_sub Sort Prop.
Combined Scheme eval_mut_ind from
  eval_exp_mut_ind,
  eval_natrec_mut_ind,
  eval_app_mut_ind,
  eval_eqrec_mut_ind,
  eval_sub_mut_ind.

#[export]
Hint Constructors eval_exp eval_natrec eval_app eval_eqrec eval_sub : mctt.
