From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export Definitions.
Import Syntax_Notations.

Reserved Notation "⊢ M ≈≈ M'" 
  (in custom judg at level 80, M custom exp, M' custom exp, no associativity). 
Reserved Notation "⊢s σ ≈≈ σ'" 
  (in custom judg at level 80, σ custom exp, σ' custom exp, no associativity). 

Generalizable All Variables.

Inductive exp_weak_cong : exp -> exp -> Prop :=
| exp_wcong_type :
  `( {{ ⊢ Type@i ≈≈ Type@i }} )
| exp_wcong_nat :
  {{ ⊢ ℕ ≈≈ ℕ }}
| exp_wcong_zero : 
  {{ ⊢ zero ≈≈ zero }}
| exp_wcong_succ :
  `( {{ ⊢ M ≈≈ M' }} ->
     {{ ⊢ succ M ≈≈ succ M'}} )
| exp_wcong_rec : 
  `( {{ ⊢ A ≈≈ A' }} ->
     {{ ⊢ MZ ≈≈ MZ' }} ->
     {{ ⊢ MS ≈≈ MS' }} ->
     {{ ⊢ M ≈≈ M' }} ->
     {{ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈≈ rec M' return A' | zero -> MZ' | succ -> MS' end  }} )
| exp_wcong_pi : 
  `( {{ ⊢ A ≈≈ A' }} ->
     {{ ⊢ B ≈≈ B' }} ->
     {{ ⊢ Π A B ≈≈ Π A' B' }} )
| exp_wcong_fn : 
  `( {{ ⊢ M ≈≈ M' }} ->
     {{ ⊢ λ A M ≈≈ λ A' M' }} )
| exp_wcong_app : 
  `( {{ ⊢ M ≈≈ M' }} ->
     {{ ⊢ N ≈≈ N' }} ->
     {{ ⊢ M N ≈≈ M' N' }} )
| exp_wcong_var : 
  `( {{ ⊢ #x ≈≈ #x }} )
| exp_wcong_sub : 
  `( {{ ⊢ M ≈≈ M' }} ->
     {{ ⊢s σ ≈≈ σ' }} ->
     {{ ⊢ M[σ] ≈≈ M'[σ'] }} )
where "⊢ M ≈≈ M'" := (exp_weak_cong M M') (in custom judg) : type_scope
with subst_weak_cong : sub -> sub -> Prop :=
| subst_wcong_id : 
  {{ ⊢s Id ≈≈ Id }}
| subst_wcong_weaken :
  `( {{ ⊢s Wk ≈≈ Wk }} )
| subst_wcong_compose :
  `( {{ ⊢s τ ≈≈ τ' }} ->
     {{ ⊢s σ ≈≈ σ' }} ->
     {{ ⊢s σ ∘ τ ≈≈ σ' ∘ τ' }} )
| subst_wcong_extend :
  `( {{ ⊢s σ ≈≈ σ' }} ->
     {{ ⊢ M ≈≈ M' }} ->
     {{ ⊢s (σ ,, M) ≈≈ (σ' ,, M') }} )
where "⊢s σ ≈≈ σ'" := (subst_weak_cong σ σ') (in custom judg) : type_scope.

#[export]
Hint Constructors exp_weak_cong subst_weak_cong : mctt.

Scheme exp_weak_cong_mut_ind := Induction for exp_weak_cong Sort Prop
with subst_weak_cong_mut_ind := Induction for subst_weak_cong Sort Prop.
Combined Scheme syntactic_wcong_mut_ind from
  exp_weak_cong_mut_ind,
  subst_weak_cong_mut_ind.

Reserved Notation "⊢nf M ≈≈ M'" 
  (in custom judg at level 80, M custom nf, M' custom nf, no associativity). 
Reserved Notation "⊢ne N ≈≈ N'" 
  (in custom judg at level 80, N custom nf, N' custom nf, no associativity). 

Inductive nf_weak_cong : nf -> nf -> Prop :=
| nf_wcong_type :
  `({{ ⊢nf Type@i ≈≈ Type@i }} )
| nf_wcong_nat :
  {{ ⊢nf ℕ ≈≈ ℕ }}
| nf_wcong_zero : 
  {{ ⊢nf zero ≈≈ zero }}
| nf_wcong_succ :
  `( {{ ⊢nf M ≈≈ M' }} ->
     {{ ⊢nf succ M ≈≈ succ M'}} )
| nf_wcong_pi : 
  `( {{ ⊢nf A ≈≈ A' }} ->
     {{ ⊢nf B ≈≈ B' }} ->
     {{ ⊢nf Π A B ≈≈ Π A' B' }} )
| nf_wcong_fn : 
  `( {{ ⊢nf M ≈≈ M' }} ->
     {{ ⊢nf λ A M ≈≈ λ A' M' }} )
| nf_wcong_neut : 
  `( {{ ⊢ne M ≈≈ M' }} ->
     {{ ⊢nf ⇑ M ≈≈ ⇑ M' }} )
where "⊢nf M ≈≈ M'" := (nf_weak_cong M M') (in custom judg) : type_scope
with ne_weak_cong : ne -> ne -> Prop :=
| ne_wcong_netrec : 
  `( {{ ⊢nf A ≈≈ A' }} ->
     {{ ⊢nf MZ ≈≈ MZ' }} ->
     {{ ⊢nf MS ≈≈ MS' }} ->
     {{ ⊢ne M ≈≈ M' }} ->
     {{ ⊢ne rec M return A | zero -> MZ | succ -> MS end ≈≈ rec M' return A' | zero -> MZ' | succ -> MS' end  }} )
| ne_wcong_app :
  `( {{ ⊢ne M ≈≈ M' }} ->
     {{ ⊢nf N ≈≈ N' }} ->
     {{ ⊢ne M N ≈≈ M' N' }} )
| ne_wcong_var : 
  `( {{ ⊢ne #x ≈≈ #x }} )
where "⊢ne N ≈≈ N'" := (ne_weak_cong N N') (in custom judg) : type_scope.

#[export]
Hint Constructors nf_weak_cong ne_weak_cong : mctt.

Scheme nf_weak_cong_mut_ind := Induction for nf_weak_cong Sort Prop
with ne_weak_cong_mut_ind := Induction for ne_weak_cong Sort Prop.
Combined Scheme normal_syntactic_wcong_mut_ind from
  nf_weak_cong_mut_ind,
  ne_weak_cong_mut_ind.