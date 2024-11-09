From Coq Require Import Morphisms_Relations.

From Mcltt Require Import LibTactics.
From Mcltt.Core Require Import Base.
From Mcltt.Core.Completeness Require Import ContextCases LogicalRelation SubstitutionCases SubtypingCases TermStructureCases UniverseCases VariableCases.
From Mcltt.Core.Semantic Require Import Realizability.
Import Domain_Notations.

Lemma rel_exp_eq_cong : forall {Γ i A A' M1 M1' M2 M2'},
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ M1 ≈ M1' : A }} ->
    {{ Γ ⊨ M2 ≈ M2' : A }} ->
    {{ Γ ⊨ Eq A M1 M2 ≈ Eq A' M1' M2' : Type@i }}.
Proof.
  intros * [env_relΓ]%rel_exp_of_typ_inversion1 HM1 HM2.
  destruct_conjs.
  invert_rel_exp HM1.
  invert_rel_exp HM2.
  eexists_rel_exp_of_typ.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  invert_rel_typ_body.
  unfold per_univ in *.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  econstructor; mauto 3.
  eexists.
  per_univ_elem_econstructor; mauto 3; try solve_refl.
Qed.
#[export]
Hint Resolve rel_exp_eq_cong : mcltt.

Lemma valid_exp_eq : forall {Γ i A M1 M2},
    {{ Γ ⊨ A : Type@i }} ->
    {{ Γ ⊨ M1 : A }} ->
    {{ Γ ⊨ M2 : A }} ->
    {{ Γ ⊨ Eq A M1 M2 : Type@i }}.
Proof. mauto. Qed.

#[export]
Hint Resolve valid_exp_eq : mcltt.

Lemma rel_exp_refl_cong : forall {Γ i A A' M M'},
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ M ≈ M' : A }} ->
    {{ Γ ⊨ refl A M ≈ refl A' M' : Eq A M M }}.
Proof.
  intros * [env_relΓ]%rel_exp_of_typ_inversion1 HM.
  destruct_conjs.
  invert_rel_exp HM.
  eexists_rel_exp.
  intros.
  saturate_refl_for env_relΓ.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_rel_typ.
  destruct_by_head rel_exp.
  unfold per_univ in *.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  eexists; split; econstructor; mauto 4.
  - per_univ_elem_econstructor; mauto 3;
      try (etransitivity; [| symmetry]; eassumption);
      try reflexivity.
  - econstructor; saturate_refl; mauto 3.
    symmetry; mauto 3.
Qed.
#[export]
Hint Resolve rel_exp_refl_cong : mcltt.

Lemma rel_exp_eq_sub : forall {Γ σ Δ i A M1 M2},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ ⊨ A : Type@i }} ->
    {{ Δ ⊨ M1 : A }} ->
    {{ Δ ⊨ M2 : A }} ->
    {{ Γ ⊨ (Eq A M1 M2)[σ] ≈ Eq A[σ] M1[σ] M2[σ] : Type@i }}.
Proof.
  intros * [env_relΓ [? [env_relΔ]]] HA HM1 HM2.
  destruct_conjs.
  invert_rel_exp_of_typ HA.
  invert_rel_exp HM1.
  invert_rel_exp HM2.
  eexists_rel_exp_of_typ.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  invert_rel_typ_body.
  unfold per_univ in *.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  econstructor; mauto.
  eexists.
  per_univ_elem_econstructor; mauto 3; try solve_refl.
Qed.

#[export]
Hint Resolve rel_exp_eq_sub : mcltt.

Lemma rel_exp_refl_sub : forall {Γ σ Δ i A M},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ ⊨ A : Type@i }} ->
    {{ Δ ⊨ M : A }} ->
    {{ Γ ⊨ (refl A M)[σ] ≈ refl A[σ] M[σ] : (Eq A M M)[σ] }}.
Proof.
  intros * [env_relΓ [? [env_relΔ]]] HA HM.
  destruct_conjs.
  invert_rel_exp_of_typ HA.
  invert_rel_exp HM.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  invert_rel_typ_body.
  unfold per_univ in *.
  destruct_conjs.
  handle_per_univ_elem_irrel.
  eexists; split; econstructor; mauto 3.
  - per_univ_elem_econstructor; mauto 3; try solve_refl.
  - saturate_refl.
    econstructor; intuition.
Qed.

#[export]
Hint Resolve rel_exp_refl_sub : mcltt.

Lemma rel_exp_eqrec_sub : forall {Γ σ Δ i A M1 M2 j B BR N},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ ⊨ A : Type@i }} ->
    {{ Δ ⊨ M1 : A }} ->
    {{ Δ ⊨ M2 : A }} ->
    {{ Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊨ B : Type@j }} ->
    {{ Δ, A ⊨ BR : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Δ ⊨ N : Eq A M1 M2 }} ->
    {{ Γ ⊨ eqrec N as Eq A M1 M2 return B | refl -> BR end[σ]
         ≈ eqrec N[σ] as Eq A[σ] M1[σ] M2[σ] return B[q (q (q σ))] | refl -> BR[q σ] end
        : B[σ,,M1[σ],,M2[σ],,N[σ]] }}.
Proof.
  intros * [env_relΓ [? [env_relΔ]]] HA HM1 HM2 HB HBR HN.
  destruct_conjs.
  assert {{ Δ, A ⊨ A[Wk] : Type@i }} as HA'.
  {
    assert {{ ⊨ Δ, A }} by mauto 3.
    assert {{ Δ, A ⊨s Wk : Δ }} by mauto 3.
    assert {{ Δ, A ⊨ A[Wk] : Type@i[Wk] }} by mauto 3.
    mauto 4.
  }
  assert {{ Δ, A, A[Wk] ⊨ Eq A[Wk∘Wk] #1 #0 : Type@i }} as HEq.
  {
    assert {{ ⊨ Δ, A }} by mauto 3.
    assert {{ Δ, A ⊨s Wk : Δ }} by mauto 3.
    assert {{ ⊨ Δ, A, A[Wk] }} by mauto 3.
    assert {{ Δ, A, A[Wk] ⊨s Wk : Δ, A }} by mauto 3.
    assert {{ Δ, A, A[Wk] ⊨s Wk∘Wk : Δ }} by mauto 3.
    assert {{ Δ, A, A[Wk] ⊨ A[Wk∘Wk] : Type@i[Wk∘Wk] }} by mauto 3.
    assert {{ Δ, A, A[Wk] ⊨ A[Wk∘Wk] : Type@i }} by mauto 4.
    assert {{ Δ, A, A[Wk] ⊨ A[Wk][Wk] ≈ A[Wk∘Wk] : Type@i[Wk∘Wk] }} by mauto 3.
    assert {{ Δ, A, A[Wk] ⊨ A[Wk][Wk] ≈ A[Wk∘Wk] : Type@i }} by mauto 4.
    assert {{ Δ, A, A[Wk] ⊨ #0 : A[Wk][Wk] }} by mauto 3.
    assert {{ Δ, A, A[Wk] ⊨ #0 : A[Wk∘Wk] }} by mauto 3.
    assert {{ Δ, A, A[Wk] ⊨ #1 : A[Wk][Wk] }} by mauto 3.
    assert {{ Δ, A, A[Wk] ⊨ #1 : A[Wk∘Wk] }} by mauto 3.
    mauto 4.
  }
  invert_rel_exp_of_typ HA.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relA]; shelve_unifiable; [eassumption |]).
  invert_rel_exp HM1.
  invert_rel_exp HM2.
  destruct_conjs.
  pose (env_relΔA := cons_per_ctx_env env_relΔ elem_relA).
  assert {{ EF Δ, A ≈ Δ, A ∈ per_ctx_env ↘ env_relΔA }} by (econstructor; mauto 3; try reflexivity; typeclasses eauto).
  invert_rel_exp_of_typ HA'.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relA']; shelve_unifiable; [eassumption |]).
  pose (env_relΔAA := cons_per_ctx_env env_relΔA elem_relA').
  assert {{ EF Δ, A, A[Wk] ≈ Δ, A, A[Wk] ∈ per_ctx_env ↘ env_relΔAA }} by (econstructor; mauto 3; try reflexivity; typeclasses eauto).
  invert_rel_exp_of_typ HEq.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relEq]; shelve_unifiable; [eassumption |]).
  pose (env_relΔAAEq := cons_per_ctx_env env_relΔAA elem_relEq).
  assert {{ EF Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ≈ Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ∈ per_ctx_env ↘ env_relΔAAEq }} by (econstructor; mauto 3; try reflexivity; typeclasses eauto).
  invert_rel_exp HN.
  eexists_rel_exp.
  intros.
  (* (on_all_hyp: destruct_rel_by_assumption env_relΓ). *)
  (* (on_all_hyp: destruct_rel_by_assumption env_relΔ). *)
  (* destruct_by_head rel_typ. *)
  (* destruct_by_head rel_exp. *)
  (* invert_rel_typ_body. *)
  (* assert {{ Dom ρ1 ↦ m1 ≈ ρ0 ↦ m0 ∈ env_relΔA }} by (unfold env_relΔA; mauto 3). *)
  (* (on_all_hyp: destruct_rel_by_assumption env_relΔA). *)
  (* simplify_evals. *)
  (* handle_per_univ_elem_irrel. *)
  (* assert {{ Dom ρ1 ↦ m1 ↦ m2 ≈ ρ0 ↦ m0 ↦ m3 ∈ env_relΔAA }} by (unfold env_relΔAA; unshelve eexists; intuition). *)
  (* (on_all_hyp: destruct_rel_by_assumption env_relΔAA). *)
  (* simplify_evals. *)
  (* match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H). *)
  (* handle_per_univ_elem_irrel. *)
  (* assert {{ Dom ρ1 ↦ m1 ↦ m2 ↦ m4 ≈ ρ0 ↦ m0 ↦ m3 ↦ m'2 ∈ env_relΔAAEq }} as HrelΔAAEq by (apply_relation_equivalence; unshelve eexists; intuition). *)
  (* apply_relation_equivalence. *)
  (* (on_all_hyp: fun H => directed destruct (H _ _ HrelΔAAEq) as []). *)
  (* destruct_conjs. *)
  (* match_by_head per_eq ltac:(fun H => destruct H). *)

(** We need some insane number of steps here.
    It might be better to do some optimization first. *)
Admitted.
#[export]
Hint Resolve rel_exp_eqrec_sub : mcltt.

Lemma rel_exp_eqrec_cong : forall {Γ i A A' M1 M1' M2 M2' j B B' BR BR' N N'},
    {{ Γ ⊨ A : Type@i }} ->
    {{ Γ ⊨ M1 : A }} ->
    {{ Γ ⊨ M2 : A }} ->
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ M1 ≈ M1' : A }} ->
    {{ Γ ⊨ M2 ≈ M2' : A }} ->
    {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊨ B ≈ B' : Type@j }} ->
    {{ Γ, A ⊨ BR ≈ BR' : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Γ ⊨ N ≈ N' : Eq A M1 M2 }} ->
    {{ Γ ⊨ eqrec N as Eq A M1 M2 return B | refl -> BR end
         ≈ eqrec N' as Eq A' M1' M2' return B' | refl -> BR' end
        : B[Id,,M1,,M2,,N] }}.
Proof.
Admitted.
#[export]
Hint Resolve rel_exp_eqrec_cong : mcltt.

Lemma rel_exp_eqrec_beta : forall {Γ i A M j B BR},
    {{ Γ ⊨ A : Type@i }} ->
    {{ Γ ⊨ M : A }} ->
    {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊨ B : Type@j }} ->
    {{ Γ, A ⊨ BR : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Γ ⊨ eqrec refl A M as Eq A M M return B | refl -> BR end
         ≈ BR[Id,,M]
        : B[Id,,M,,M,,refl A M] }}.
Proof.
Admitted.
#[export]
Hint Resolve rel_exp_eqrec_beta : mcltt.
