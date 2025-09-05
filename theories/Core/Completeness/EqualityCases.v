From Coq Require Import Morphisms_Relations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import ContextCases LogicalRelation SubstitutionCases SubtypingCases TermStructureCases UniverseCases VariableCases.
From Mctt.Core.Semantic Require Import Realizability.
Import Domain_Notations.

Lemma rel_exp_eq_cong : forall {Γ i A A' M1 M1' M2 M2'},
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ M1 ≈ M1' : A }} ->
    {{ Γ ⊨ M2 ≈ M2' : A }} ->
    {{ Γ ⊨ Eq A M1 M2 ≈ Eq A' M1' M2' : Type@i }}.
Proof.
  intros * HA HM1 HM2.
  invert_rel_exp_of_typ HA env_relΓ.
  invert_rel_exp HM1.
  invert_rel_exp HM2.
  eexists_rel_exp_of_typ.
  destruct_rel_by_assumption env_relΓ H2.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  destruct_by_head per_univ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  econstructor; mauto 3.
  eexists.
  per_univ_elem_econstructor; mauto 3; try solve_refl.
Qed.
#[export]
Hint Resolve rel_exp_eq_cong : mctt.

Lemma valid_exp_eq : forall {Γ i A M1 M2},
    {{ Γ ⊨ A : Type@i }} ->
    {{ Γ ⊨ M1 : A }} ->
    {{ Γ ⊨ M2 : A }} ->
    {{ Γ ⊨ Eq A M1 M2 : Type@i }}.
Proof. mauto. Qed.

#[export]
Hint Resolve valid_exp_eq : mctt.

Lemma rel_exp_refl_cong : forall {Γ i A A' M M'},
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ M ≈ M' : A }} ->
    {{ Γ ⊨ refl A M ≈ refl A' M' : Eq A M M }}.
Proof.
  intros * HA HM.
  invert_rel_exp_of_typ HA env_relΓ.
  invert_rel_exp HM.
  eexists_rel_exp.
  intros.
  saturate_refl_for env_relΓ.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_rel_typ.
  destruct_by_head per_univ.
  invert_rel_typ_body_nouip.
  destruct_by_head rel_exp.
  simplify_evals.
  eexists; split; econstructor; mauto 4.
  - per_univ_elem_econstructor; mauto 3;
      try (etransitivity; [| symmetry]; eassumption).
    solve_refl.
  - econstructor; saturate_refl; mauto 3.
    symmetry; mauto 3.
Qed.
#[export]
Hint Resolve rel_exp_refl_cong : mctt.

Lemma rel_exp_eq_sub : forall {Γ σ Δ i A M1 M2},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ ⊨ A : Type@i }} ->
    {{ Δ ⊨ M1 : A }} ->
    {{ Δ ⊨ M2 : A }} ->
    {{ Γ ⊨ (Eq A M1 M2)[σ] ≈ Eq A[σ] M1[σ] M2[σ] : Type@i }}.
Proof.
  intros * [env_relΓ [? [env_relΔ []]]] HA HM1 HM2.
  invert_rel_exp_of_typ HA.
  invert_rel_exp HM1.
  invert_rel_exp HM2.
  eexists_rel_exp_of_typ.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  destruct_by_head per_univ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  econstructor; mauto.
  eexists.
  per_univ_elem_econstructor; mauto 3; try solve_refl.
Qed.

#[export]
Hint Resolve rel_exp_eq_sub : mctt.

Lemma rel_exp_refl_sub : forall {Γ σ Δ i A M},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ ⊨ A : Type@i }} ->
    {{ Δ ⊨ M : A }} ->
    {{ Γ ⊨ (refl A M)[σ] ≈ refl A[σ] M[σ] : (Eq A M M)[σ] }}.
Proof.
  intros * [env_relΓ [? [env_relΔ []]]] HA HM.
  invert_rel_exp_of_typ HA.
  invert_rel_exp HM.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  destruct_by_head per_univ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  eexists; split; econstructor; mauto 3.
  - per_univ_elem_econstructor; mauto 3; try solve_refl.
  - saturate_refl.
    econstructor; intuition.
Qed.

#[export]
Hint Resolve rel_exp_refl_sub : mctt.

Lemma rel_exp_eqrec_wf_Awk : forall {Γ i A},
    {{ Γ ⊨ A : Type@i }} ->
    {{ Γ, A ⊨ A[Wk] : Type@i }}.
Proof.
  intros * HA.
  assert {{ ⊨ Γ, A }} by mauto 3.
  assert {{ Γ, A ⊨s Wk : Γ }} by mauto 3.
  assert {{ Γ, A ⊨ A[Wk] : Type@i[Wk] }} by mauto 3.
  mauto 4.
Qed.

Lemma rel_exp_eqrec_wf_EqAwkwk : forall {Γ i A},
    {{ Γ ⊨ A : Type@i }} ->
    {{ Γ, A, A[Wk] ⊨ Eq A[Wk∘Wk] #1 #0 : Type@i }}.
Proof.
  intros * HA.
  apply rel_exp_eqrec_wf_Awk in HA as HA'.
  assert {{ ⊨ Γ, A }} by mauto 3.
  assert {{ Γ, A ⊨s Wk : Γ }} by mauto 3.
  assert {{ ⊨ Γ, A, A[Wk] }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊨s Wk : Γ, A }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊨s Wk∘Wk : Γ }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊨ A[Wk∘Wk] : Type@i[Wk∘Wk] }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊨ A[Wk∘Wk] : Type@i }} by mauto 4.
  assert {{ Γ, A, A[Wk] ⊨ A[Wk∘Wk] ≈ A[Wk][Wk] : Type@i[Wk∘Wk] }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊨ A[Wk][Wk] ≈ A[Wk∘Wk] : Type@i[Wk∘Wk] }} by mauto 2.
  assert {{ Γ, A, A[Wk] ⊨ A[Wk][Wk] ≈ A[Wk∘Wk] : Type@i }} by mauto 4.
  assert {{ Γ, A, A[Wk] ⊨ #0 : A[Wk][Wk] }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊨ #0 : A[Wk∘Wk] }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊨ #1 : A[Wk][Wk] }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊨ #1 : A[Wk∘Wk] }} by mauto 3.
  mauto 3.
Qed.

Lemma eval_eqrec_relΓA_helper : forall {Γ env_relΓ i A},
  {{ DF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ }} ->
  {{ Γ ⊨ A : Type@i }} ->
  exists env_relΓA,
   {{ EF Γ, A ≈ Γ, A ∈ per_ctx_env ↘ env_relΓA }}
   /\
  (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) R a a' m1 m1',
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ Dom m1 ≈ m1' ∈ R }} ->
    {{ Dom ρ ↦ m1 ≈ ρ' ↦ m1' ∈ env_relΓA }}).
Proof.
  intros * HΓ HA.
  invert_rel_exp_of_typ HA.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relA]; shelve_unifiable; [eassumption |]).
  pose (env_relΓA := cons_per_ctx_env env_relΓ elem_relA).
  assert {{ EF Γ, A ≈ Γ, A ∈ per_ctx_env ↘ env_relΓA }} by (econstructor; mauto 3; try reflexivity; typeclasses eauto).
  eexists env_relΓA; split; auto. intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  simplify_evals.
  handle_per_univ_elem_irrel.
  unfold env_relΓA; mauto 3.
Qed.

Lemma eval_eqrec_relΓAAEq_helper : forall {Γ env_relΓ i A},
  {{ DF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ }} ->
  {{ Γ ⊨ A : Type@i }} ->
  exists env_relΓAAEq,
   {{ EF Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ≈ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ∈ per_ctx_env ↘ env_relΓAAEq }}
   /\
  (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) R a a' m1 m1' m2 m2' n n',
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ Dom m1 ≈ m1' ∈ R }} ->
    {{ Dom m2 ≈ m2' ∈ R }} ->
    {{ Dom n ≈ n' ∈ per_eq R m1 m2' }} ->
    {{ Dom ρ ↦ m1 ↦ m2 ↦ n ≈ ρ' ↦ m1' ↦ m2' ↦ n' ∈ env_relΓAAEq }}).
Proof.
  intros * HΓ HA.
  destruct_conjs.
  apply rel_exp_eqrec_wf_Awk in HA as HA'.
  apply rel_exp_eqrec_wf_EqAwkwk in HA as HEq.
  eapply eval_eqrec_relΓA_helper in HA as HΓA; eauto.
  destruct HΓA as [env_relΓA [equiv_ΓA HΓA]].
  eapply @eval_eqrec_relΓA_helper with (A:={{{ A[Wk] }}}) in equiv_ΓA as HΓAA; eauto.
  destruct HΓAA as [env_relΓAA [equiv_ΓAA HΓAA]].
  eapply @eval_eqrec_relΓA_helper with (A:={{{ Eq A[Wk∘Wk] #1 #0 }}}) in equiv_ΓAA as HΓAAEq; eauto.
  destruct HΓAAEq as [env_relΓAAEq [equiv_ΓAAEq HΓAAEq]].
  eexists; intuition.
  assert {{ Dom ρ ↦ m1 ≈ ρ' ↦ m1' ∈ env_relΓA }} by mauto 3.
  (on_all_hyp: destruct_rel_by_assumption env_relΓA).
  assert {{ Dom ρ ↦ m1 ↦ m2 ≈ ρ' ↦ m1' ↦ m2' ∈ env_relΓAA }} by mauto 3.
  eapply HΓAAEq with (a:= d{{{ Eq a m1 m2 }}}); mauto 4.
  mauto 3 using per_univ_elem_eq'.
Qed.

Lemma eval_eqrec_sub_neut : forall {Γ env_relΓ σ Δ env_relΔ i j A A' M1 M1' M2 M2' B B' BR BR' m m'},
    {{ DF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ }} ->
    {{ DF Δ ≈ Δ ∈ per_ctx_env ↘ env_relΔ }} ->
    {{ Δ ⊨ A : Type@i }} ->
    {{ Δ ⊨ A ≈ A' : Type@i }} ->
    {{ Δ ⊨ M1 ≈ M1' : A }} ->
    {{ Δ ⊨ M2 ≈ M2' : A }} ->
    {{ Δ, A ⊨ BR ≈ BR' : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊨ B ≈ B' : Type@j }} ->
    {{ Dom m ≈ m' ∈ per_bot }} ->
    (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) ρσ ρ'σ' a a' m1 m1' m2 m2',
        {{ ⟦ σ ⟧s ρ ↘ ρσ }} ->
        {{ ⟦ σ ⟧s ρ' ↘ ρ'σ' }} ->
        {{ Dom ρσ ≈ ρ'σ' ∈ env_relΔ }} ->
        {{ ⟦ A ⟧ ρσ ↘ a }} ->
        {{ ⟦ A' ⟧ ρ'σ' ↘ a' }} ->
        {{ ⟦ M1 ⟧ ρσ ↘ m1 }} ->
        {{ ⟦ M1' ⟧ ρ'σ' ↘ m1' }} ->
        {{ ⟦ M2 ⟧ ρσ ↘ m2 }} ->
        {{ ⟦ M2' ⟧ ρ'σ' ↘ m2' }} ->
        {{ Dom eqrec m under ρσ as Eq a m1 m2 return B | refl -> BR end ≈
               eqrec m' under ρ' as Eq a' m1' m2' return B'[q (q (q σ))] | refl -> BR'[q σ] end ∈ per_bot }}).
Proof.
  intros * equiv_Γ_Γ equiv_Δ_Δ HA HAA' HM1 HM2 HBR HB equiv_m_m'. intros.
  eapply eval_eqrec_relΓA_helper in HA as HΔA; eauto.
  destruct HΔA as [env_relΔA [equiv_ΔA HΔA]].
  eapply eval_eqrec_relΓAAEq_helper in HA as HΔAAEq; eauto.
  destruct HΔAAEq as [env_relΔAAEq [equiv_ΔAAEq HΔAAEq]].
  invert_rel_exp_of_typ HA.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relA]; shelve_unifiable; [eassumption |]).
  invert_rel_exp HM1.
  invert_rel_exp HM2.
  invert_rel_exp_of_typ HAA'.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relA']; shelve_unifiable; [eassumption |]).
  (on_all_hyp_rev: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  invert_rel_typ_body_nouip.
  destruct_by_head rel_exp.
  simplify_evals.
  intros s.
  assert {{ Dom ρσ ↦ ⇑! a s ≈ ρ'σ' ↦ ⇑! a' s ∈ env_relΔA }}.
  {
    eapply HΔA; eauto 3.
    eapply var_per_elem; eassumption.
  }
  invert_rel_exp HBR.
  (on_all_hyp_rev: destruct_rel_by_assumption env_relΔA).
  destruct_by_head rel_typ.
  invert_rel_typ_body.
  destruct_by_head rel_exp.
  assert {{ Dom ρσ ↦ ⇑! a s ↦ ⇑! a s ↦ refl ⇑! a s ≈ ρ'σ' ↦ ⇑! a' s ↦ ⇑! a' s ↦ refl ⇑! a' s ∈ env_relΔAAEq }}.
  {
    eapply HΔAAEq; eauto 3; try (eapply var_per_elem; eassumption).
    econstructor; eauto; eapply var_per_elem; eauto.
    - etransitivity; [|symmetry]; eassumption.
    - etransitivity; [symmetry|]; eassumption.
  }
  assert {{ Dom ρσ ↦ ⇑! a s ↦ ⇑! a (S s) ↦ ⇑! (Eq a (⇑! a s) (⇑! a (S s))) (S (S s)) ≈ ρ'σ' ↦ ⇑! a' s ↦ ⇑! a' (S s) ↦ ⇑! (Eq a' (⇑! a' s) (⇑! a' (S s))) (S (S s)) ∈ env_relΔAAEq }}. {
    eapply HΔAAEq; eauto 3; try (eapply var_per_elem; eassumption).
    econstructor.
    eapply var_per_bot; eassumption.
  }
  invert_rel_exp_of_typ HB.
  (on_all_hyp_rev: destruct_rel_by_assumption env_relΔAAEq).
  destruct_by_head per_univ.
  invert_rel_typ_body.
  (on_all_hyp: fun H => edestruct (per_univ_then_per_top_typ H s) as [? []]).
  (on_all_hyp: fun H => edestruct (per_univ_then_per_top_typ H (S (S (S s)))) as [? []]).
  functional_read_rewrite_clear.
  match goal with
  | _ : {{ ⟦ σ ⟧s ρ' ↘ ^?x }},
      _ : {{ ⟦ A ⟧ ^?x ↘ ^?ax }},
        _ : {{ ⟦ B ⟧ ρσ ↦ ⇑! a s ↦ ⇑! a s ↦ refl ⇑! a s ↘ ^?bx }},
          _ : {{ ⟦ B' ⟧ ^?x ↦ ⇑! a' s ↦ ⇑! a' s ↦ refl ⇑! a' s ↘ ^?bx' }},
                  _ : {{ ⟦ BR ⟧ ρσ ↦ ⇑! a s ↘ ^?brx }},
                    _ : {{ ⟦ BR' ⟧ ^?x ↦ ⇑! a' s ↘ ^?brx' }} |- _ =>
      rename x into ρ'σ;
      rename ax into a0;
      rename bx into brefl;
      rename bx' into brefl';
      rename brx into br;
      rename brx' into br'
  end.
  assert {{ Dom ⇓ a m1 ≈ ⇓ a' m1' ∈ per_top }} as Htop1 by eauto using per_elem_then_per_top.
  assert {{ Dom ⇓ a m2 ≈ ⇓ a' m2' ∈ per_top }} as Htop2 by eauto using per_elem_then_per_top.
  assert {{ Dom ⇓ brefl br ≈ ⇓ brefl' br' ∈ per_top }} as Htopbr by eauto using per_elem_then_per_top.
  destruct (Htop1 s).
  destruct (Htop2 s).
  destruct (Htopbr (S s)).
  destruct (equiv_m_m' s).
  destruct_conjs.
  eexists; split.
  - eapply read_ne_eqrec; mauto 3.
  - eapply read_ne_eqrec; mauto 3;
      repeat (econstructor; try eassumption).
Qed.

(* eval_eqrec_neut has name clashes with the constructor name *)
Corollary eval_eqrec_neut_same_ctx : forall {Γ env_relΓ i j A A' M1 M1' M2 M2' B B' BR BR' m m'},
    {{ DF Γ ≈ Γ ∈ per_ctx_env ↘ env_relΓ }} ->
    {{ Γ ⊨ A : Type@i }} ->
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ ⊨ M1 ≈ M1' : A }} ->
    {{ Γ ⊨ M2 ≈ M2' : A }} ->
    {{ Γ, A ⊨ BR ≈ BR' : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊨ B ≈ B' : Type@j }} ->
    {{ Dom m ≈ m' ∈ per_bot }} ->
    (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) a a' m1 m1' m2 m2',
        {{ ⟦ A ⟧ ρ ↘ a }} ->
        {{ ⟦ A' ⟧ ρ' ↘ a' }} ->
        {{ ⟦ M1 ⟧ ρ ↘ m1 }} ->
        {{ ⟦ M1' ⟧ ρ' ↘ m1' }} ->
        {{ ⟦ M2 ⟧ ρ ↘ m2 }} ->
        {{ ⟦ M2' ⟧ ρ' ↘ m2' }} ->
        {{ Dom eqrec m under ρ as Eq a m1 m2 return B | refl -> BR end ≈
               eqrec m' under ρ' as Eq a' m1' m2' return B' | refl -> BR' end ∈ per_bot }}).
Proof.
  intros.
  assert {{ Dom eqrec m under ρ as Eq a m1 m2 return B | refl -> BR end ≈
                eqrec m' under ρ' as Eq a' m1' m2' return B'[q (q (q Id))] | refl -> BR'[q Id] end ∈ per_bot }}
    by (eapply (@eval_eqrec_sub_neut _ _ _ _ _ _ _ _ _ M1 M1' M2 M2'); mauto 3).
  etransitivity; [eassumption |].
  intros s.
  match_by_head per_bot ltac:(fun H => specialize (H s) as [? []]).
  eexists; split; [eassumption |].
  dir_inversion_by_head read_ne; subst.
  simplify_evals.
  mauto 4.
Qed.

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
  intros * [env_relΓ [? [env_relΔ []]]] HA HM1 HM2 HB HBR HN.
  eapply eval_eqrec_relΓA_helper in HA as HA'; eauto.
  destruct HA' as [env_relΔA [equiv_ΔA HΔA]].
  eapply eval_eqrec_relΓAAEq_helper in HA as HA'; eauto.
  destruct HA' as [env_relΔAAEq [equiv_ΔAAEq HΔAAEq]].
  pose proof (HA' := HA).
  invert_rel_exp_of_typ HA'.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relA]; shelve_unifiable; [eassumption |]).
  pose proof (HM1' := HM1).
  pose proof (HM2' := HM2).
  pose proof (HBR' := HBR).
  invert_rel_exp HM1'.
  invert_rel_exp HM2'.
  invert_rel_exp HN.
  invert_rel_exp_of_typ HB.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relB]; shelve_unifiable; [eassumption |]).
  invert_rel_exp HBR'.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  invert_rel_typ_body_nouip.
  destruct_by_head rel_exp.
  simplify_evals.
  match_by_head per_eq ltac:(fun H => destruct H);
  match goal with
    | _: {{ ⟦ σ ⟧s ρ ↘ ^?ρσ0 }},
        _: {{ ⟦ σ ⟧s ρ' ↘ ^?ρσ0' }},
          _: {{ ⟦ M1 ⟧ ^?ρσ0' ↘ ^?m10' }},
            _: {{ ⟦ M2 ⟧ ^?ρσ0' ↘ ^?m20' }} |- _ =>
      rename ρσ0 into ρσ;
      rename ρσ0' into ρ'σ;
      rename m10' into m1';
      rename m20' into m2'
    end.
  - assert {{ Dom ρσ ↦ n ≈ ρ'σ ↦ n' ∈ env_relΔA }} by mauto 3.
    assert {{ Dom ρσ ↦ m1 ≈ ρ'σ ↦ m1' ∈ env_relΔA }} by mauto 3.
    handle_per_ctx_env_irrel.
    (on_all_hyp: destruct_rel_by_assumption env_relΔA).
    assert {{ Dom ρσ ↦ m1 ↦ m2 ↦ refl n ≈ ρ'σ ↦ m1' ↦ m2' ↦ refl n' ∈ env_relΔAAEq }} by mauto 3.
    assert {{ Dom ρσ ↦ n ↦ n ↦ refl n ≈ ρσ ↦ m1 ↦ m2 ↦ refl n ∈ env_relΔAAEq }}.
    {
      assert (elem_relA ρσ ρ'σ H10 n m2) by (do 2 (etransitivity; [|symmetry]; eauto)).
      eapply HΔAAEq; mauto 3.
      - etransitivity; [|symmetry]; eassumption.
      - symmetry; assumption.
      - econstructor; mauto 3; (etransitivity; [|symmetry]; eassumption).
    }
    (on_all_hyp: destruct_rel_by_assumption env_relΔAAEq).
    destruct_by_head rel_typ.
    invert_rel_typ_body_nouip.
    destruct_by_head rel_exp.
    eexists; split.
    + match goal with
      | _: {{ ⟦ B ⟧ ρσ ↦ m1 ↦ m2 ↦ refl n ↘ ^?b0 }},
          _: {{ ⟦ B ⟧ ρ'σ ↦ m1' ↦ m2' ↦ refl n' ↘ ^?b0'  }} |- _ =>
        eapply mk_rel_mod_eval with (a:=b0) (a':=b0')
      end; try solve [do 2 (econstructor; mauto)].
      mauto 3.
    + do 2 (econstructor; mauto).
  - assert {{ Dom ρσ ↦ m1 ≈ ρ'σ ↦ m1' ∈ env_relΔA }} by mauto 3.
    (on_all_hyp: destruct_rel_by_assumption env_relΔA).
    (on_all_hyp: fun H => directed invert_per_univ_elem_nouip H).
    handle_per_univ_elem_irrel.
    assert {{ Dom ρσ ↦ m1 ↦ m2 ↦ ⇑ a1 n ≈ ρ'σ ↦ m1' ↦ m2' ↦ ⇑ a' n' ∈ env_relΔAAEq }} by mauto 3.
    (on_all_hyp: destruct_rel_by_assumption env_relΔAAEq).
    destruct_by_head rel_typ.
    invert_rel_typ_body_nouip.
    destruct_by_head rel_exp.
    eexists; split.
    + do 4 (econstructor; mauto 3).
    + econstructor; mauto.
      * econstructor; mauto.
        eapply eval_eqrec_neut.
        do 5 (econstructor; mauto 3).
      * eapply per_bot_then_per_elem; mauto.
        rewrite_relation_equivalence_right.
        eapply (@eval_eqrec_sub_neut Γ _ _ Δ);
          revgoals; unshelve mauto 3; assumption.
Qed.

#[export]
Hint Resolve rel_exp_eqrec_sub : mctt.

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
  intros * HA _ _ HAA' HM1M1' HM2M2' HBB' HBRBR' HNN'.
  invert_rel_exp_of_typ HAA' env_relΓ.
  assert (HB: {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊨ B : Type@j }} ) by (eapply rel_exp_trans; [| eapply rel_exp_sym]; eassumption).
  assert (HN: {{ Γ ⊨ N : Eq A M1 M2 }} ) by (eapply rel_exp_trans; [| eapply rel_exp_sym]; eassumption).
  eapply eval_eqrec_relΓA_helper in HA as HA'; eauto.
  destruct HA' as [env_relΓA [equiv_ΓA HΓA]].
  eapply eval_eqrec_relΓAAEq_helper in HA as HA'; eauto.
  destruct HA' as [env_relΓAAEq [equiv_ΓAAEq HΓAAEq]].
  invert_rel_exp_of_typ HA.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relA]; shelve_unifiable; [eassumption |]).
  invert_rel_exp HM1M1'.
  invert_rel_exp HM2M2'.
  invert_rel_exp HN.
  invert_rel_exp HNN'.
  invert_rel_exp_of_typ HB.
  invert_rel_exp_of_typ HBB'.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relB]; shelve_unifiable; [eassumption |]).
  invert_rel_exp HBRBR'.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body_nouip.
  destruct_by_head rel_exp.
  simplify_evals.
  match_by_head per_eq ltac:(fun H => inversion H; subst; clear H).
  - (* m1', m2', n' for M1, M2, N evaluated under ρ'*)
    (* m1'', m2'', n'' for M1', M2', N' evaluated under ρ'*)
    match goal with
    | _: (env_relΓ ?ρ0 ?ρ0'),
        _: {{ ⟦ A ⟧ ^?ρ0' ↘ ^?a0' }},
          _: {{ ⟦ M1 ⟧ ^?ρ0' ↘ ^?m10 }},
            _: {{ ⟦ M2 ⟧ ^?ρ0' ↘ ^?m20 }},
              _: {{ ⟦ M1' ⟧ ^?ρ0' ↘ ^?m10' }},
                _: {{ ⟦ M2' ⟧ ^?ρ0' ↘ ^?m20' }},
                  _: {{ ⟦ N ⟧ ^?ρ0 ↘ refl ^?n10 }},
                    _: {{ ⟦ N ⟧ ^?ρ0' ↘ refl ^?n10' }},
                      _: {{ ⟦ N' ⟧ ^?ρ0' ↘ refl ^?n10'' }} |- _ => 
      rename ρ0' into ρ';
      rename a0' into a';
      rename m10 into m1';
      rename m20 into m2';
      rename m10' into m1'';
      rename m20' into m2'';
      rename n10'' into n'';
      rename n10' into n';
      rename n10 into n
    end.
    assert {{ Dom ρ ↦ n ≈ ρ' ↦ n'' ∈ env_relΓA }} by mauto 3.
    handle_per_ctx_env_irrel.
    (on_all_hyp: destruct_rel_by_assumption env_relΓA).
    simplify_evals.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem_nouip H).
    handle_per_univ_elem_irrel.
    assert {{ Dom ρ ↦ m1 ↦ m2 ↦ refl n ≈ ρ' ↦ m1' ↦ m2' ↦ refl n' ∈ env_relΓAAEq }} by mauto 3.
    assert {{ Dom ρ ↦ n ↦ n ↦ refl n ≈ ρ ↦ m1 ↦ m2 ↦ refl n ∈ env_relΓAAEq }}.
    {
      eapply HΓAAEq; mauto 3.
      - etransitivity; [|symmetry]; eassumption.
      - symmetry; assumption.
      - do 3 (etransitivity; [|symmetry]; eauto).
      - econstructor; mauto 3; try (etransitivity; [|symmetry]; eassumption).
        do 3 (etransitivity; [|symmetry]; eauto).
    }
    (on_all_hyp: destruct_rel_by_assumption env_relΓAAEq).
    destruct_by_head rel_typ.
    destruct_by_head per_univ.
    invert_rel_typ_body_nouip.
    destruct_by_head rel_exp.
    eexists; split.
    + match goal with
      | _: {{ ⟦ B ⟧ ρ ↦ m1 ↦ m2 ↦ refl n ↘ ^?b0 }},
          _: {{ ⟦ B ⟧ ρ' ↦ m1' ↦ m2' ↦ refl n' ↘ ^?b0'  }} |- _ =>
        eapply mk_rel_mod_eval with (a:=b0) (a':=b0')
      end; try solve [do 2 (econstructor; mauto)].
      mauto 3.
    + econstructor; mauto 3.
  - match goal with
    | _: (env_relΓ ?ρ0 ?ρ0'),
        _: {{ ⟦ A ⟧ ^?ρ0' ↘ ^?a_0' }},
          _: {{ ⟦ A' ⟧ ^?ρ0' ↘ ^?a_0'' }},
          _: {{ ⟦ M1 ⟧ ^?ρ0' ↘ ^?m10 }},
            _: {{ ⟦ M2 ⟧ ^?ρ0' ↘ ^?m20 }},
              _: {{ ⟦ M1' ⟧ ^?ρ0' ↘ ^?m10' }},
                _: {{ ⟦ M2' ⟧ ^?ρ0' ↘ ^?m20' }},
                  _: {{ ⟦ N ⟧ ^?ρ0 ↘ ⇑ ^?an0' ^?n10 }},
                    _: {{ ⟦ N ⟧ ^?ρ0' ↘ ⇑ ^?an1' ^?n10' }},
                      _: {{ ⟦ N' ⟧ ^?ρ0' ↘ ⇑ ^?an2' ^?n10'' }}
                      |- _ =>
      rename ρ0' into ρ';
      rename m10 into m1';
      rename m20 into m2';
      rename m10' into m1'';
      rename m20' into m2'';
      rename an2' into an''; rename n10'' into n'';
      rename an1' into an'; rename n10' into n';
      rename an0' into an; rename n10 into n;
      rename a_0'' into a'';
      rename a_0' into a'''
    end; rename a''' into a'.
    assert {{ Dom ρ ↦ m1 ≈ ρ' ↦ m1' ∈ env_relΓA }} by mauto 3.
    assert {{ Dom ρ ↦ m1 ≈ ρ' ↦ m1'' ∈ env_relΓA }} by mauto 3.
    (on_all_hyp: destruct_rel_by_assumption env_relΓA).
    assert {{ Dom ρ ↦ m1 ↦ m2 ↦ ⇑ an n ≈ ρ' ↦ m1' ↦ m2' ↦ ⇑ an' n' ∈ env_relΓAAEq }} by mauto 3.
    assert {{ Dom ρ ↦ m1 ↦ m2 ↦ ⇑ an n ≈ ρ' ↦ m1'' ↦ m2'' ↦ ⇑ an'' n'' ∈ env_relΓAAEq }} by mauto 3.
    (on_all_hyp: destruct_rel_by_assumption env_relΓAAEq).
    destruct_by_head rel_typ.
    destruct_by_head per_univ.
    invert_rel_typ_body_nouip.
    destruct_by_head rel_exp.
    simplify_evals.
    eexists; split.
    + do 3 (econstructor; mauto 3).
    + econstructor; mauto.
      eapply per_bot_then_per_elem; mauto.
      handle_per_univ_elem_irrel.
      eapply (@eval_eqrec_neut_same_ctx Γ _ _);
        revgoals; unshelve mauto 3; try eassumption;
        try (unshelve (eapply rel_exp_cumu, rel_exp_of_typ; mauto 3); eassumption);
        econstructor; mauto 3.
Qed.

#[export]
Hint Resolve rel_exp_eqrec_cong : mctt.

Lemma rel_exp_eqrec_beta : forall {Γ i A M j B BR},
    {{ Γ ⊨ A : Type@i }} ->
    {{ Γ ⊨ M : A }} ->
    {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊨ B : Type@j }} ->
    {{ Γ, A ⊨ BR : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Γ ⊨ eqrec refl A M as Eq A M M return B | refl -> BR end
         ≈ BR[Id,,M]
        : B[Id,,M,,M,,refl A M] }}.
Proof.
  (* Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊨ B : Type@j is not necessary *)
  intros * HA HM _ HBR.
  invert_rel_exp_of_typ HA env_relΓ.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relA]; shelve_unifiable; [eassumption |]).
  invert_rel_exp HM.
  pose (env_relΓA := cons_per_ctx_env env_relΓ elem_relA).
  assert {{ EF Γ, A ≈ Γ, A ∈ per_ctx_env ↘ env_relΓA }} by (econstructor; mauto 3; try reflexivity; typeclasses eauto).
  invert_rel_exp HBR.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  invert_rel_typ_body.
  assert {{ Dom ρ ↦ m ≈ ρ' ↦ m' ∈ env_relΓA }} by (unfold env_relΓA; mauto 3).
  (on_all_hyp: destruct_rel_by_assumption env_relΓA).
  destruct_by_head rel_typ.
  invert_rel_typ_body_nouip.
  destruct_by_head rel_exp.
  assert ({{ ⟦ B[Id,,M,,M,,refl A M] ⟧ ρ ↘ m0 }}) by (econstructor; mauto).
  assert ({{ ⟦ B[Id,,M,,M,,refl A M] ⟧ ρ' ↘ m2 }}) by (econstructor; mauto).
  eexists; split; mauto 3. econstructor; mauto 3.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve rel_exp_eqrec_beta : mctt.
