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
  intros * [env_relΓ]%rel_exp_of_typ_inversion1 HM1 HM2.
  destruct_conjs.
  invert_rel_exp HM1.
  invert_rel_exp HM2.
  eexists_rel_exp_of_typ.
  intros.
  destruct_rel_by_assumption env_relΓ H2. 
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  invert_rel_typ_body.
  unfold per_univ in *.
  deex. handle_per_univ_elem_irrel.
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
Hint Resolve rel_exp_refl_cong : mctt.

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
Hint Resolve rel_exp_eq_sub : mctt.

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
Hint Resolve rel_exp_refl_sub : mctt.

Lemma rel_exp_eqrec_wf_Awk : forall {Γ i A},
    {{ Γ ⊨ A : Type@i }} ->
    {{ Γ, A ⊨ A[Wk] : Type@i }}.
Proof.
  intros * [env_relΓ]%rel_exp_of_typ_inversion1. destruct_conjs.
  assert {{ ⊨ Γ, A }} by mauto.
  assert {{ Γ, A ⊨s Wk : Γ }} by mauto 3.
  assert {{ Γ, A ⊨ A[Wk] : Type@i[Wk] }} by mauto.
  mauto 4.
Qed.

Lemma rel_exp_eqrec_wf_EqAwkwk : forall {Γ i A},
    {{ Γ ⊨ A : Type@i }} ->
    {{ Γ, A, A[Wk] ⊨ Eq A[Wk∘Wk] #1 #0 : Type@i }}.
Proof.
  intros * HA.
  apply rel_exp_eqrec_wf_Awk in HA as HA'.
  apply rel_exp_of_typ_inversion1 in HA as [env_relΓ].
  destruct_conjs.
  assert {{ ⊨ Γ, A }} by mauto.
  assert {{ Γ, A ⊨s Wk : Γ }} by mauto 3.
  assert {{ ⊨ Γ, A, A[Wk] }} by mauto.
  assert {{ Γ, A, A[Wk] ⊨s Wk : Γ, A }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊨s Wk∘Wk : Γ }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊨ A[Wk∘Wk] : Type@i[Wk∘Wk] }} by mauto.
  assert {{ Γ, A, A[Wk] ⊨ A[Wk∘Wk] : Type@i }} by mauto 4.
  assert {{ Γ, A, A[Wk] ⊨ A[Wk][Wk] ≈ A[Wk∘Wk] : Type@i[Wk∘Wk] }} by mauto.
  assert {{ Γ, A, A[Wk] ⊨ A[Wk][Wk] ≈ A[Wk∘Wk] : Type@i }} by mauto 4.
  assert {{ Γ, A, A[Wk] ⊨ #0 : A[Wk][Wk] }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊨ #0 : A[Wk∘Wk] }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊨ #1 : A[Wk][Wk] }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊨ #1 : A[Wk∘Wk] }} by mauto 3.
  mauto 4.
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
  apply rel_exp_eqrec_wf_Awk in HA as HA'.
  apply rel_exp_eqrec_wf_EqAwkwk in HA as HEq.
  invert_rel_exp_of_typ HA.
  invert_rel_exp HM1.
  invert_rel_exp HM2.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relA]; shelve_unifiable; [eassumption |]).  
  invert_rel_exp_of_typ HAA'.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relAx]; shelve_unifiable; [eassumption |]).  
  gen ρσ ρ'σ'. intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  handle_per_univ_elem_irrel.
  pose (env_relΔA := cons_per_ctx_env env_relΔ elem_relA).
  assert {{ EF Δ, A ≈ Δ, A ∈ per_ctx_env ↘ env_relΔA }} by (econstructor; mauto 3; try reflexivity; typeclasses eauto).
  functional_read_rewrite_clear.
  intros s.
  assert {{ Dom ρσ ↦ ⇑! a s ≈ ρ'σ' ↦ ⇑! a' s ∈ env_relΔA }}. {
    unshelve eexists; intuition. simpl.
    eapply var_per_elem; eauto.
  }
  invert_rel_exp HBR.
  invert_rel_exp_of_typ HA'.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relA']; shelve_unifiable; [eassumption |]).
  gen ρσ ρ'σ'. intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΔA).
  invert_rel_typ_body.
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  handle_per_univ_elem_irrel.
  pose (env_relΔAA := cons_per_ctx_env env_relΔA elem_relA').
  assert {{ Dom ρσ ↦ ⇑! a s ↦ ⇑! a s ≈ ρ'σ' ↦ ⇑! a' s ↦ ⇑! a' s ∈ env_relΔAA}}. {
    unfold env_relΔAA; unshelve eexists; intuition.
    eapply var_per_elem; eauto. setoid_rewrite H19. eauto.
  }
  assert {{ Dom ρσ ↦ ⇑! a s ↦ ⇑! a (S s) ≈ ρ'σ' ↦ ⇑! a' s ↦ ⇑! a' (S s) ∈ env_relΔAA }}. {
    unfold env_relΔAA; unshelve eexists; intuition.
    eapply var_per_elem; eauto.
    setoid_rewrite H19. eauto.
  }
  assert {{ EF Δ, A, A[Wk] ≈ Δ, A, A[Wk] ∈ per_ctx_env ↘ env_relΔAA }} by (econstructor; mauto 3; try reflexivity; typeclasses eauto).
  invert_rel_exp_of_typ HEq. 
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relEq]; shelve_unifiable; [eassumption |]).
  gen ρσ ρ'σ'. intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΔAA).
  invert_rel_typ_body.
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  handle_per_univ_elem_irrel.
  rename ρσ0 into ρσ.
  pose (env_relΔAAEq := cons_per_ctx_env env_relΔAA elem_relEq).
  assert {{ Dom ρσ ↦ ⇑! a s ↦ ⇑! a s ↦ refl ⇑! a s ≈ ρ'σ' ↦ ⇑! a' s ↦ ⇑! a' s ↦ refl ⇑! a' s ∈ env_relΔAAEq }}.
  {
    unfold env_relΔAAEq; unshelve eexists; intuition.
    simpl. apply H44; econstructor; eapply var_per_elem; eauto.
    etransitivity; [|symmetry]; eassumption.
    etransitivity; [symmetry|]; eassumption.
  }
  assert {{ Dom ρσ ↦ ⇑! a s ↦ ⇑! a (S s) ↦ ⇑! (Eq a (⇑! a s) (⇑! a (S s))) (S (S s)) ≈ ρ'σ' ↦ ⇑! a' s ↦ ⇑! a' (S s) ↦ ⇑! (Eq a' (⇑! a' s) (⇑! a' (S s))) (S (S s)) ∈ env_relΔAAEq }}. {
    unfold env_relΔAAEq; unshelve eexists; intuition. simpl.
    eapply H39. econstructor. eapply var_per_bot.
  }
  assert {{ EF Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ≈ Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ∈ per_ctx_env ↘ env_relΔAAEq }} by (econstructor; mauto 3; try reflexivity; typeclasses eauto).
  invert_rel_exp_of_typ HB.
  gen ρσ ρ'σ'. intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΔAAEq).
  invert_rel_typ_body.
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  handle_per_univ_elem_irrel.
  simplify_evals. simpl in *.
  handle_per_univ_elem_irrel.
  (on_all_hyp: fun H => edestruct (per_univ_then_per_top_typ H s) as [? []]).
  (on_all_hyp: fun H => edestruct (per_univ_then_per_top_typ H (S (S (S s)))) as [? []]).
  functional_read_rewrite_clear.
  (* TODO *)
  setoid_rewrite <- H36 in H19.
  eapply per_elem_then_per_top in H27 as Hrelam1; eauto.
  eapply per_elem_then_per_top in H29 as Hrelam2; eauto.
  apply per_univ_then_per_top_typ in H19.
  destruct (Hrelam1 s). destruct_conjs.
  destruct (Hrelam2 s). destruct_conjs.
  handle_per_univ_elem_irrel.
  eapply per_univ_then_per_top_typ in H63 as Hrelm3; eauto.
  eapply per_univ_then_per_top_typ in H55 as Hrelm4; eauto.
  destruct (Hrelm3 (S (S (S s)))). destruct_conjs.
  destruct (Hrelm4 (S s)). destruct_conjs.
  destruct (equiv_m_m' s). destruct_conjs. 
  functional_read_rewrite_clear.
  clear H23.
  (on_all_hyp: fun H => unshelve epose proof (per_elem_then_per_top H _ (S s)) as [? []]; shelve_unifiable; [eassumption |]).
  (on_all_hyp: fun H => unshelve epose proof (per_elem_then_per_top H _ (S (S (S s)))) as [? []]; shelve_unifiable; [eassumption |]).
  functional_read_rewrite_clear.
  eexists. split.
  - eapply read_ne_eqrec; mauto.
  - match goal with
    | _: {{ ⟦ B' ⟧ ρ'σ' ↦ ⇑! a' s ↦ ⇑! a' (S s) ↦ ⇑! (Eq a' ⇑! a' s ⇑! a' (S s)) (S (S s)) ↘ ^?b0'' }} ,
        _: {{ ⟦ B' ⟧ ρ'σ' ↦ ⇑! a' s ↦ ⇑! a' s ↦ refl ⇑! a' s ↘ ^?bbr0'  }} ,
          _: {{ ⟦ BR' ⟧ ρ'σ' ↦ ⇑! a' s ↘ ^?br0' }} |- _ =>
      eapply read_ne_eqrec with (b:=b0'') (br:=br0') (bbr:=bbr0'); eauto
    end.
    + repeat econstructor; mauto 3.
    + repeat econstructor; mauto 3.
    + repeat econstructor; mauto 3.
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
                eqrec m' under ρ' as Eq a' m1' m2' return B'[q (q (q Id))] | refl -> BR'[q Id] end ∈ per_bot }}. 
  { eapply (@eval_eqrec_sub_neut _ _ _ _ _ _ _ _ _ M1 M1' M2 M2'); mauto 3. }
  etransitivity; [eassumption |].
  intros s.
  match_by_head per_bot ltac:(fun H => specialize (H s) as [? []]).
  eexists; split; [eassumption |].
  dir_inversion_by_head read_ne; subst.
  simplify_evals.
  mauto.
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
  intros * [env_relΓ [? [env_relΔ]]] HA HM1 HM2 HB HBR HN.
  destruct_conjs.
  apply rel_exp_eqrec_wf_Awk in HA as HA'.
  apply rel_exp_eqrec_wf_EqAwkwk in HA as HEq.
  invert_rel_exp_of_typ HA.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relA]; shelve_unifiable; [eassumption |]).
  invert_rel_exp HM1.
  invert_rel_exp HM2.
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
  invert_rel_exp_of_typ HB.
  invert_rel_exp HBR.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  invert_rel_typ_body.
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
  - assert {{ Dom ρσ ↦ n ≈ ρ'σ ↦ n' ∈ env_relΔA }} by (unfold env_relΔA; mauto 3).
    assert {{ Dom ρσ ↦ m1 ≈ ρ'σ ↦ m1' ∈ env_relΔA }} by (unfold env_relΔA; mauto 3).
    handle_per_ctx_env_irrel.
    (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relAx]; shelve_unifiable; [eassumption |]).
    assert {{ Dom ρσ ↦ n ≈ ρσ ↦ m1 ∈ env_relΔA }}. { 
      assert {{ Dom ρσ ≈ ρσ ∈ env_relΔ }} by (etransitivity; [|symmetry]; eassumption).
      (on_all_hyp: destruct_rel_by_assumption env_relΔ). intros.
      destruct_by_head rel_typ.
      destruct_by_head rel_exp.
      invert_rel_typ_body. 
      unfold env_relΔA.
      simplify_evals.
      rewrite_relation_equivalence_right.
      dir_inversion_by_head per_eq. subst.
      symmetry. mauto.
    }
    (on_all_hyp: destruct_rel_by_assumption env_relΔA).
    simplify_evals.
    handle_per_univ_elem_irrel.
    assert {{ Dom ρσ ↦ m1 ↦ m2 ≈ ρ'σ ↦ m1' ↦ m2' ∈ env_relΔAA }} by (unfold env_relΔAA; unshelve eexists; intuition).
    assert {{ Dom ρσ ↦ n ↦ n ≈ ρσ ↦ m1 ↦ m2 ∈ env_relΔAA }}. {
      unfold env_relΔAA; unshelve eexists; intuition. simpl. 
      saturate_PER.
      (* TODO *)
      apply H43; eauto.
      etransitivity; eauto. etransitivity; [|symmetry]; eauto.
    }
    (on_all_hyp: destruct_rel_by_assumption env_relΔAA).
    simplify_evals.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    handle_per_univ_elem_irrel.
    assert {{ Dom ρσ ↦ m1 ↦ m2 ↦ refl n ≈ ρ'σ ↦ m1' ↦ m2' ↦ refl n' ∈ env_relΔAAEq }} by (unshelve eexists; simpl; intuition; eauto).
    assert {{ Dom ρσ ↦ n ↦ n ↦ refl n ≈ ρσ ↦ m1 ↦ m2 ↦ refl n ∈ env_relΔAAEq }}. {
      unfold env_relΔAA; unshelve eexists; intuition. simpl. 
      saturate_PER.
      (* TODO *)
      apply H46. econstructor; mauto; 
      apply H42; auto.
      etransitivity; [|symmetry]; eauto.
      etransitivity; [|symmetry]; eauto.
    }
    (on_all_hyp: destruct_rel_by_assumption env_relΔAAEq).
    destruct_conjs.
    destruct_by_head rel_typ.
    destruct_by_head rel_exp.
    handle_per_univ_elem_irrel.
    simplify_evals.
    simpl in *.
    handle_per_ctx_env_irrel.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    handle_per_univ_elem_irrel.
    deex. eexists; split. 
    handle_per_univ_elem_irrel.
    + match goal with
      | _: {{ ⟦ B ⟧ ρσ ↦ m1 ↦ m2 ↦ refl n ↘ ^?b0 }},
          _: {{ ⟦ B ⟧ ρ'σ ↦ m1' ↦ m2' ↦ refl n' ↘ ^?b0'  }} |- _ =>
        eapply mk_rel_mod_eval with (a:=b0) (a':=b0')
      end.
      do 2 (econstructor; mauto).
      do 2 (econstructor; mauto). mauto.
    + econstructor; mauto.
      econstructor; mauto.
      eapply H17. auto.
  - assert {{ Dom ρσ ↦ m1 ≈ ρ'σ ↦ m1' ∈ env_relΔA }} by (unfold env_relΔA; mauto 3).
    handle_per_ctx_env_irrel.
    (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relAx]; shelve_unifiable; [eassumption |]).
    (on_all_hyp: destruct_rel_by_assumption env_relΔA).
    simplify_evals.
    handle_per_univ_elem_irrel.
    assert {{ Dom ρσ ↦ m1 ↦ m2 ≈ ρ'σ ↦ m1' ↦ m2' ∈ env_relΔAA }} by (unfold env_relΔAA; unshelve eexists; intuition).
    assert {{ Dom ρσ ↦ m1 ↦ m2 ≈ ρσ ↦ m1 ↦ m2 ∈ env_relΔAA }} by (etransitivity; [|symmetry]; eassumption).
    (on_all_hyp: destruct_rel_by_assumption env_relΔAA).
    simplify_evals.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    handle_per_univ_elem_irrel.
    (on_all_hyp: destruct_rel_by_assumption env_relΔAAEq).
    assert {{ Dom ρσ ↦ m1 ↦ m2 ↦ ⇑ a1 n ≈ ρ'σ ↦ m1' ↦ m2' ↦ ⇑ a' n' ∈ env_relΔAAEq }} by 
      (unshelve eexists; simpl; intuition; eauto).
    assert {{ Dom ρσ ↦ m1 ↦ m2 ↦ (⇑ (Eq a m1 m2) n) ≈ ρ'σ ↦ m1' ↦ m2' ↦ (⇑ (Eq a0 m1' m2') n') ∈ env_relΔAAEq }} by (unshelve eexists; simpl; intuition; eauto).
    assert {{ Dom ρσ ↦ m1 ↦ m2 ↦ (⇑ a1 n) ≈ ρσ ↦ m1 ↦ m2 ↦ (⇑ (Eq a m1 m2) n) ∈ env_relΔAAEq }}. {
      unshelve eexists; simpl; intuition; eauto.
      eapply H41. econstructor; eauto.
      etransitivity; [|symmetry]; eauto. 
    }
    (on_all_hyp: destruct_rel_by_assumption env_relΔAAEq).
    destruct_conjs.
    destruct_by_head rel_typ.
    destruct_by_head rel_exp.
    handle_per_univ_elem_irrel.
    simplify_evals.
    handle_per_ctx_env_irrel.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    handle_per_univ_elem_irrel.
    simplify_evals.
    deex. eexists; split. 
    handle_per_univ_elem_irrel.
    + repeat (econstructor; mauto 3).
    + econstructor; mauto.  
      econstructor; mauto.
      eapply eval_eqrec_neut with (b:=a'1).
      repeat (econstructor; mauto 3).
      eapply per_bot_then_per_elem; mauto.
      rewrite_relation_equivalence_right. mauto.
      eapply (@eval_eqrec_sub_neut Γ _ _ Δ);
        unshelve mauto; eauto; 
        econstructor; eexists; eauto.
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
  intros * HA _ _ [env_relΓ]%rel_exp_of_typ_inversion1 HM1M1' HM2M2' HBB' HBRBR' HNN'.
  assert (HB: {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊨ B : Type@j }} ) by (eapply rel_exp_trans; [| eapply rel_exp_sym]; eassumption).
  assert (HN: {{ Γ ⊨ N : Eq A M1 M2 }} ) by (eapply rel_exp_trans; [| eapply rel_exp_sym]; eassumption).
  destruct_conjs.
  apply rel_exp_eqrec_wf_Awk in HA as HA'.
  apply rel_exp_eqrec_wf_EqAwkwk in HA as HEq.
  invert_rel_exp_of_typ HA.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relA]; shelve_unifiable; [eassumption |]).
  pose (env_relΓA := cons_per_ctx_env env_relΓ elem_relA).
  assert {{ EF Γ, A ≈ Γ, A ∈ per_ctx_env ↘ env_relΓA }} by (econstructor; mauto 3; try reflexivity; typeclasses eauto).
  invert_rel_exp_of_typ HA'.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relA']; shelve_unifiable; [eassumption |]).
  pose (env_relΓAA := cons_per_ctx_env env_relΓA elem_relA').
  assert {{ EF Γ, A, A[Wk] ≈ Γ, A, A[Wk] ∈ per_ctx_env ↘ env_relΓAA }} by (econstructor; mauto 3; try reflexivity; typeclasses eauto).
  invert_rel_exp_of_typ HEq.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relEq]; shelve_unifiable; [eassumption |]).
  pose (env_relΓAAEq := cons_per_ctx_env env_relΓAA elem_relEq).
  assert {{ EF Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ≈ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ∈ per_ctx_env ↘ env_relΓAAEq }} by (econstructor; mauto 3; try reflexivity; typeclasses eauto).
  invert_rel_exp HM1M1'.
  invert_rel_exp HM2M2'.
  invert_rel_exp HN.
  invert_rel_exp HNN'.
  invert_rel_exp HB.
  invert_rel_exp_of_typ HBB'.
  invert_rel_exp HBRBR'.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  invert_rel_typ_body.
  match_by_head per_eq ltac:(fun H => dependent destruction H).
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
    assert {{ Dom ρ ↦ n ≈ ρ' ↦ n'' ∈ env_relΓA }} by (unfold env_relΓA; mauto 3).
    assert {{ Dom ρ ↦ m1 ≈ ρ' ↦ m1' ∈ env_relΓA }} by (unfold env_relΓA; mauto 3).
    assert {{ Dom ρ ↦ m1 ≈ ρ' ↦ m1'' ∈ env_relΓA }} by (unfold env_relΓA; mauto 3).
    handle_per_ctx_env_irrel.
    (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relAx]; shelve_unifiable; [eassumption |]).
    assert {{ Dom ρ ↦ n ≈ ρ ↦ m1 ∈ env_relΓA }}. { 
      assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (etransitivity; [|symmetry]; eassumption).
      (on_all_hyp: destruct_rel_by_assumption env_relΓ). intros.
      destruct_by_head rel_typ.
      destruct_by_head rel_exp.
      invert_rel_typ_body. 
      unfold env_relΓA.
      simplify_evals.
      rewrite_relation_equivalence_right.
      dir_inversion_by_head per_eq. subst.
      symmetry. mauto.
    }
    (on_all_hyp: destruct_rel_by_assumption env_relΓA).
    simplify_evals.
    handle_per_univ_elem_irrel.
    assert {{ Dom ρ ↦ m1 ↦ m2 ≈ ρ' ↦ m1'' ↦ m2'' ∈ env_relΓAA }} by (unfold env_relΓAA; unshelve eexists; intuition).
    assert {{ Dom ρ ↦ m1 ↦ m2 ≈ ρ' ↦ m1' ↦ m2' ∈ env_relΓAA }} by (unfold env_relΓAA; unshelve eexists; intuition).
    assert {{ Dom ρ ↦ n ↦ n ≈ ρ ↦ m1 ↦ m2 ∈ env_relΓAA }}. {
      unfold env_relΓAA; unshelve eexists; intuition. simpl. 
      saturate_PER.
      (* TODO *)
      apply H51. apply H60. 
      etransitivity; eauto. etransitivity; eauto. symmetry; auto.
    }
    (on_all_hyp: destruct_rel_by_assumption env_relΓAA).
    simplify_evals.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    handle_per_univ_elem_irrel.
    assert {{ Dom ρ ↦ m1 ↦ m2 ↦ refl n ≈ ρ' ↦ m1' ↦ m2' ↦ refl n' ∈ env_relΓAAEq }}. {
      unfold env_relΓAA; unshelve eexists; intuition. simpl. 
      apply H70; econstructor; eapply H56; auto.
    }
    assert {{ Dom ρ ↦ n ↦ n ↦ refl n ≈ ρ ↦ m1 ↦ m2 ↦ refl n ∈ env_relΓAAEq }}. {
      unfold env_relΓAA; unshelve eexists; intuition. simpl. 
      saturate_PER.
      (* TODO *)
      apply H57. econstructor; mauto;
      apply H59; auto.
      etransitivity; [|symmetry]; eauto.
      etransitivity; [|symmetry]; eauto.
    }
    (on_all_hyp: destruct_rel_by_assumption env_relΓAAEq).
    destruct_conjs.
    destruct_by_head rel_typ.
    destruct_by_head rel_exp.
    handle_per_univ_elem_irrel.
    simplify_evals.
    simpl in *.
    handle_per_ctx_env_irrel.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    handle_per_univ_elem_irrel.
    deex. eexists; split. 
    handle_per_univ_elem_irrel.
    + match goal with
      | _: {{ ⟦ B ⟧ ρ ↦ m1 ↦ m2 ↦ refl n ↘ ^?b0 }},
          _: {{ ⟦ B ⟧ ρ' ↦ m1' ↦ m2' ↦ refl n' ↘ ^?b0'  }} |- _ =>
        eapply mk_rel_mod_eval with (a:=b0) (a':=b0')
      end.
      do 2 (econstructor; mauto).
      do 2 (econstructor; mauto). mauto.
    + handle_per_univ_elem_irrel.
      econstructor; mauto.
      eapply H41; eauto.
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
    assert {{ Dom ρ ↦ m1 ≈ ρ' ↦ m1' ∈ env_relΓA }} by (unfold env_relΓA; mauto 3).
    assert {{ Dom ρ ↦ m1 ≈ ρ' ↦ m1'' ∈ env_relΓA }} by (unfold env_relΓA; mauto 3).
    handle_per_ctx_env_irrel.
    (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relAx]; shelve_unifiable; [eassumption |]).
    (on_all_hyp: destruct_rel_by_assumption env_relΓA).
    simplify_evals.
    handle_per_univ_elem_irrel.
    assert {{ Dom ρ ↦ m1 ↦ m2 ≈ ρ' ↦ m1' ↦ m2' ∈ env_relΓAA }} by (unfold env_relΓAA; unshelve eexists; intuition).
    assert {{ Dom ρ ↦ m1 ↦ m2 ≈ ρ' ↦ m1'' ↦ m2'' ∈ env_relΓAA }} by (unfold env_relΓAA; unshelve eexists; intuition).
    assert {{ Dom ρ ↦ m1 ↦ m2 ≈ ρ ↦ m1 ↦ m2 ∈ env_relΓAA }} by (etransitivity; [|symmetry]; eassumption).
    (on_all_hyp: destruct_rel_by_assumption env_relΓAA).
    simplify_evals.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    handle_per_univ_elem_irrel.
    (on_all_hyp: destruct_rel_by_assumption env_relΓAAEq).
    assert {{ Dom ρ ↦ m1 ↦ m2 ↦ ⇑ an n ≈ ρ' ↦ m1' ↦ m2' ↦ ⇑ an' n' ∈ env_relΓAAEq }} by
      (unshelve eexists; simpl; intuition; eauto).
    assert {{ Dom ρ ↦ m1 ↦ m2 ↦ (⇑ (Eq a m1 m2) n) ≈ ρ' ↦ m1'' ↦ m2'' ↦ (⇑ (Eq a'' m1'' m2'') n'') ∈ env_relΓAAEq }} by (unshelve eexists; simpl; intuition; eauto).
    assert {{ Dom ρ ↦ m1 ↦ m2 ↦ (⇑ an n) ≈ ρ ↦ m1 ↦ m2 ↦ (⇑ (Eq a m1 m2) n) ∈ env_relΓAAEq }}. {
      unshelve eexists; simpl; intuition; eauto.
      eapply H58. econstructor; eauto.
      etransitivity; [|symmetry]; eauto. 
    }
    (on_all_hyp: destruct_rel_by_assumption env_relΓAAEq).
    destruct_conjs.
    destruct_by_head rel_typ.
    destruct_by_head rel_exp.
    handle_per_univ_elem_irrel.
    simplify_evals.
    handle_per_ctx_env_irrel.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    handle_per_univ_elem_irrel.
    simplify_evals.
    deex. eexists; split. 
    handle_per_univ_elem_irrel.
    + repeat (econstructor; mauto 3).
    + econstructor; mauto.
      eapply per_bot_then_per_elem; mauto.
      handle_per_univ_elem_irrel. mauto.
      eapply (@eval_eqrec_neut_same_ctx Γ _ _ );
        unshelve mauto; eauto;
        econstructor; eexists; eauto.
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
  apply rel_exp_eqrec_wf_Awk in HA as HA'.
  apply rel_exp_eqrec_wf_EqAwkwk in HA as HEq.
  invert_rel_exp_of_typ HA.
  rename x into env_relΓ.
  destruct_conjs.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relA]; shelve_unifiable; [eassumption |]).
  invert_rel_exp HM.
  pose (env_relΓA := cons_per_ctx_env env_relΓ elem_relA).
  assert {{ EF Γ, A ≈ Γ, A ∈ per_ctx_env ↘ env_relΓA }} by (econstructor; mauto 3; try reflexivity; typeclasses eauto).
  invert_rel_exp_of_typ HA'.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relA']; shelve_unifiable; [eassumption |]).
  pose (env_relΓAA := cons_per_ctx_env env_relΓA elem_relA').
  assert {{ EF Γ, A, A[Wk] ≈ Γ, A, A[Wk] ∈ per_ctx_env ↘ env_relΓAA }} by (econstructor; mauto 3; try reflexivity; typeclasses eauto).
  invert_rel_exp_of_typ HEq.
  (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relEq]; shelve_unifiable; [eassumption |]).
  pose (env_relΓAAEq := cons_per_ctx_env env_relΓAA elem_relEq).
  assert {{ EF Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ≈ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ∈ per_ctx_env ↘ env_relΓAAEq }} by (econstructor; mauto 3; try reflexivity; typeclasses eauto).
  invert_rel_exp HBR.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  invert_rel_typ_body. 
  assert {{ Dom ρ ↦ m ≈ ρ' ↦ m' ∈ env_relΓA }} by (unfold env_relΓA; mauto 3).
  (on_all_hyp: destruct_rel_by_assumption env_relΓA).
  simplify_evals.
  handle_per_univ_elem_irrel.
  assert {{ Dom ρ ↦ m ↦ m ≈ ρ' ↦ m' ↦ m' ∈ env_relΓAA }} by (unfold env_relΓAA; unshelve eexists; intuition).
  (on_all_hyp: destruct_rel_by_assumption env_relΓAA).
  simplify_evals.
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
  handle_per_univ_elem_irrel.
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  simplify_evals.
  handle_per_univ_elem_irrel.
  assert ({{ ⟦ B[Id,,M,,M,,refl A M] ⟧ ρ ↘ m0 }}) by (econstructor; mauto 5).
  assert ({{ ⟦ B[Id,,M,,M,,refl A M] ⟧ ρ' ↘ m2 }}) by (econstructor; mauto 5).
  eexists; split; mauto 3. econstructor; mauto 3. 
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve rel_exp_eqrec_beta : mctt.
