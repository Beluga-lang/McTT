From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Completeness Require Import 
  UniverseCases
  EqualityCases
  FundamentalTheorem.
From Mctt.Core.Soundness Require Import
  ContextCases
  LogicalRelation
  SubstitutionCases
  SubtypingCases
  TermStructureCases
  UniverseCases.
Import Domain_Notations.


Lemma glu_rel_eq : forall Γ A i M N,
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ ⊩ M : A }} ->
    {{ Γ ⊩ N : A }} ->
    {{ Γ ⊩ Eq A M N : Type@i }}.
Proof.
  intros * HA HM HN.
  assert {{ ⊩ Γ }} as [SbΓ] by mauto.
  saturate_syn_judge.
  invert_sem_judge.

  eapply glu_rel_exp_of_typ; mauto 3.
  intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 4.
  split; mauto 3.
  apply_glu_rel_judge.
  saturate_glu_typ_from_el.
  unify_glu_univ_lvl i.
  deepexec glu_univ_elem_per_univ ltac:(fun H => pose proof H).
  match_by_head per_univ ltac:(fun H => destruct H).
  do 2 deepexec glu_univ_elem_per_elem ltac:(fun H => pose proof H; fail_at_if_dup ltac:(4)).

  eexists; repeat split; mauto.
  - eexists. per_univ_elem_econstructor; mauto. reflexivity.
  - intros.
    match_by_head1 glu_univ_elem invert_glu_univ_elem.
    handle_per_univ_elem_irrel.
    handle_functional_glu_univ_elem.
    econstructor; mauto 3;
      intros Δ' τ **;
      assert {{ Δ' ⊢s τ : Δ }} by mauto 2;
      assert {{ Δ' ⊢s σ ∘ τ ® ρ ∈ SbΓ }} by (eapply glu_ctx_env_sub_monotone; eassumption);
      assert {{ Δ' ⊢s σ ∘ τ : Γ }} by mauto 2;
      apply_glu_rel_judge;
      handle_functional_glu_univ_elem;
      unify_glu_univ_lvl i.
    + bulky_rewrite.
    + assert {{ Δ' ⊢ M[σ][τ] ≈ M[σ ∘ τ] : A[σ ∘ τ] }} by mauto.
      bulky_rewrite.
    + assert {{ Δ' ⊢ N[σ][τ] ≈ N[σ ∘ τ] : A[σ ∘ τ] }} by mauto.
      bulky_rewrite.
Qed.

#[export]
  Hint Resolve glu_rel_eq : mctt.

Lemma glu_rel_eq_refl : forall Γ A M,
    {{ Γ ⊩ M : A }} ->
    {{ Γ ⊩ refl A M : Eq A M M }}.
Proof.
  intros * HM.
  assert {{ ⊩ Γ }} as [SbΓ] by mauto.
  saturate_syn_judge.
  invert_sem_judge.
  assert {{ Γ ⊢ A : Type@i }} by mauto.
  eexists; split; eauto.
  exists i; intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 4.
  apply_glu_rel_judge.
  saturate_glu_typ_from_el.
  deepexec glu_univ_elem_per_univ ltac:(fun H => pose proof H).
  match_by_head per_univ ltac:(fun H => unfold per_univ in H; deex_once_in H).
  deepexec glu_univ_elem_per_elem ltac:(fun H => pose proof H; fail_at_if_dup ltac:(4)).
  saturate_glu_info.
  eexists; repeat split; mauto.
  - glu_univ_elem_econstructor; mauto 3; reflexivity.
  - do 2 try econstructor; mauto 3;
    intros Δ' τ **;
      assert {{ Δ' ⊢s τ : Δ }} by mauto 2;
    assert {{ Δ' ⊢s σ ∘ τ ® ρ ∈ SbΓ }} by (eapply glu_ctx_env_sub_monotone; eassumption);
    assert {{ Δ' ⊢s σ ∘ τ : Γ }} by mauto 2;
    assert {{ Δ' ⊢ M[σ][τ] ≈ M[σ ∘ τ] : A[σ ∘ τ] }} by mauto;
    apply_glu_rel_judge;
    saturate_glu_typ_from_el;
    bulky_rewrite.
Qed.

#[export]
  Hint Resolve glu_rel_eq_refl : mctt.

Lemma glu_rel_exp_eq_clean_inversion : forall {i Γ Sb M1 M2 A N},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ ⊩ M1 : A }} ->
    {{ Γ ⊩ M2 : A }} ->
    {{ Γ ⊩ N : Eq A M1 M2 }} ->
    glu_rel_exp_resp_sub_env i Sb N {{{Eq A M1 M2}}}.
Proof.
  intros * ? HA HM1 HM2 HN.
  assert {{ Γ ⊩ Eq A M1 M2 : Type@i }} by mauto.
  eapply glu_rel_exp_clean_inversion2 in HN; eassumption.
Qed.


#[global]
  Ltac invert_glu_rel_exp H ::=
  directed (unshelve eapply (glu_rel_exp_eq_clean_inversion _) in H; shelve_unifiable; try eassumption;
   simpl in H)
  + universe_invert_glu_rel_exp H.

#[local]
  Hint Resolve completeness_fundamental_ctx completeness_fundamental_exp : mctt.

Lemma glu_rel_eq_eqrec : forall Γ A i M1 M2 B j BR N,
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ ⊩ M1 : A }} ->
    {{ Γ ⊩ M2 : A }} ->
    {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊩ B : Type@j }} ->
    {{ Γ, A ⊩ BR : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Γ ⊩ N : Eq A M1 M2 }} ->
    {{ Γ ⊩ eqrec N as Eq A M1 M2 return B | refl -> BR end : B[Id,,M1,,M2,,N] }}.
Proof.
  intros * HA HM1 HM2 HB HBR HN.
  assert {{ ⊩ Γ }} by mauto.
  assert {{ ⊩ Γ }} as [SbΓ] by mauto.
  saturate_syn_judge.

  assert {{ Γ ⊩s Id,,M1 : Γ, A }} by (eapply glu_rel_sub_extend; mauto 3; bulky_rewrite).
  assert {{ ⊩ Γ , A }} by mauto.
  assert {{ ⊩ Γ , A }} as [SbΓA] by mauto.
  assert {{ Γ ⊩s Id,,M1,,M2 : Γ, A, A[Wk] }} by (eapply glu_rel_sub_extend; mauto 4).
  assert {{ ⊩ Γ , A, A[Wk] }} by (unshelve mauto; eauto). 
  assert {{ ⊩ Γ , A, A[Wk] }} as [SbΓAA] by mauto.
  assert {{ Γ ⊩s Id,,M1,,M2,,N : Γ, A, A[Wk], Eq A[Wk ∘ Wk] #1 #0 }}.
  {
    eapply glu_rel_sub_extend; mauto 4.
    eapply glu_rel_eq.
    - mauto.
    - rewrite <- @exp_eq_sub_compose_typ with (i := i); mauto 3.
    - rewrite <- @exp_eq_sub_compose_typ with (i := i); mauto 3.
  }
  assert {{ ⊩ Γ, A, A[Wk], Eq A[Wk ∘ Wk] #1 #0 }} as [SbΓAAEq] by mauto.
  assert {{ Γ, A ⊩s Id,,#0 : Γ, A, A[Wk] }} by
    (eapply glu_rel_sub_extend; mauto 3; bulky_rewrite).
  saturate_syn_judge.

  assert {{ Γ, A ⊢ (Eq A[Wk∘Wk] #1 #0)[Id,,#0] ≈ Eq A[Wk] #0 #0 : Type@i }} by admit.

  assert {{ Γ, A ⊩s Id,,#0,,refl A[Wk] #0 : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }}.
  {
    eapply glu_rel_sub_extend; mauto 3.
    - eapply glu_rel_eq;
        try rewrite <- @exp_eq_sub_compose_typ with (A:=A); mauto.
    - bulky_rewrite.
      mauto 3.
  }
  saturate_syn_judge.

  invert_sem_judge.

  eexists; split; eauto.
  exists j; intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 4.
  apply_glu_rel_judge.
  apply_glu_rel_exp_judge.

  rename m2 into n.
  rename m1 into m2.
  rename m0 into m1.
  rename m into a.
  
  repeat invert_glu_rel1.  
  handle_functional_glu_univ_elem.
  saturate_glu_typ_from_el.
  unify_glu_univ_lvl i.

  rename B1 into Aσ.
  rename M0 into M1σ.
  rename N1 into M2σ.

  deepexec (glu_univ_elem_per_univ i) ltac:(fun H => pose proof H).
  match_by_head per_univ ltac:(fun H => unfold per_univ in H; deex_in H).
  do 2 deepexec (glu_univ_elem_per_elem i) ltac:(fun H => pose proof H; fail_at_if_dup ltac:(4)).
  saturate_glu_info.

  eassert (exists mr, {{ ⟦ eqrec N as Eq A M1 M2 return B | refl -> BR end ⟧ ρ ↘ mr }} /\ 
                      {{ Γ0 ⊢ eqrec N as Eq A M1 M2 return B | refl -> BR end[σ] : B[Id,,M1,,M2,,N][σ] ® mr ∈ El0 }}) as [? [? ?]].
  {
    destruct_glu_eq.
    - assert {{ Γ0 ⊢w Id : Γ0 }} as HId by mauto.
      assert {{ Γ0 ⊢ M'' : Aσ }} by (gen_presups; trivial).
      pose proof (H91 _ _ HId) as HM''.
      saturate_glu_typ_from_el.
      assert {{ Γ0 ⊢ Aσ[Id] ≈ Aσ : Type@i }} as HrwB1 by mauto 3.
      rewrite HrwB1 in *.
      assert {{ Γ0 ⊢ Aσ ≈ A[σ] : Type@i }} as HrwB1' by mauto 4.
      rewrite HrwB1' in *.
      saturate_glu_info. 
      assert (SbΓA Γ0 {{{σ ,, M''}}} d{{{ρ ↦ m'}}}).
      {
        match_by_head1 (glu_ctx_env SbΓA) invert_glu_ctx_env.
        apply_equiv_left.
        econstructor; mauto 3; bulky_rewrite.
        handle_per_univ_elem_irrel.
        handle_functional_glu_univ_elem. simpl.
        eapply glu_univ_elem_resp_per_elem with (m:=m2) (R:=R); try symmetry; eauto.
        assert {{ Γ0 ⊢ #0[σ,,M''] ≈ M2σ : A[σ] }} by mauto.
        assert {{ Γ0 ⊢ M2σ[Id] ≈ #0[σ,,M''] : A[σ] }} by mauto 4.
        eapply glu_univ_elem_trm_resp_exp_eq; eauto.
      }
      destruct_glu_rel_exp_with_sub.
      simplify_evals.
      handle_per_univ_elem_irrel.
      eexists; split; mauto 3.
      assert {{ Γ0 ⊢ B[Id,,#0,,refl A[Wk] #0][σ,,M''] ≈ B[Id,,M1,,M2,,N][σ] : Type@j }} by admit.
      assert {{ Γ0 ⊢ BR[σ,,M''] ≈ eqrec N as Eq A M1 M2 return B | refl -> BR end[σ] : B[Id,,#0,,refl A[Wk] #0][σ,,M''] }} by admit.
      (* m9 (⟦ BR ⟧ ρ ↦ m') -> El7 -> m (⟦ B ⟧ ρ ↦ m' ↦ m' ↦ refl m') *)
      (* m8 (⟦ BR ⟧ ρ ↦ m) -> El0 -> m7 (⟦ B ⟧ ρ ↦ m1 ↦ m2 ↦ refl m') *)
      (* by relating m7 and m, we can show El7 is equivalent to EL0 *)
      assert (exists R, {{ DF m7 ≈ m ∈ per_univ_elem j ↘ R }}). {
        assert {{ Γ ⊢ A : Type@i }} as HwfA by mauto 3.
        assert {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢ B : Type@j }} as HwfB by admit.
        apply completeness_fundamental_exp in HwfA.
        apply completeness_fundamental_exp in HwfB.
        pose proof HwfA.
        invert_rel_exp_of_typ HwfA. 
        rename x into env_relΓ.
        destruct_all.
        eapply eval_eqrec_relΓAAEq_helper in H53 as [env_relΓAAEq [equiv_ΓAAEq HΓAAEq]]; eauto.
        assert ({{ Dom ρ ↦ m1 ↦ m2 ↦ refl m' ≈ ρ ↦ m' ↦ m' ↦ refl m' ∈ env_relΓAAEq }}). {
          eapply HΓAAEq; eauto.
          - eapply (@glu_ctx_env_per_env Γ); mauto.
          - etransitivity; [|symmetry]; eassumption. 
          - econstructor; eauto. 
            etransitivity; [|symmetry]; eassumption.
            etransitivity; [|symmetry]; eassumption.  
        }
        invert_rel_exp_of_typ HwfB.
        (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relB]; shelve_unifiable; [eassumption |]).
        gen ρ. intros.
        (on_all_hyp: destruct_rel_by_assumption env_relΓAAEq).
        simplify_evals. mauto.
      }
      deex. handle_per_univ_elem_irrel.
      eapply glu_univ_elem_resp_per_univ with (a':=m) in H74 as H'; mauto.
      handle_functional_glu_univ_elem.
      eapply glu_univ_elem_trm_resp_typ_exp_eq; eauto.
      eapply glu_univ_elem_trm_resp_exp_eq; eauto.
    - match_by_head1 per_bot ltac:(fun H => pose proof (H (length Γ0)) as [V [HV _]]).
      assert {{ Γ0 ⊢w Id : Γ0 }} as HId by mauto.
      pose proof (H45 _ _ V HId HV).
      assert {{ Γ0 ⊢ N[σ] ≈ V : (Eq A M1 M2)[σ] }}. {
        assert {{ Γ0 ⊢ (Eq A M1 M2)[σ][Id] ≈ (Eq A M1 M2)[σ] : Type@i }} by mauto 4.
        assert {{ Γ0 ⊢ N[σ][Id] ≈ V : (Eq A M1 M2)[σ] }} by mauto 3.
        mauto 4.
      }
      eexists; split; mauto 3.
      eapply realize_glu_elem_bot; mauto 3.
      econstructor; mauto 3.
      + eapply glu_univ_elem_typ_resp_exp_eq; mauto 3.
      + assert {{ ⊨ Γ }} by mauto 3.
        assert {{ Γ ⊨ A : Type@i }} by mauto 3.
        assert {{ Γ ⊨ M1 : A }} by mauto 3.
        assert {{ Γ ⊨ M2 : A }} by mauto 3.
        assert {{ Γ, A ⊨ BR : B[Id,,#0,,refl A[Wk] #0] }} by mauto.
        assert {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊨ B : Type@j }} by mauto 3.
        unfold valid_ctx in *. unfold per_ctx in *. deex.
        eapply (@eval_eqrec_neut_same_ctx _ _ _ _ A _ M1 _ M2); mauto 3.
        eapply (@glu_ctx_env_per_env Γ); mauto.
      + intros. 
        assert {{ Δ ⊢ eqrec N as Eq A M1 M2 return B | refl -> BR end[σ][σ0] ≈ M' : B[Id,,M1,,M2,,N][σ][σ0] }} by admit.
        auto.
      }
  econstructor; mauto.
Admitted.

#[export]
  Hint Resolve glu_rel_eq_eqrec : mctt.
