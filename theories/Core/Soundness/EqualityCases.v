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

Lemma wf_exp_eq_eqrec_Awkqσ_Aσwk : forall {Γ σ Δ i A},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ, A[σ] ⊢ A[Wk][q σ] ≈ A[σ][Wk] : Type@i }}.
Proof.
  intros.
  assert  {{ ⊢ Δ, A }} by mauto 3.
  assert {{ Δ, A ⊢s Wk : Δ }} by mauto 2.
  assert {{ Δ, A ⊢ A[Wk] : Type@i }} by mauto 2.
  assert {{ ⊢ Δ, A, A[Wk] }} by mauto 2.
  assert {{ Δ, A, A[Wk] ⊢s Wk∘Wk : Δ }} by mauto 3.
  assert {{ Δ, A, A[Wk] ⊢ A[Wk∘Wk] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ A[σ] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ A[σ] : Type@i }} by mauto 2.
  assert {{ Γ, A[σ] ⊢s q σ : Δ, A }} by mauto 2.
  assert {{ Γ, A[σ] ⊢s Wk : Γ }} by mauto 3.
  assert {{ Γ, A[σ] ⊢ A[σ][Wk] : Type@i }} by mauto 2.
  assert {{ ⊢ Γ, A[σ], A[σ][Wk] }} by mauto 3.
  assert {{ Γ, A[σ], A[σ][Wk] ⊢s Wk : Γ, A[σ] }} by mauto 2.
  assert {{ Γ, A[σ], A[σ][Wk] ⊢ A[σ][Wk∘Wk] : Type@i }} by mauto 3.
  assert {{ Γ, A[σ] ⊢ A[Wk][q σ] ≈ A[σ][Wk] : Type@i }} by mauto 3.
  assert {{ ⊢ Γ, A[σ], A[Wk][q σ] ≈ Γ, A[σ], A[σ][Wk] }} by (econstructor; mauto 3).
  assert {{ Γ, A[σ], A[σ][Wk] ⊢s q (q σ) : Δ, A, A[Wk] }} by mauto 3.
  assert {{ Γ, A[σ], A[σ][Wk] ⊢ A[Wk][q σ∘Wk] : Type@i }} by mauto 3.
  assert {{ Γ, A[σ], A[σ][Wk] ⊢ A[Wk][q σ∘Wk] ≈ A[σ][Wk∘Wk] : Type@i }}. {  {
    transitivity {{{ A[Wk][q σ][Wk] }}}; [mauto 3 |].
    transitivity {{{ A[σ][Wk][Wk] }}}; [| mauto 2].
    eapply exp_eq_sub_cong_typ1; mauto 3.
  }}
  mauto 3.
Qed.

Lemma wf_exp_eq_eqrec_cong_sub : forall {Γ σ Δ i j A A' M1 M1' M2 M2' N N' B B' BR BR'},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ A[σ] ≈ A' : Type@i }} ->
    {{ Γ ⊢ M1[σ] ≈ M1' : A[σ] }} ->
    {{ Γ ⊢ M2[σ] ≈ M2' : A[σ] }} ->
    {{ Γ ⊢ N[σ] ≈ N' : Eq A[σ] M1[σ] M2[σ]}} ->
    {{ Γ , A[σ] ⊢ BR[q σ] ≈ BR' : A[σ] }} ->
    {{ Γ , A[σ] , A[σ][Wk], Eq A[σ][Wk∘Wk] #1 #0 ⊢ B[q (q (q σ))] ≈ B' : Type@j }} ->
    {{ Γ ⊢ eqrec N as Eq A M1 M2 return B | refl -> BR end[σ] ≈ 
           eqrec N' as Eq A' M1' M2' return B' | refl -> BR' end : B[Id,,M1,,M2,,N][σ] }}.
Proof.
Admitted.

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
  pose (SbΓA := cons_glu_sub_pred i Γ {{{ A }}} SbΓ).
  saturate_syn_judge.
  assert {{ EG Γ, A ∈ glu_ctx_env ↘ SbΓA }} by (invert_glu_rel_exp HA; econstructor; mauto 3; try reflexivity).
  assert {{ Γ ⊩s Id,,M1 : Γ, A }} by (eapply glu_rel_sub_extend; mauto 3; bulky_rewrite).
  assert {{ ⊩ Γ , A }} by mauto.
  assert {{ Γ ⊩s Id,,M1,,M2 : Γ, A, A[Wk] }} by (eapply glu_rel_sub_extend; mauto 4).
  assert {{ ⊩ Γ , A, A[Wk] }} by (unshelve mauto; eauto). 
  assert {{ Γ , A ⊩ A[Wk] : Type@i }} by (unshelve mauto; eauto). 
  saturate_syn_judge. 
  pose (SbΓAA := cons_glu_sub_pred i {{{ Γ , A }}} {{{ A[Wk] }}} SbΓA).
  assert {{ EG Γ, A , A[Wk] ∈ glu_ctx_env ↘ SbΓAA }} by (invert_glu_rel_exp H13; econstructor; mauto 3; try reflexivity).
  assert {{ Γ ⊩s Id,,M1,,M2,,N : Γ, A, A[Wk], Eq A[Wk ∘ Wk] #1 #0 }}.
  {
    eapply glu_rel_sub_extend; mauto 4.
    eapply glu_rel_eq.
    - mauto.
    - rewrite <- @exp_eq_sub_compose_typ with (i := i); mauto 3.
    - rewrite <- @exp_eq_sub_compose_typ with (i := i); mauto 3.
  }
  assert {{ Γ, A ⊩s Id,,#0,,refl A[Wk] #0 : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }}.
  {
    assert {{ Γ, A ⊩s Id,,#0 : Γ, A, A[Wk] }} by
    (eapply glu_rel_sub_extend; mauto 3; bulky_rewrite).
    assert {{ ⊩ Γ, A, A[Wk], Eq A[Wk ∘ Wk] #1 #0 }} by mauto.
      assert {{ Γ, A ⊢ (Eq A[Wk∘Wk] #1 #0)[Id,,#0] ≈ Eq A[Wk] #0 #0 : Type@i }}. {
      admit.
    }
    eapply glu_rel_sub_extend; mauto 3.
    - eapply glu_rel_eq;
        try rewrite <- @exp_eq_sub_compose_typ with (A:=A); mauto.
    - bulky_rewrite.
      mauto 3.
  }
  assert {{ Γ, A, A[Wk] ⊩ Eq A[Wk ∘ Wk] #1 #0 : Type@i }}. {
    assert {{ Γ, A, A[Wk] ⊩s Wk : Γ, A }} by mauto 3.
    assert {{ Γ, A, A[Wk] ⊩s Wk∘Wk : Γ }} by mauto 3.
    assert {{ Γ, A, A[Wk] ⊩ A[Wk∘Wk] : Type@i[Wk∘Wk] }} by mauto.
    assert {{ Γ, A, A[Wk] ⊩ #0 : A[Wk][Wk] }} by mauto 3.
    assert {{ Γ, A, A[Wk] ⊩ #1 : A[Wk][Wk] }} by mauto 3.
    assert {{ Γ, A, A[Wk] ⊢ A[Wk][Wk] ≈ A[Wk∘Wk] : Type@i }} by mauto 4.
    assert {{ Γ, A, A[Wk] ⊩ #0 : A[Wk∘Wk] }} by mauto 3.
    assert {{ Γ, A, A[Wk] ⊩ #1 : A[Wk∘Wk] }} by mauto 3.
    mauto 3.
  }
  pose (SbΓAAEq := cons_glu_sub_pred i {{{ Γ , A , A[Wk] }}} {{{ Eq A[Wk ∘ Wk] #1 #0 }}} SbΓAA).
  assert {{ EG Γ, A , A[Wk] , Eq A[Wk ∘ Wk] #1 #0 ∈ glu_ctx_env ↘ SbΓAAEq }} by (invert_glu_rel_exp H22; econstructor; mauto 3; try reflexivity).

  saturate_syn_judge.
  clear H22. clear H12. clear H13. clear H11. clear H9.
  invert_sem_judge.
  eexists; split; eauto.
  exists j; intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 4.
  apply_glu_rel_judge.
  apply_glu_rel_exp_judge.

  match goal with
  | [ _ : {{ ⟦ A ⟧ ρ ↘ ^?a' }} , 
        _ : {{ ⟦ M1 ⟧ ρ ↘ ^?m1' }} ,
          _ : {{ ⟦ M2 ⟧ ρ ↘ ^?m2' }} ,
            _ : {{ ⟦ N ⟧ ρ ↘ ^?n' }} |- _ ] => 
    rename a' into a;
    rename n' into n;
    rename m1' into m1'';
    rename m2' into m2''
  end; rename m1'' into m1; rename m2'' into m2.
  
  repeat invert_glu_rel1.  
  rename Γ0 into Δ.
  handle_functional_glu_univ_elem.
  saturate_glu_typ_from_el.
  unify_glu_univ_lvl i.

  match goal with
  | [ H : {{ Δ ⊢ (Eq A M1 M2)[σ] ≈ Eq ^?A' ^?M1' ^?M2' : Type@i }} |- _ ] => 
      rename A' into Aσ;
      rename M1' into M1σ;
      rename M2' into M2σ
  end.

  deepexec (glu_univ_elem_per_univ i) ltac:(fun H => pose proof H).
  match_by_head per_univ ltac:(fun H => unfold per_univ in H; deex_in H).
  saturate_glu_info.

  eassert (exists mr, {{ ⟦ eqrec N as Eq A M1 M2 return B | refl -> BR end ⟧ ρ ↘ mr }} /\ 
                      {{ Δ ⊢ eqrec N as Eq A M1 M2 return B | refl -> BR end[σ] : B[Id,,M1,,M2,,N][σ] ® mr ∈ El0 }}) as [? [? ?]].
  {
    destruct_glu_eq; rename Γ0 into Δ. rename M'' into Mσ.
    - assert {{ Δ ⊢w Id : Δ }} as HId by mauto.
      assert {{ Δ ⊢ Mσ : Aσ }} by (gen_presups; trivial).
      pose proof (H75 _ _ HId) as HMσ.
      pose proof (H71 _ _ HId) as HM1σ.
      pose proof (H72 _ _ HId) as HM2σ.
      saturate_glu_typ_from_el.
      assert {{ Δ ⊢ Aσ[Id] ≈ Aσ : Type@i }} as HrwB1 by mauto 3.
      rewrite HrwB1 in *.
      assert {{ Δ ⊢ Aσ ≈ A[σ] : Type@i }} as HrwB1' by mauto 4.
      rewrite HrwB1' in *.
      assert {{ Δ ⊢ M1σ[Id] ≈ M1σ : A[σ] }} as HrwM1 by mauto 3.
      rewrite HrwM1 in *.
      assert {{ Δ ⊢ M2σ[Id] ≈ M2σ : A[σ] }} as HrwM2 by mauto 3.
      rewrite HrwM2 in *.
      assert {{ Δ ⊢ M1σ ≈ M1[σ] : A[σ] }} as HrwM1' by mauto 4.
      assert {{ Δ ⊢ M2σ ≈ M2[σ] : A[σ] }} as HrwM2' by mauto 4.
      saturate_glu_info. 
      assert (SbΓA Δ {{{σ ,, Mσ}}} d{{{ρ ↦ m'}}}).
      {
        unfold SbΓA. eapply cons_glu_sub_pred_helper; mauto 3.
        eapply glu_univ_elem_trm_resp_exp_eq; mauto.
      }
      assert {{ Δ ⊢ B[Id,,#0,,refl A[Wk] #0][σ,,Mσ] ≈ B[Id,,M1,,M2,,N][σ] : Type@j }}.  {
        admit.
      }
      assert {{ Δ ⊢ BR[σ,,Mσ] ≈ eqrec N as Eq A M1 M2 return B | refl -> BR end[σ] : B[Id,,#0,,refl A[Wk] #0][σ,,Mσ] }}. {
        rewrite H84.
        transitivity {{{ eqrec (refl Aσ Mσ) as Eq Aσ Mσ Mσ return B[q (q (q σ))] | refl -> BR[q σ] end }}}.
        - eapply wf_exp_eq_conv'.
          + symmetry. etransitivity; [eapply wf_exp_eq_eqrec_beta|]; mauto 3.
            admit. admit. admit.
          + admit.
        - symmetry. eapply (@wf_exp_eq_eqrec_cong_sub Δ _ Γ _ j); mauto 3.
          admit. admit.
      }
      destruct_glu_rel_exp_with_sub.
      simplify_evals.
      handle_per_univ_elem_irrel.
      eexists; split; mauto 3.
      (* m9 (⟦ BR ⟧ ρ ↦ m') -> El7 -> m (⟦ B ⟧ ρ ↦ m' ↦ m' ↦ refl m') *)
      (* m8 (⟦ BR ⟧ ρ ↦ m) -> El0 -> m7 (⟦ B ⟧ ρ ↦ m1 ↦ m2 ↦ refl m') *)
      (* by relating m7 and m, we can show El7 is equivalent to El0 *)
      assert (exists R, {{ DF m6 ≈ m ∈ per_univ_elem j ↘ R }}). {
        assert {{ Γ ⊢ A : Type@i }} as HwfA by mauto 3.
        assert {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢ B : Type@j }} as HwfB by auto.
        apply completeness_fundamental_exp in HwfA as HrelA.
        apply completeness_fundamental_exp in HwfB as HrelB.
        pose proof HrelA as HrelA'.
        invert_rel_exp_of_typ HrelA. 
        rename x into env_relΓ.
        destruct_all.
        eapply eval_eqrec_relΓAAEq_helper in HrelA' as [env_relΓAAEq [equiv_ΓAAEq HΓAAEq]]; eauto.
        assert ({{ Dom ρ ↦ m1 ↦ m2 ↦ refl m' ≈ ρ ↦ m' ↦ m' ↦ refl m' ∈ env_relΓAAEq }}). {
          eapply HΓAAEq; eauto.
          - eapply (@glu_ctx_env_per_env Γ); mauto.
          - etransitivity; [|symmetry]; eassumption. 
          - econstructor; eauto. 
            etransitivity; [|symmetry]; eassumption.
            etransitivity; [|symmetry]; eassumption.  
        }
        invert_rel_exp_of_typ HrelB.
        (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relB]; shelve_unifiable; [eassumption |]).
        gen ρ. intros.
        (on_all_hyp: destruct_rel_by_assumption env_relΓAAEq).
        simplify_evals. mauto.
      }
      deex. handle_per_univ_elem_irrel.
      eapply glu_univ_elem_resp_per_univ with (a':=m) in H57 as H'; mauto.
      handle_functional_glu_univ_elem.
      eapply glu_univ_elem_trm_resp_typ_exp_eq; eauto.
      eapply glu_univ_elem_trm_resp_exp_eq; eauto.
    - eexists; split; mauto 3.
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
      + intros Δ' τ w **.
        assert {{ ⊢ Δ' }} by mauto 3.
        assert {{ Δ' ⊢s τ : Δ }} by mauto 3.
        assert {{ Δ' ⊢s σ∘τ : Γ }} by mauto 3.
        assert {{ Δ' ⊢s σ∘τ ® ρ ∈ SbΓ }} by (eapply glu_ctx_env_sub_monotone; eassumption).
        assert {{ Δ', A[σ∘τ] ⊢s q (σ∘τ) ® ρ ↦ ⇑! a (length Δ') ∈ SbΓA }}. {
          assert {{ Δ', A[σ∘τ] ⊢ A[(σ∘τ)][Wk] ≈ A[Wk][q (σ∘τ)] : Type@i }}. { 
            symmetry.
            eapply (@wf_exp_eq_eqrec_Awkqσ_Aσwk _ _ Γ); mauto 3.
          }
          unfold SbΓA. eapply cons_glu_sub_pred_helper; mauto 3. 
          - eapply glu_ctx_env_sub_monotone; mauto.
          - eapply glu_univ_elem_trm_resp_typ_exp_eq; eauto.
            eapply glu_univ_elem_trm_resp_exp_eq; eauto.
            eapply var0_glu_elem; mauto 3. 
            eapply glu_univ_elem_typ_resp_exp_eq with (A:={{{ A[σ][τ] }}}); mauto 3.
            eapply glu_univ_elem_typ_monotone; mauto 3.
            mauto. mauto 4.
        }
        assert {{ Δ', A[σ∘τ], A[Wk][σ∘τ], (Eq A[Wk∘Wk] #1 #0)[σ∘τ] ⊢s q (q (q (σ∘τ))) ® ρ ↦ ⇑! a (length Δ') ↦ ⇑! a (S (length Δ')) ↦ ⇑! (Eq a (⇑! a (length Δ')) (⇑! a (S (length Δ')))) (S (S (length Δ'))) ∈ SbΓAAEq }}. {
          admit.
        }
        clear_glu_ctx Δ.
        destruct_glu_rel_exp_with_sub.
        simplify_evals.
        match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
        apply_predicate_equivalence. 
        match_by_head read_ne ltac:(fun H => directed inversion_clear H).
        handle_functional_glu_univ_elem.
        inversion_clear_by_head eq_glu_exp_pred.
        destruct_glu_eq.
        unfold univ_glu_exp_pred' in *.
        destruct_conjs.
        clear_dups.
        rename Γ0 into Δ'.
        assert {{ Δ' ⊢ A[σ∘τ] ® glu_typ_top i a}} as []. {
          eapply realize_glu_typ_top; mauto 3.
          eapply glu_univ_elem_typ_resp_exp_eq; mauto.
        }
        assert {{ Δ' ⊢ M1[σ∘τ] : A[σ∘τ] ® m1 ∈ glu_elem_top i a }} as [] by (eapply realize_glu_elem_top; eassumption).
        assert {{ Δ' ⊢ M2[σ∘τ] : A[σ∘τ] ® m2 ∈ glu_elem_top i a }} as [] by (eapply realize_glu_elem_top with (El:=El); eauto).
        assert {{ Δ' , A[σ∘τ] ⊢ BR[q (σ∘τ)] : B[Id,,#0,,refl A[Wk] #0][q (σ∘τ)] ® m5 ∈ glu_elem_top j m }} as [] by (eapply realize_glu_elem_top with (El:=El5); eauto).
        assert {{ Δ', A[σ∘τ], A[Wk][σ∘τ], (Eq A[Wk∘Wk] #1 #0)[σ∘τ] ⊢ B[q (q (q (σ∘τ)))] ® glu_typ_top j m4 }} as [] by (eapply realize_glu_typ_top; eauto).
        assert {{ Δ' ⊢ B[Id,,M1,,M2,,N][σ][τ] ≈ B[Id,,M1,,M2,,N][σ∘τ] : Type@j }} by mauto 3.
        assert {{ Δ' ⊢ eqrec N as Eq A M1 M2 return B | refl -> BR end[σ][τ] ≈ eqrec N as Eq A M1 M2 return B | refl -> BR end[σ∘τ] : B[Id,,M1,,M2,,N][σ∘τ] }} by mauto 4.
        rewrite H140. rewrite H141.
        eapply (@wf_exp_eq_eqrec_cong_sub _ _ Γ); fold nf_to_exp; fold ne_to_exp; eauto.
    }
  econstructor; mauto.
Admitted.

#[export]
  Hint Resolve glu_rel_eq_eqrec : mctt.
