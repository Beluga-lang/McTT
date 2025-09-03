From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Soundness Require Import
  ContextCases
  LogicalRelation
  SubstitutionCases
  SubtypingCases
  TermStructureCases
  UniverseCases
  FunctionCases.
Import Domain_Notations.

Lemma glu_rel_exp_sigma : forall {Γ A B i},
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ, A ⊩ B : Type@i }} ->
    {{ Γ ⊩ Σ A B : Type@i }}.
Proof.
  intros * HA HB.
  assert {{ ⊩ Γ }} as [SbΓ] by mauto.
  assert {{ Γ ⊢ A : Type@i }} by mauto.
  invert_glu_rel_exp HA.
  assert {{ EG Γ, A ∈ glu_ctx_env ↘ cons_glu_sub_pred i Γ A SbΓ }} by (econstructor; mauto; reflexivity).
  assert {{ Γ, A ⊢ B : Type@i }} by mauto.
  invert_glu_rel_exp HB.
  eapply glu_rel_exp_of_typ; mauto 3.
  intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 4.
  split; mauto 3.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
  handle_functional_glu_univ_elem.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  rename m into a.
  assert {{ Γ ⊨ Σ A B : Type@i }} as [env_relΓ]%rel_exp_of_typ_inversion1 by mauto 3 using completeness_fundamental_exp.
  assert {{ Γ, A ⊨ B : Type@i }} as [env_relΓA]%rel_exp_of_typ_inversion1 by mauto 3 using completeness_fundamental_exp.
  destruct_conjs.
  match_by_head1 (per_ctx_env env_relΓA) invert_per_ctx_env.
  pose env_relΓA.
  assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  simplify_evals.
  eexists; repeat split; mauto.
  intros.
  match_by_head1 glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
  handle_per_univ_elem_irrel.
  handle_functional_glu_univ_elem.
  econstructor; mauto 4; intros Δ' τ **;
    assert {{ Δ' ⊢s τ : Δ }} by mauto 2.
  + assert {{ Dom ρ ↦ m ≈ ρ ↦ m ∈ env_relΓA }} as HrelΓA by (apply_relation_equivalence; mautosolve 2).
    apply_relation_equivalence.
    (on_all_hyp: fun H => destruct (H _ _ HrelΓA)).
    unfold per_univ in *. deex.
    functional_eval_rewrite_clear.
    match goal with
    | _: {{ ⟦ B ⟧ ρ ↦ m ↘ ^?a }} |- _ =>
        rename a into b
    end. 
    assert {{ Δ' ⊢ M : A[σ][τ] }} by mauto 3 using glu_univ_elem_trm_escape.
    assert {{ DG b ∈ glu_univ_elem i ↘ SP m equiv_m ↘ SEl m equiv_m }} by mauto 2.
    erewrite <- @sub_decompose_q_typ; mauto 3.
    assert {{ Δ' ⊢s (σ∘τ),,M ® ρ ↦ m ∈ cons_glu_sub_pred i Γ A SbΓ }} as Hconspred by mauto 2.
    (on_all_hyp: fun H => destruct (H _ _ _ Hconspred)).
    simplify_evals.
      match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
    apply_predicate_equivalence.
    unfold univ_glu_exp_pred' in *.
    destruct_conjs.
    handle_functional_glu_univ_elem. 
    auto.
Qed.

#[export]
Hint Resolve glu_rel_exp_sigma : mctt.

Lemma glu_rel_exp_of_sigma : forall {Γ M A B i Sb},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ Γ ⊨ Σ A B : Type@i }} ->
    (forall Δ σ ρ,
        {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
        exists a m,
          {{ ⟦ A ⟧ ρ ↘ a }} /\
            {{ ⟦ M ⟧ ρ ↘ m }} /\
            forall (P : glu_typ_pred) (El : glu_exp_pred), {{ DG Σ a ρ B ∈ glu_univ_elem i ↘ P ↘ El }} -> 
              {{ Δ ⊢ M[σ] : (Σ A B)[σ] ® m ∈ El }}) ->
    {{ Γ ⊩ M : Σ A B }}.
Proof.
  intros * ? [env_relΓ] Hbody.
  destruct_conjs.
  eexists; split; mauto 3.
  eexists; intros.
  edestruct Hbody as [? [? [? []]]]; mauto 3.
  assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body_nouip.
  destruct_by_head rel_exp.
  destruct_conjs.
  simplify_evals.
  mauto 4.
Qed.

Lemma exp_eq_elim_q_compse : forall {Γ σ Δ τ Δ' M A B i},
    {{ Γ ⊢s τ : Δ }} ->
    {{ Δ ⊢s σ : Δ' }} ->
    {{ Δ', A ⊢ B : Type@i }} ->
    {{ Δ ⊢ M : A[σ] }} ->
    {{ Γ ⊢ B[q σ][τ,,M[τ]] ≈ B[σ∘τ,,M[τ]] : Type@i }}.
Proof.
  intros.
  assert (exists j, {{ Δ' ⊢ A : Type@j }}) by mauto. destruct_all.  
  assert {{ Δ ⊢ A[σ] : Type@j }} by mauto 3.
  assert {{ ⊢ Δ, A[σ] }} by mauto 3.  
  symmetry; eapply @exp_eq_compose_typ_twice with 
    (Ψ:= {{{ Δ', A }}}) (Δ:={{{ Δ, A[σ] }}}); mauto 3.
  etransitivity ; [ |symmetry; eapply wf_sub_eq_extend_compose ]; mauto 3.
  eapply wf_sub_eq_extend_cong; mauto 3.
  transitivity {{{ σ∘(Wk∘(τ,,M[τ])) }}}; mauto 3.
  eapply wf_sub_eq_compose_cong; [| mauto 3].
  symmetry; eapply wf_sub_eq_p_extend; mauto 3.
  symmetry; eapply wf_sub_eq_compose_assoc; mauto 3.
  symmetry. eapply wf_exp_eq_conv'; 
    [ eapply wf_exp_eq_var_0_sub | ]; mauto 3.
Qed.

Lemma glu_rel_exp_pair : forall {Γ M N A B i},
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ, A ⊩ B : Type@i }} ->
    {{ Γ ⊩ M : A }} ->
    {{ Γ ⊩ N : B[Id,,M] }} ->
    {{ Γ ⊩ ⟨ M : A ; N : B ⟩ : Σ A B }}.
Proof.
  intros * HA HB HM HN.
  assert {{ ⊩ Γ }} as [SbΓ] by mauto 3.
  assert {{ Γ ⊩ Σ A B : Type@i }} by mauto 4.
  assert {{ Γ ⊢ M : A }} by mauto 2.
  assert {{ Γ ⊢ N : B[Id,,M]}} by mauto 2.
  assert {{ Γ ⊢ A : Type@i }} by mauto 3.
  assert {{ Γ ⊩s Id,,M : Γ, A }} by (eapply glu_rel_sub_extend; mauto 3; bulky_rewrite).
  assert {{ Γ ⊩ B[Id,,M] : Type@i }}. {
    assert {{ Γ ⊢ A ⊆ A[Id] }} by mauto 4.
    mauto.
  }
  invert_glu_rel_exp HM.
  invert_glu_rel_exp HN.
  invert_glu_rel_exp HA.
  pose (SbΓA := cons_glu_sub_pred i Γ A SbΓ).
  assert {{ EG Γ, A ∈ glu_ctx_env ↘ SbΓA }} by (econstructor; mauto 3; reflexivity).
  assert {{ Γ, A ⊢ B : Type@i }} by mauto 2.
  invert_glu_rel_exp HB.
  destruct_conjs.
    
  eapply glu_rel_exp_of_sigma; mauto 3.
  - eapply completeness_fundamental_exp; mauto 3.
  - intros.
    destruct_glu_rel_exp_with_sub.
    simplify_evals.
    match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
    apply_predicate_equivalence.
    unfold univ_glu_exp_pred' in *.
    destruct_conjs.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    handle_functional_glu_univ_elem.
    inversion_clear_by_head sigma_glu_exp_pred.
    match goal with
    | _: glu_univ_elem i ?P' ?El' ?a',
      _: glu_univ_elem i ?P1' ?El1' ?b',
        _: {{ ⟦ A ⟧ ρ ↘ ^?a' }}, _: {{ ⟦ N ⟧ ρ ↘ ^?n' }},
        _: {{ ⟦ M ⟧ ρ ↘ ^?m' }}, _: {{ ⟦ B ⟧ ρ ↦ ^?m' ↘ ^?b' }} 
        |- _ =>
        rename a' into a; rename n' into n;
        rename b' into b; rename m' into m;
        rename P' into Pa; rename El' into Ela;
        rename P1' into Pb; rename El1' into Elb
    end.
    do 2 eexists; repeat split; mauto 3.
    intros.
    invert_glu_univ_elem H18.
    handle_functional_glu_univ_elem.
    match goal with
    | _: glu_univ_elem i ?P' ?El' ?a' |- _ =>
        rename P' into Pa;
        rename El' into Ela
    end.
    assert (equiv_m : {{ Dom m ≈ m ∈ fst_rel }}). {
      eapply glu_univ_elem_per_elem with (P:=Pa) (El:=Ela); mauto 3. 
    }
    assert {{ Δ ⊢ fst (⟨ M : A ; N : B ⟩)[σ] ≈ M[σ] : A[σ] }}. {
      assert {{ Δ ⊢ (fst (⟨ M : A ; N : B ⟩))[σ] ≈ fst (⟨ M : A ; N : B ⟩)[σ] : A[σ] }} as <- by (eapply wf_exp_eq_fst_sub; mauto 3).
      eapply wf_exp_eq_sub_cong; mauto 3.
    }
    assert {{ Δ ⊢ fst (⟨ M : A ; N : B ⟩)[σ] : A[σ] }} by (gen_presups; mauto 3).
    eapply mk_sigma_glu_exp_pred with (equiv_m:=equiv_m); mauto 3.
    + eapply wf_exp_sub; mauto.
    + invert_per_univ_elem H24. rewrite H26.
      destruct_rel_mod_eval. simplify_evals.
      eapply mk_rel_mod_proj with (equiv_b_b':=equiv_m); mauto 3.
      eapply glu_univ_elem_per_elem  with (P:=Pb) (El:=Elb) (a:=b); mauto 3.
    + intros.
      invert_per_univ_elem H24. destruct_rel_mod_eval. simplify_evals.  
      rename a0 into b'.
      assert {{ DG b' ∈ glu_univ_elem i ↘ SP m' equiv_m' ↘ SEl m' equiv_m' }} by mauto 3.
      assert {{ Δ0 ⊢s σ0 : Δ }} by mauto 3.
      assert {{ Δ0 ⊢s (σ∘σ0),,M' ® ρ ↦ m' ∈ SbΓA }} as HSbΓA by (unfold SbΓA; mauto 2).
      (on_all_hyp: fun H => destruct (H _ _ _ HSbΓA)).
      simplify_evals.
      match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
      destruct_all.
      unfold univ_glu_exp_pred' in *.
      destruct_all. handle_functional_glu_univ_elem.
      destruct_all. handle_functional_glu_univ_elem.
      eapply glu_univ_elem_typ_resp_exp_eq; eauto.
      eapply sub_decompose_q_typ; mauto 3.
      eapply glu_univ_elem_trm_escape with (El:=Ela); mauto 3.
    + intros.
      eapply glu_univ_elem_trm_resp_exp_eq; mauto 3.
    + assert {{ DG b ∈ glu_univ_elem i ↘ SP m equiv_m ↘ SEl m equiv_m }} by mauto 3.
      (* assert {{ Δ ⊢s σ0 : Δ }} by mauto 3. *)
      assert {{ Δ ⊢s σ,,M[σ] ® ρ ↦ m ∈ SbΓA }} as HSbΓA. {
        unfold SbΓA; mauto 2.
      }
      (on_all_hyp: fun H => destruct (H _ _ _ HSbΓA)).
      simplify_evals.
      match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
      rewrite H29 in H30.
      unfold univ_glu_exp_pred' in *.
      destruct_all. handle_functional_glu_univ_elem.
      assert {{ Δ ⊢ B[q σ][Id,,(fst (⟨ M : A ; N : B ⟩)[σ])] ≈ B[Id,,M][σ] : Type@i }} as ->.
      {
        assert {{ Δ , A[σ] ⊢ B[q σ] : Type@i }}. {
          eapply wf_conv'; [eapply wf_exp_sub | ]; mauto 3.
          econstructor; mauto 3.
        }
        transitivity {{{ B[σ,,M[σ]] }}}.
        etransitivity; [eapply exp_eq_elim_sub_rhs_typ | ]; mauto 3.
        eapply wf_eq_typ_exp_sub_cong; mauto 3.
        eapply wf_sub_eq_extend_cong; mauto 3.
        eapply exp_eq_compose_typ_twice; mauto 3.
        etransitivity; [|symmetry; eapply wf_sub_eq_extend_compose]; mauto 3.
        eapply wf_sub_eq_extend_cong; mauto 3. symmetry; mauto 3. 
      }
      assert {{ Δ ⊢ (snd (⟨ M : A ; N : B ⟩)[σ]) ≈ N[σ] : B[Id,,M][σ] }} as ->. 
      {
        assert {{ Δ ⊢ B[σ,,fst (⟨ M : A ; N : B ⟩)[σ]] ≈ B[Id,,M][σ] : Type@i }}. {
          transitivity {{{B[σ,, M[σ]]}}}.
          eapply exp_eq_sub_cong_typ2; mauto 3.
          eapply wf_sub_eq_extend_cong; mauto 3.
          symmetry; eapply exp_eq_elim_sub_lhs_typ_gen; mauto 3.
        } 
        rewrite <- H9.
        etransitivity; [symmetry; eapply wf_exp_eq_snd_sub | ]; mauto 3.
        rewrite H9.
        eapply wf_exp_eq_sub_cong; mauto 3.
      }
      auto.
Qed.

#[export]
Hint Resolve glu_rel_exp_pair : mctt.

Lemma glu_rel_exp_fst : forall {Γ M A B i},
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ, A ⊩ B : Type@i }} ->
    {{ Γ ⊩ M : Σ A B }} ->
    {{ Γ ⊩ fst M : A }}.
Proof.
  intros * HA HB HM.
  assert {{ ⊩ Γ }} as [SbΓ] by mauto 3.
  assert {{ Γ ⊩ Σ A B : Type@i }} by mauto 4.
  assert {{ Γ ⊢ A : Type@i }} by mauto 3.
  assert {{ Γ ⊢ M : Σ A B }} by mauto 3.
  invert_glu_rel_exp HM.
  invert_glu_rel_exp HA.
  assert {{ Γ, A ⊢ B : Type@i }} by mauto 2.
  eexists; split; mauto 3.
  eexists. intros.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  rename m into a. rename m0 into m.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  apply_predicate_equivalence.
  unfold univ_glu_exp_pred' in *.
  destruct_all. handle_functional_glu_univ_elem.
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).  
  apply_predicate_equivalence.
  dependent destruction H16. simplify_evals.
  econstructor; mauto 3.
  assert (FP Γ0 {{{ FT }}}) by eauto.
  assert {{ Γ0 ⊢ (fst M)[σ] ≈ ((fst M[σ]))[Id] : A[σ] }} as ->.
  {
    transitivity {{{ (fst M)[σ][Id] }}}; mauto 3.
    symmetry; eapply wf_exp_eq_sub_id; mauto 3.
    eapply wf_exp_sub; mauto 3.
    eapply wf_exp_eq_conv'; [eapply wf_exp_eq_sub_cong | ]; mauto 3.
  }
  assert {{ Γ0 ⊢ A[σ] ≈ FT : Type@i }} as -> by mauto 3.
  intuition.
  bulky_rewrite.
Qed.

#[export]
Hint Resolve glu_rel_exp_fst : mctt.

Lemma glu_rel_exp_snd : forall {Γ M A B i},
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ, A ⊩ B : Type@i }} ->
    {{ Γ ⊩ M : Σ A B }} ->
    {{ Γ ⊩ snd M : B[Id,,fst M] }}.
Proof.
  intros * HA HB HM.
  assert {{ ⊩ Γ }} as [SbΓ] by mauto 3.
  assert {{ Γ ⊩ Σ A B : Type@i }} by mauto 4.
  assert {{ Γ ⊢ A : Type@i }} by mauto 3.
  assert {{ Γ ⊢ M : Σ A B }} by mauto 3.
  invert_glu_rel_exp HM.
  invert_glu_rel_exp HA.
  pose (SbΓA := cons_glu_sub_pred i Γ A SbΓ).
  assert {{ EG Γ, A ∈ glu_ctx_env ↘ SbΓA }} by (econstructor; mauto 3; reflexivity).
  assert {{ Γ, A ⊢ B : Type@i }} by mauto 2.
  invert_glu_rel_exp HB.
  destruct_conjs.
  eexists; split; mauto 3.
  eexists. intros.  
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  apply_predicate_equivalence.
  unfold univ_glu_exp_pred' in *.
  destruct_all. handle_functional_glu_univ_elem.
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).  
  apply_predicate_equivalence.
  dependent destruction H17. simplify_evals.
  rename m into a. rename m0 into m.
  destruct_rel_mod_eval. simplify_evals.
  rename a0 into b.
  assert {{ Γ0 ⊢ fst M[σ] : A[σ] }}. {
    eapply wf_fst with (B:={{{B[q σ]}}}) (i:=i); mauto 3.
  }
  assert {{ ⟦ B[Id,,fst M] ⟧ ρ ↘ b }} by mauto 4.
  eapply mk_glu_rel_exp_with_sub with (El:=SEl m1 equiv_m); mauto 3.
  assert {{ Γ0 ⊢w Id : Γ0 }} by mauto.
  assert (FP Γ0 {{{ FT }}}) by eauto.
  assert {{ Γ0 ⊢ (fst M)[σ] ≈ ((fst M[σ]))[Id] : A[σ] }}.
  {
    transitivity {{{ (fst M)[σ][Id] }}}; mauto 3.
    symmetry; eapply wf_exp_eq_sub_id; mauto 3.
    eapply wf_exp_sub; mauto 3.
    eapply wf_exp_eq_conv'; [eapply wf_exp_eq_sub_cong | ]; mauto 3.
  }
  assert {{ Γ0 ⊢ A[σ] ≈ FT : Type@i }} by mauto 3.
  assert {{ Γ0 ⊢s σ,,(fst M[σ]) ® ρ ↦ m1 ∈ SbΓA }} as HSbΓA. {
    unfold SbΓA; mauto 2.
    eapply glu_ctx_env_sub_resp_sub_eq with (σ:={{{(σ,,fst M[σ])∘Id}}}); mauto 3.
    eapply glu_rel_sub_extend_helper; mauto 3.
    eapply glu_ctx_env_sub_resp_sub_eq; mauto 3. symmetry; mauto 3.
    assert {{ Γ0 ⊢ A[σ][Id] ≈ A[σ] : Type@i }} by mauto 3.
    bulky_rewrite.
    econstructor; mauto 3.
  }
  assert (
    FEl Γ0 {{{ FT }}} {{{ (fst M[σ]) }}} m1 /\
    SEl m1 equiv_m Γ0 {{{ ST[Id,,(fst M[σ])] }}} {{{ (snd M[σ]) }}} m2
  ) by intuition.
  destruct_all.
  assert (FEl Γ0 {{{ FT[Id] }}} {{{ (fst M[σ]) }}} m1) by (bulky_rewrite; auto).
  assert (glu_univ_elem i (SP m1 equiv_m) (SEl m1 equiv_m) b) by mauto 3.
  (on_all_hyp: fun H => destruct (H _ _ _ HSbΓA)).
  simplify_evals. rename m0 into b.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem H).
  apply_predicate_equivalence.
  destruct_all. unfold univ_glu_exp_pred' in *. destruct_all.
  handle_functional_glu_univ_elem.
  assert (SP m1 equiv_m Γ0 {{{ ST[Id,,fst M[σ]] }}}) by auto.
  assert {{ Γ0 ⊢ B[σ,,fst M[σ]] ≈ ST[Id,,fst M[σ]] : Type@i }} by mauto 3.
  assert {{ Γ0 ⊢ B[Id,,fst M][σ] ≈  B[σ,,fst M[σ]] : Type@i }}. {
    transitivity {{{B[σ,,(fst M)[σ]]}}}; mauto 3.
    eapply exp_eq_elim_sub_lhs_typ_gen; mauto 3.
    eapply wf_eq_typ_exp_sub_cong; mauto 3.
    eapply wf_sub_eq_extend_cong; mauto 3.
  }
  rewrite H40. rewrite H39. 
  eapply glu_univ_elem_trm_resp_exp_eq; mauto 3.
  rewrite <- H39.
  assert {{ Γ0 ⊢ (snd M[σ]) ≈ snd M[σ] :B[σ,,fst M[σ]] }}. {
    assert {{ Γ0 ⊢ B[q σ][Id,,fst M[σ]] ≈ B[σ,,fst M[σ]] : Type@i }} as <- by mauto 3.
    eapply exp_eq_refl.
    eapply wf_snd with (A:={{{ A[σ] }}}) (i:=i); mauto 3.
  }
  symmetry; eapply wf_exp_eq_snd_sub; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_exp_snd : mctt.
