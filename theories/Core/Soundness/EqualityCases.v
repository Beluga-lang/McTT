From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Realizability.
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
  assert {{ Γ ⊢ A : Type@x }} by mauto.
  eexists; split; eauto.
  exists x; intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 4.
  apply_glu_rel_judge.
  saturate_glu_typ_from_el.
  deepexec glu_univ_elem_per_univ ltac:(fun H => pose proof H).
  match_by_head per_univ ltac:(fun H => destruct H).
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
  assert {{ ⊩ Γ , A, A[Wk] }} by mauto.
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

  repeat invert_glu_rel1.
  handle_functional_glu_univ_elem.
  saturate_glu_typ_from_el.
  unify_glu_univ_lvl i.

  deepexec (glu_univ_elem_per_univ i) ltac:(fun H => pose proof H).
  match_by_head per_univ ltac:(fun H => destruct H).
  do 2 deepexec (glu_univ_elem_per_elem i) ltac:(fun H => pose proof H; fail_at_if_dup ltac:(4)).
  saturate_glu_info.

  eassert (exists mr, {{ ⟦ eqrec N as Eq A M1 M2 return B | refl -> BR end ⟧ ρ ↘ mr }}
                 /\ {{ Γ0 ⊢ eqrec N as Eq A M1 M2 return B | refl -> BR end[σ] : B[Id,,M1,,M2,,N][σ] ® mr ∈ H77 }}) as [? [? ?]].
  {
    destruct_glu_eq.
    - assert {{ Γ0 ⊢w Id : Γ0 }} as HId by mauto.
      assert {{ Γ0 ⊢ M'' : B1 }} by (gen_presups; trivial).
      pose proof (H99 _ _ HId) as HM''.
      saturate_glu_typ_from_el.
      assert {{ Γ0 ⊢ B1[Id] ≈ B1 : Type@i }} as HrwB1 by mauto 3.
      rewrite HrwB1 in *.
      assert {{ Γ0 ⊢ B1 ≈ A[σ] : Type@i }} as HrwB1' by mauto 4.
      rewrite HrwB1' in *.
      saturate_glu_info.

      assert (SbΓA Γ0 {{{σ ,, M''}}} d{{{ρ ↦ m'}}}).
      {
        match_by_head1 (glu_ctx_env SbΓA) invert_glu_ctx_env.
        apply_equiv_left.
        econstructor; mauto 3; bulky_rewrite.
        admit.
      }
      destruct_glu_rel_exp_with_sub.
      simplify_evals.
      simpl in *.

      eexists; split; mauto 3.
      admit.

    - match_by_head1 per_bot ltac:(fun H => pose proof (H (length Γ0)) as [V [HV _]]).
      assert {{ Γ0 ⊢w Id : Γ0 }} as HId by mauto.
      pose proof (H54 _ _ V HId HV).
      assert {{ Γ0 ⊢ N[σ] ≈ V : (Eq A M1 M2)[σ] }} by admit.

      eexists; split; mauto 3.

      admit.
  }

  econstructor; mauto.


Admitted.

#[export]
  Hint Resolve glu_rel_eq_eqrec : mctt.
