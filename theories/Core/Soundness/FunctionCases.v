From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import FundamentalTheorem UniverseCases.
From Mctt.Core.Soundness Require Import
  ContextCases
  LogicalRelation
  SubstitutionCases
  SubtypingCases
  TermStructureCases
  UniverseCases.
Import Domain_Notations.

Lemma cons_glu_sub_pred_pi_helper : forall {Γ Sb Γ' σ ρ A a i P El Γ'' τ M c},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ Γ' ⊢s σ ® ρ ∈ Sb }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ Γ'' ⊢w τ : Γ' }} ->
    {{ Γ'' ⊢ M : A[σ][τ] ® c ∈ El }} ->
    {{ Γ'' ⊢s σ∘τ,,M ® ρ ↦ c ∈ cons_glu_sub_pred i Γ A Sb }}.
Proof.
  intros.
  assert {{ Γ'' ⊢s σ∘τ ® ρ ∈ Sb }} by (eapply glu_ctx_env_sub_monotone; mauto 3).
  eapply cons_glu_sub_pred_helper; try eassumption.
  assert {{ Γ' ⊢s σ : Γ }} by mauto 2.
  assert {{ Γ'' ⊢s τ : Γ' }} by mauto 2.
  enough {{ Γ'' ⊢ A[σ∘τ] ≈ A[σ][τ] : Type@i }} as ->; mauto 3.
Qed.

#[local]
Hint Resolve cons_glu_sub_pred_pi_helper : mctt.

Lemma glu_rel_exp_pi : forall {Γ A B i},
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ, A ⊩ B : Type@i }} ->
    {{ Γ ⊩ Π A B : Type@i }}.
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
  assert {{ Γ ⊨ Π A B : Type@i }} as [env_relΓ]%rel_exp_of_typ_inversion1 by mauto 3 using completeness_fundamental_exp.
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
  econstructor; mauto 3; intros Δ' τ **;
    assert {{ Δ' ⊢s τ : Δ }} by mauto 2.
  - assert {{ Δ' ⊢s σ ∘ τ ® ρ ∈ SbΓ }} by (eapply glu_ctx_env_sub_monotone; eassumption).
    assert {{ Δ' ⊢s σ ∘ τ : Γ }} by mauto 2.
    assert (glu_rel_exp_with_sub (S i) Δ' A {{{ Type @ i }}} {{{ σ ∘ τ }}} ρ) as [] by mauto 4.
    simplify_evals.
    match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
    apply_predicate_equivalence.
    unfold univ_glu_exp_pred' in *.
    destruct_conjs.
    handle_functional_glu_univ_elem.
    autorewrite with mctt.
    eassumption.
  - assert {{ Dom ρ ↦ m ≈ ρ ↦ m ∈ env_relΓA }} as HrelΓA by (apply_relation_equivalence; mautosolve 2).
    apply_relation_equivalence.
    (on_all_hyp: fun H => destruct (H _ _ HrelΓA)).
    destruct_by_head per_univ.
    functional_eval_rewrite_clear.
    match goal with
    | _: {{ ⟦ B ⟧ ρ ↦ m ↘ ^?a }} |- _ =>
        rename a into b
    end.
    assert {{ Δ' ⊢ M : A[σ][τ] }} by mauto 3 using glu_univ_elem_trm_escape.
    assert {{ DG b ∈ glu_univ_elem i ↘ OP m equiv_m ↘ OEl m equiv_m }} by mauto 2.
    erewrite <- @sub_decompose_q_typ; mauto 3.
    assert {{ Δ' ⊢s (σ∘τ),,M ® ρ ↦ m ∈ cons_glu_sub_pred i Γ A SbΓ }} as Hconspred by mauto 2.
    (on_all_hyp: fun H => destruct (H _ _ _ Hconspred)).
    simplify_evals.
    match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
    apply_predicate_equivalence.
    unfold univ_glu_exp_pred' in *.
    destruct_conjs.
    handle_functional_glu_univ_elem.
    eassumption.
Qed.

#[export]
Hint Resolve glu_rel_exp_pi : mctt.

Lemma glu_rel_exp_of_pi : forall {Γ M A B i Sb},
    {{ EG Γ ∈ glu_ctx_env ↘ Sb }} ->
    {{ Γ ⊨ Π A B : Type@i }} ->
    (forall Δ σ ρ,
        {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
        exists a m,
          {{ ⟦ A ⟧ ρ ↘ a }} /\
            {{ ⟦ M ⟧ ρ ↘ m }} /\
            forall (P : glu_typ_pred) (El : glu_exp_pred), {{ DG Π a ρ B ∈ glu_univ_elem i ↘ P ↘ El }} -> {{ Δ ⊢ M[σ] : (Π A B)[σ] ® m ∈ El }}) ->
    {{ Γ ⊩ M : Π A B }}.
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

Lemma glu_rel_exp_fn_helper : forall {Γ M A B i},
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ, A ⊩ B : Type@i }} ->
    {{ Γ, A ⊩ M : B }} ->
    {{ Γ ⊩ λ A M : Π A B }}.
Proof.
  intros * HA HB HM.
  assert {{ ⊩ Γ }} as [SbΓ] by mauto 3.
  assert {{ Γ ⊢ A : Type@i }} by mauto 3.
  invert_glu_rel_exp HA.
  pose (SbΓA := cons_glu_sub_pred i Γ A SbΓ).
  assert {{ EG Γ, A ∈ glu_ctx_env ↘ SbΓA }} by (econstructor; mauto 3; reflexivity).
  assert {{ Γ, A ⊢ M : B }} by mauto 3.
  invert_glu_rel_exp HM.
  destruct_conjs.
  assert {{ Γ, A ⊢ B : Type@i }} by mauto.
  assert {{ Γ, A ⊨ M : B }} as [env_relΓA] by mauto using completeness_fundamental_exp.
  destruct_conjs.
  pose env_relΓA.
  match_by_head (per_ctx_env env_relΓA) invert_per_ctx_env.
  rename tail_rel into env_relΓ.
  apply_relation_equivalence.
  assert {{ Γ ⊨ Π A B : Type@i }} by mauto using completeness_fundamental_exp.
  eapply glu_rel_exp_of_pi; mauto.
  intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 4.
  assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  destruct_rel_typ.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
  apply_predicate_equivalence.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  handle_functional_glu_univ_elem.
  do 2 eexists; repeat split; mauto.
  intros.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
  handle_per_univ_elem_irrel.
  handle_functional_glu_univ_elem.
  match goal with
  | H : {{ DG a ∈ glu_univ_elem ?i ↘ ?P ↘ ?El }} |- _ =>
      rename P into Pa;
      rename El into Ela
  end.
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
  apply_relation_equivalence.
  assert {{ Δ, A[σ] ⊢ B[q σ] : Type@i }} by mauto 3.
  econstructor; mauto 3; intros.
  - assert {{ Dom ρ ↦ c ≈ ρ ↦ c' ∈ env_relΓA }} as HrelΓA by (apply_relation_equivalence; mautosolve 2).
    destruct_rel_mod_eval.
    apply_relation_equivalence.
    (on_all_hyp: fun H => destruct (H _ _ HrelΓA) as [? [[] []]]).
    handle_per_univ_elem_irrel.
    econstructor; mauto 3.
  - eapply glu_univ_elem_typ_monotone; mauto 3.
  - assert {{ Dom ρ ↦ n ≈ ρ ↦ n ∈ env_relΓA }} as HrelΓA by (apply_relation_equivalence; mautosolve 2).
    destruct_rel_mod_eval.
    apply_relation_equivalence.
    (on_all_hyp: fun H => destruct (H _ _ HrelΓA) as [? [[] []]]).
    handle_per_univ_elem_irrel.
    eexists; split; mauto 3.
    match goal with
    | _: {{ ⟦ B ⟧ ρ ↦ n ↘ ^?a }} |- _ =>
        rename a into b
    end.
    assert {{ DG b ∈ glu_univ_elem i ↘ OP n equiv_n ↘ OEl n equiv_n }} by mauto 3.
    assert {{ Δ0 ⊢s σ0 : Δ }} by mauto 3.
    assert {{ Δ0 ⊢ N : A[σ][σ0] }} by mauto 2 using glu_univ_elem_trm_escape.
    erewrite <- @sub_decompose_q_typ; mauto 2.
    assert {{ Δ0 ⊢ (λ A M)[σ][σ0] N ≈ M[(σ∘σ0),,N] : B[σ∘σ0,,N] }} as ->.
    {
      assert {{ Δ0 ⊢s σ∘σ0 : Γ }} by mauto 3.
      assert {{ Δ0, A[σ∘σ0] ⊢ M[q (σ∘σ0)] : B[q (σ∘σ0)] }} by mauto 3.
      assert {{ Δ0 ⊢ (λ A M)[σ][σ0] ≈ (λ A M)[σ∘σ0] : (Π A B)[σ∘σ0] }} by (symmetry; mauto 3).
      assert {{ Δ0 ⊢ (λ A M)[σ][σ0] ≈ (λ A[σ∘σ0] M[q (σ∘σ0)]) : (Π A B)[σ∘σ0] }} by mauto 3.
      assert {{ Δ0 ⊢ (λ A M)[σ][σ0] ≈ (λ A[σ∘σ0] M[q (σ∘σ0)]) : Π A[σ∘σ0] B[q (σ∘σ0)] }} by mauto 3.
      assert {{ Δ0 ⊢ N : A[σ∘σ0] }} by mauto 3.
      assert {{ Δ0 ⊢ (λ A M)[σ][σ0] N ≈ (λ A[σ∘σ0] M[q (σ∘σ0)]) N : B[q (σ∘σ0)][Id,,N] }} by mauto 3.
      assert {{ Δ0 ⊢ (λ A M)[σ][σ0] N ≈ M[q (σ∘σ0)][Id,,N] : B[q (σ∘σ0)][Id,,N] }} by mauto 3.
      transitivity {{{ M[q (σ∘σ0)][Id,,N] }}}; [mauto 3 |].
      assert {{ Δ0 ⊢s Id,,N : Δ0, A[σ∘σ0] }} by mauto 3.
      assert {{ Δ0, A[σ∘σ0] ⊢s q (σ∘σ0) : Γ, A }} by mauto 2.
      assert {{ Δ0 ⊢s q (σ∘σ0)∘(Id,,N) ≈ σ∘σ0,,N : Γ, A }} by mauto 2.
      assert {{ Δ0 ⊢ B[q (σ∘σ0)∘(Id,,N)] ≈ B[σ∘σ0,,N] : Type@i }} as <- by mauto 2.
      transitivity {{{ M[q (σ∘σ0)∘(Id,,N)] }}}; mauto 3.
    }
    assert {{ Δ0 ⊢ N : A[σ][σ0] ® n ∈ Ela }} by mauto 3.
    assert {{ Δ0 ⊢s (σ∘σ0),,N ® ρ ↦ n ∈ SbΓA }} as HSbΓA by (unfold SbΓA; mauto 2).
    (on_all_hyp: fun H => destruct (H _ _ _ HSbΓA)).
    simplify_evals.
    match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
    handle_functional_glu_univ_elem.
    mauto 3.
Qed.

Lemma glu_rel_exp_fn : forall {Γ M A B i},
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ, A ⊩ M : B }} ->
    {{ Γ ⊩ λ A M : Π A B }}.
Proof.
  intros * HA HM.
  assert (exists j, {{ Γ, A ⊩ B : Type@j }}) as [j] by mauto 3.
  assert {{ ⊩ Γ }} by mauto 3.
  assert (i <= max i j) by lia.
  assert {{ Γ ⊢ Type@i ⊆ Type@(max i j) }} by mauto 4.
  assert {{ Γ ⊩ A : Type@(max i j) }} by mauto 3.
  assert {{ ⊩ Γ, A }} by mauto 3.
  assert (j <= max i j) by lia.
  assert {{ Γ, A ⊢ Type@j ⊆ Type@(max i j) }} by mauto 4.
  assert {{ Γ, A ⊩ B : Type@(max i j) }} by mauto 3.
  mauto 3 using glu_rel_exp_fn_helper.
Qed.

#[export]
Hint Resolve glu_rel_exp_fn : mctt.

Lemma glu_rel_exp_app_helper : forall {Γ M N A B i},
    {{ Γ ⊩ A : Type@i }} ->
    {{ Γ, A ⊩ B : Type@i }} ->
    {{ Γ ⊩ M : Π A B }} ->
    {{ Γ ⊩ N : A }} ->
    {{ Γ ⊩ M N : B[Id,,N] }}.
Proof.
  intros * HA HB HM HN.
  assert {{ ⊩ Γ }} as [SbΓ] by mauto 3.
  assert {{ Γ ⊩ Π A B : Type@i }} by mauto 4.
  assert {{ Γ ⊢ N : A }} by mauto 2.
  invert_glu_rel_exp HN.
  assert {{ Γ ⊢ A : Type@i }} by mauto 3.
  invert_glu_rel_exp HA.
  pose (SbΓA := cons_glu_sub_pred i Γ A SbΓ).
  assert {{ EG Γ, A ∈ glu_ctx_env ↘ SbΓA }} by (econstructor; mauto 3; reflexivity).
  assert {{ Γ, A ⊢ B : Type@i }} by mauto 2.
  invert_glu_rel_exp HB.
  destruct_conjs.
  assert {{ Γ ⊢ M : Π A B }} by mauto 2.
  invert_glu_rel_exp HM.
  eexists; split; [eassumption |].
  eexists.
  intros.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
  apply_predicate_equivalence.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  handle_functional_glu_univ_elem.
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
  inversion_clear_by_head pi_glu_exp_pred.
  match goal with
  | _: glu_univ_elem i ?P' ?El' a,
      _: {{ ⟦ A ⟧ ρ ↘ ^?a' }},
      _: {{ ⟦ N ⟧ ρ ↘ ^?n' }} |- _ =>
      rename a' into a;
      rename n' into n;
      rename P' into Pa;
      rename El' into Ela
  end.
  assert {{ Dom a ≈ a ∈ per_univ i }} as [] by mauto 3.
  handle_per_univ_elem_irrel.
  assert {{ Dom n ≈ n ∈ in_rel }} by (eapply glu_univ_elem_per_elem; revgoals; eassumption).
  (on_all_hyp: destruct_rel_by_assumption in_rel).
  simplify_evals.
  match goal with
  | _: {{ ⟦ B ⟧ ρ ↦ n ↘ ^?b' }},
      _: {{ $| m & n |↘ ^?mn' }} |- _ =>
      rename b' into b;
      rename mn' into mn
  end.
  eapply mk_glu_rel_exp_with_sub''; mauto 3.
  intros.
  match_by_head1 (in_rel n n) ltac:(fun H => rename H into equiv_n).
  assert {{ DG b ∈ glu_univ_elem i ↘ OP n equiv_n ↘ OEl n equiv_n }} by mauto 3.
  handle_functional_glu_univ_elem.
  assert {{ Δ ⊢w Id : Δ }} by mauto 3.
  assert {{ Δ ⊢ IT[Id] ® Pa }} by mauto 2.
  assert {{ Δ ⊢ IT[Id] : Type@i }} by (eapply glu_univ_elem_univ_lvl; revgoals; eassumption).
  assert {{ Δ ⊢ IT : Type@i }} by mauto 2.
  assert {{ Δ ⊢ IT[Id] ≈ A[σ] : Type@i }} as HAeq by (eapply glu_univ_elem_typ_unique_upto_exp_eq'; revgoals; eassumption).
  assert {{ Δ ⊢ N[σ] : IT[Id] ® n ∈ Ela }} by (rewrite HAeq; eassumption).
  assert (exists mn : domain, {{ $| m & n |↘ mn }} /\ {{ Δ ⊢ M[σ][Id] N[σ] : OT[Id,,N[σ]] ® mn ∈ OEl n equiv_n }}) as [] by mauto 2.
  destruct_conjs.
  functional_eval_rewrite_clear.
  assert {{ Δ ⊢ N[σ] : A[σ][Id] ® n ∈ Ela }} by (autorewrite with mctt; eassumption).
  assert {{ Δ ⊢s σ∘Id,,N[σ] ® ρ ↦ n ∈ SbΓA }} as Hcons by (unfold SbΓA; mauto 2).
  (on_all_hyp: destruct_glu_rel_by_assumption SbΓA).
  simplify_evals.
  match_by_head1 glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
  apply_predicate_equivalence.
  unfold univ_glu_exp_pred' in *.
  destruct_conjs.
  handle_functional_glu_univ_elem.
  assert {{ Δ ⊢s σ : Γ }} by mauto 2.
  assert {{ Δ ⊢ N[σ] : A[σ] }} by mauto 2.
  assert {{ Δ ⊢ B[Id,,N][σ] ≈ B[σ,,N[σ]] : Type@i }} as -> by mauto 2.
  assert {{ Δ ⊢ (M N)[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }} as -> by mauto 2.
  assert {{ Δ ⊢ M[σ][Id] N[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }} as <-.
  {
    assert {{ Δ ⊢ M[σ][Id] ≈ M[σ] : (Π A B)[σ] }} by mauto 2.
    assert {{ Δ ⊢ M[σ][Id] ≈ M[σ] : Π A[σ] B[q σ] }} by mauto 3.
    assert {{ Δ ⊢ M[σ][Id] N[σ] ≈ M[σ] N[σ] : B[q σ][Id,,N[σ]] }} as HGoal' by mauto 3.
    autorewrite with mctt in HGoal'.
    eassumption.
  }
  assert {{ Δ ⊢ B[σ,,N[σ]] ≈ B[(σ∘Id),,N[σ]] : Type@i }} as ->
      by (eapply exp_eq_sub_cong_typ2'; try eassumption; econstructor; mauto 3).
  assert {{ Δ ⊢ B[(σ∘Id),,N[σ]] ≈ OT[Id,,N[σ]] : Type@i }} as ->.
  {
    assert {{ Δ ⊢ OT[Id,,N[σ]] ® OP n equiv_n }} by (eapply glu_univ_elem_trm_typ; eassumption).
    eapply glu_univ_elem_typ_unique_upto_exp_eq'; revgoals; eassumption.
  }
  eassumption.
Qed.

Lemma glu_rel_exp_app : forall {Γ M N A B i},
    {{ Γ, A ⊩ B : Type@i }} ->
    {{ Γ ⊩ M : Π A B }} ->
    {{ Γ ⊩ N : A }} ->
    {{ Γ ⊩ M N : B[Id,,N] }}.
Proof.
  intros * HB HM HN.
  assert {{ ⊩ Γ, A }} as [SbΓA] by mauto 3.
  match_by_head (glu_ctx_env SbΓA) invert_glu_ctx_env.
  apply_predicate_equivalence.
  rename i0 into j.
  rename TSb into SbΓ.
  assert {{ Γ, A ⊩ B : Type@i }} by mauto 4.
  assert {{ Γ ⊩ A : Type@j }} by (eexists; intuition; eexists; mauto 4).
  assert {{ ⊩ Γ }} by mauto 2.
  assert (j <= max i j) by lia.
  assert {{ Γ ⊢ Type@j ⊆ Type@(max i j) }} by mauto 3.
  assert {{ Γ ⊩ A : Type@(max i j) }} by mauto 3.
  assert {{ ⊩ Γ, A }} by mauto 2.
  assert (i <= max i j) by lia.
  assert {{ Γ, A ⊢ Type@i ⊆ Type@(max i j) }} by mauto 4.
  assert {{ Γ, A ⊩ B : Type@(max i j) }} by mauto 3.
  mauto 2 using glu_rel_exp_app_helper.
Qed.

#[export]
Hint Resolve glu_rel_exp_app : mctt.
