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
  apply_glu_rel_judge_nouip.
  handle_functional_glu_univ_elem.
  deepexec glu_univ_elem_per_univ ltac:(fun H => pose proof H).
  match_by_head1 per_univ ltac:(fun H => simpl in H; deex_once_in H).
  do 2 deepexec glu_univ_elem_per_elem ltac:(fun H => pose proof H; fail_at_if_dup ltac:(4)).

  eexists; repeat split; mauto.
  - eexists.
    per_univ_elem_econstructor; mauto.
    reflexivity.
  - intros.
    match_by_head1 glu_univ_elem invert_glu_univ_elem.
    handle_functional_glu_univ_elem.
    handle_per_univ_elem_irrel.
    econstructor; mauto 3;
      intros Ψ τ **;
      assert {{ Ψ ⊢s τ : Δ }} by mauto 2;
      assert {{ Ψ ⊢s σ ∘ τ ® ρ ∈ SbΓ }} by (eapply glu_ctx_env_sub_monotone; eassumption);
        assert {{ Ψ ⊢s σ ∘ τ : Γ }} by mauto 2;
        apply_glu_rel_judge_nouip;
        handle_functional_glu_univ_elem.
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
  deepexec glu_univ_elem_per_univ ltac:(fun P => let H := fresh "H" in pose proof P as H; unfold per_univ in H; deex_once_in H).
  deepexec glu_univ_elem_per_elem ltac:(fun H => pose proof H).
  saturate_glu_info.
  eexists; repeat split; mauto.
  - glu_univ_elem_econstructor; mauto 3; reflexivity.
  - econstructor; try econstructor; mautosolve 3.
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

Lemma glu_rel_eq_eqrec_synprop_gen : forall {Γ σ Δ i A},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ, A[σ], A[σ][Wk] ⊢s q (q σ) : Δ, A, A[Wk] }} /\
    {{ Γ, A[σ] ⊢ A[Wk][q σ] ≈ A[σ][Wk] : Type@i }} /\
    {{ Γ, A[σ], A[σ][Wk] ⊢ A[Wk][q σ∘Wk] ≈ A[σ][Wk∘Wk] : Type@i }} /\
    {{ Γ, A[σ], A[σ][Wk] ⊢ (Eq A[Wk∘Wk] #1 #0)[q (q σ)] ≈ Eq A[σ][Wk∘Wk] #1 #0 : Type@i }} /\
    {{ Δ, A ⊢s Id,,#0,,refl A[Wk] #0 : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} /\
    {{ ⊢ Γ, A[σ], A[σ][Wk], (Eq A[Wk∘Wk] #1 #0)[q (q σ)] }} /\
    {{ Δ, A ⊢ (Eq A[Wk∘Wk] #1 #0)[Id,,#0] ≈ Eq A[Wk] #0 #0 : Type@i }} /\
    {{ Γ, A[σ] ⊢ (Eq A[σ][Wk∘Wk] #1 #0)[Id,,#0] ≈ Eq A[σ][Wk] #0 #0 : Type@i }} /\
    {{ Γ, A[σ] ⊢ (Eq A[σ][Wk∘Wk] #0 #0)[Id,,#0] ≈ Eq A[σ][Wk] #0 #0 : Type@i }} /\
    {{ Γ, A[σ] ⊢s Id,,#0,,refl A[σ][Wk] #0 : Γ, A[σ], A[σ][Wk], Eq A[σ][Wk∘Wk] #1 #0 }} /\
    {{ Γ, A[σ], A[σ][Wk], Eq A[σ][Wk∘Wk] #1 #0 ⊢s q (q (q σ)) : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} /\
    {{ Γ, A[σ] ⊢s q (q (q σ))∘(Id,,#0,,refl A[σ][Wk] #0) ≈ (Id,,#0,,refl A[Wk] #0)∘q σ : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} /\
    (forall {M1 M2},
      {{ Γ ⊢ M1 : A[σ] }} ->
      {{ Γ ⊢ M2 : A[σ] }} ->
      {{ Γ ⊢ (Eq A[Wk] #0 #0)[σ,,M1] ≈ Eq A[σ] M1 M1 : Type@i }} /\
      {{ Γ ⊢ (Eq A[σ][Wk∘Wk] #1 #0)[Id,,M1,,M2] ≈ Eq A[σ] M1 M2 : Type@i }} /\
      {{ Γ ⊢ (Eq A[Wk∘Wk] #1 #0)[σ,,M1,,M2] ≈ Eq A[σ] M1 M2 : Type@i }} /\
        (forall {N},
        {{ Γ ⊢ N : Eq A[σ] M1 M2 }} ->
        {{ Γ ⊢s q (q (q σ))∘(Id,,M1,,M2,,N) ≈ (σ,,M1,,M2,,N) : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }})).
Proof.
  intros.
  gen_presups.
  assert {{ ⊢ Δ, A }} by mauto 2.
  assert {{ Δ, A ⊢s Wk : Δ }} by mauto 2.
  assert {{ Δ, A ⊢ A[Wk] : Type@i }} by mauto 2.
  assert {{ ⊢ Δ, A, A[Wk] }} by mauto 2.
  assert {{ Δ, A, A[Wk] ⊢s Wk : Δ, A }} by mauto 2.
  assert {{ Δ, A, A[Wk] ⊢s Wk∘Wk : Δ }} by mauto 2.
  assert {{ Δ, A, A[Wk] ⊢ A[Wk∘Wk] : Type@i }} by mauto 2.
  assert {{ Δ, A, A[Wk] ⊢ Eq A[Wk∘Wk] #1 #0 : Type@i }} by mauto 2.

  assert {{ Γ ⊢ A[σ] : Type@i }} by mauto 2.
  assert {{ ⊢ Γ, A[σ] }} by mauto 2.
  assert {{ Γ, A[σ] ⊢s q σ : Δ, A }} by mauto 2.
  assert {{ Γ, A[σ] ⊢s Wk : Γ }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ A[σ][Wk] : Type@i }} by mauto 2.
  assert {{ ⊢ Γ, A[σ], A[σ][Wk] }} by mauto 2.
  assert {{ Γ, A[σ], A[σ][Wk] ⊢s Wk : Γ, A[σ] }} by mauto 2.
  assert {{ Γ, A[σ], A[σ][Wk] ⊢s Wk∘Wk : Γ }} by mauto 2.
  assert {{ Γ, A[σ], A[σ][Wk] ⊢ A[σ][Wk∘Wk] : Type@i }} by mauto 2.
  assert {{ Γ, A[σ], A[σ][Wk] ⊢ Eq A[σ][Wk∘Wk] #1 #0 : Type@i }} by (econstructor; mauto 2).
  assert {{ Γ, A[σ] ⊢ A[Wk][q σ] ≈ A[σ][Wk] : Type@i }} by mauto 3.
  assert {{ ⊢ Γ, A[σ], A[Wk][q σ] ≈ Γ, A[σ], A[σ][Wk] }} by (econstructor; mauto 3).
  assert {{ Γ, A[σ], A[σ][Wk] ⊢s q (q σ) : Δ, A, A[Wk] }} by mauto 3.
  assert {{ Γ, A[σ], A[σ][Wk] ⊢ A[Wk][q σ∘Wk] : Type@i }} by mauto 3.
  assert {{ Γ, A[σ], A[σ][Wk] ⊢ A[Wk][q σ∘Wk] ≈ A[σ][Wk∘Wk] : Type@i }}.
  {
    transitivity {{{ A[Wk][q σ][Wk] }}}; [mautosolve 3 |].
    transitivity {{{ A[σ][Wk][Wk] }}}; mautosolve 2.
  }
  assert {{ Γ, A[σ], A[σ][Wk] ⊢ A[Wk∘Wk][q (q σ)] ≈ A[σ][Wk∘Wk] : Type@i }}.
  {
    transitivity {{{ A[Wk][q σ∘Wk] }}}; [| eassumption].
    transitivity {{{ A[Wk][Wk][q (q σ)] }}}; [eapply exp_eq_sub_cong_typ1; mautosolve 3 |].
    transitivity {{{ A[Wk][Wk∘q (q σ)] }}}; [mautosolve 2 |].
    eapply exp_eq_sub_cong_typ2'; mautosolve 3.
  }
  assert {{ Γ, A[σ], A[σ][Wk] ⊢ Eq A[σ][Wk∘Wk] #0 #0 : Type@i }} by (econstructor; mauto 2).
  assert {{ Γ, A[σ], A[σ][Wk] ⊢ (Eq A[Wk∘Wk] #1 #0)[q (q σ)] ≈ Eq A[σ][Wk∘Wk] #1 #0 : Type@i }}.
  {
    etransitivity; [econstructor; mautosolve 2 |].
    econstructor; [mautosolve 2 | |].
    - eapply wf_exp_eq_conv'; mauto 3 using exp_eq_var_1_sub_q_sigma.
    - eapply wf_exp_eq_conv'; [econstructor; mauto 2 |].
      + eapply wf_conv'; mauto 2.
      + etransitivity; mauto 2.
  }
  assert {{ ⊢ Γ, A[σ], A[σ][Wk], Eq A[σ][Wk∘Wk] #1 #0 }} by mauto 2.
  assert {{ ⊢ Γ, A[σ], A[σ][Wk], (Eq A[Wk∘Wk] #1 #0)[q (q σ)]}} by (econstructor; mauto 2).
  assert {{ Γ, A[σ], A[σ][Wk], Eq A[σ][Wk∘Wk] #1 #0 ⊢s q (q (q σ)) : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} by (eapply ctxeq_sub; [|eapply sub_q]; mauto 3).
  assert {{ Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 3.
  assert {{ Γ, A[σ] ⊢s Id,,#0 : Γ, A[σ], A[σ][Wk] }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ A[σ][Wk∘Wk][Id,,#0] ≈ A[σ][Wk] : Type@i }}
    by (transitivity {{{ A[σ][Wk][Wk][Id,,#0] }}}; [symmetry |]; mauto 3).

  assert {{ Γ, A[σ] ⊢s Id,,#0,,refl A[σ][Wk] #0 : Γ, A[σ], A[σ][Wk], Eq A[σ][Wk∘Wk] #1 #0 }}.
  {
    econstructor; mauto 2.
    eapply wf_conv'; [econstructor; mautosolve 2 |].
    symmetry.
    etransitivity; [econstructor; mautosolve 3 |].
    econstructor; eauto.
    - eapply wf_exp_eq_conv'; [| mautosolve 2].
      transitivity {{{ #0[Id] }}}; [| mautosolve 2].
      eapply wf_exp_eq_conv'; [econstructor |]; mautosolve 2.
    - eapply wf_exp_eq_conv'; [econstructor; mautosolve 2 |].
      transitivity {{{ A[σ][Wk] }}}; mautosolve 2.
  }
  assert {{ Γ, A[σ] ⊢s q (q σ)∘(Id,,#0) ≈ q σ,,#0 : Δ, A, A[Wk] }}.
  {
    eapply sub_eq_q_sigma_id_extend; mauto 2.
    eapply wf_conv'; mauto 2.
  }
  assert {{ Γ, A[σ] ⊢ #0 : A[σ][Wk∘Wk][Id,,#0] }} by (eapply wf_conv'; mauto 2).
  assert {{ Γ, A[σ] ⊢ #0[Id,,#0] ≈ #0 : A[σ][Wk][Id] }} by (econstructor; mauto 2).
  assert {{ Γ, A[σ] ⊢ #1[Id,,#0] ≈ #0[Id] : A[σ][Wk][Id] }} by (eapply wf_exp_eq_var_S_sub; mauto 2).
  assert {{ Γ, A[σ] ⊢ #1[Id,,#0] ≈ #0[Id] : A[σ][Wk] }} by mauto 3.
  assert {{ Γ, A[σ] ⊢ #1[Id,,#0] ≈ #0 : A[σ][Wk] }} by mauto 3.
  assert {{ Γ, A[σ] ⊢ #0[Id,,#0] ≈ #0 : A[σ][Wk] }} by mauto 3.
  assert {{ Γ, A[σ] ⊢ #1[Id,,#0] ≈ #0 : A[σ][Wk∘Wk][Id,,#0] }} by mauto 3.
  assert {{ Γ, A[σ] ⊢ #0[Id,,#0] ≈ #0 : A[σ][Wk∘Wk][Id,,#0] }} by (eapply wf_exp_eq_conv'; mauto 2).
  assert {{ Γ, A[σ] ⊢ (Eq A[σ][Wk∘Wk] #1 #0)[Id,,#0] ≈ Eq A[σ][Wk] #0 #0 : Type@i }}
    by (etransitivity; econstructor; mauto 2).
  assert {{ Γ, A[σ] ⊢ (Eq A[σ][Wk∘Wk] #0 #0)[Id,,#0] ≈ Eq A[σ][Wk] #0 #0 : Type@i }}
    by (etransitivity; econstructor; mauto 2).
  assert {{ Γ, A[σ] ⊢s (q (q σ)∘Wk)∘(Id,,#0,,refl A[σ][Wk] #0) : Δ, A, A[Wk] }} by (econstructor; mautosolve 3).
  assert {{ Γ, A[σ] ⊢s (q (q σ)∘Wk)∘(Id,,#0,,refl A[σ][Wk] #0) ≈ q (q σ)∘(Id,,#0) : Δ, A, A[Wk] }}.
  {
    transitivity {{{ q (q σ)∘(Wk∘(Id,,#0,,refl A[σ][Wk] #0)) }}}; [mautosolve 3 |].
    econstructor; [| mautosolve 2].
    eapply wf_sub_eq_p_extend with (A:={{{ Eq A[σ][Wk∘Wk] #0 #0 }}}); [mautosolve 2 | mautosolve 2 |].
    eapply wf_conv'; mauto 2.
  }
  assert {{ Γ, A[σ], A[σ][Wk], Eq A[σ][Wk∘Wk] #1 #0 ⊢s Wk : Γ, A[σ], A[σ][Wk] }} by mauto 2.
  assert {{ Γ, A[σ] ⊢s (q (q σ)∘Wk)∘(Id,,#0,,refl A[σ][Wk] #0) ≈ q σ,,#0 : Δ, A, A[Wk] }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ A[σ][Wk∘Wk][Id,,#0] ≈ A[Wk][q σ] : Type@i }} by mauto 3.
  assert {{ Γ, A[σ] ⊢ #0 : A[Wk][q σ] }} by mauto 3.
  assert {{ Γ, A[σ] ⊢ A[Wk∘Wk][q σ,,#0] ≈ A[Wk][q σ] : Type@i }}
    by (transitivity {{{ A[Wk][Wk][q σ,,#0] }}}; [eapply exp_eq_sub_cong_typ1 |]; mauto 3).
  assert {{ Γ, A[σ] ⊢s q σ,,#0 : Δ, A, A[Wk] }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ A[Wk∘Wk][q σ,,#0] : Type@i }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ A[Wk∘Wk][q σ,,#0] ≈ A[σ][Wk] : Type@i }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ #0[q σ,,#0] ≈ #0 : A[σ][Wk] }} by (eapply wf_exp_eq_conv'; mauto 2).
  assert {{ Γ, A[σ] ⊢ #0[q σ,,#0] ≈ #0 : A[Wk∘Wk][q σ,,#0] }} by mauto 3.

  assert {{ Γ, A[σ] ⊢s σ∘Wk : Δ }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ A[σ][Wk] ≈ A[σ∘Wk] : Type@i }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ∘Wk] }} by mauto 3.

  assert {{ Δ, A ⊢ #0 : A[Wk] }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ #1[q σ,,#0] ≈ #0 : A[σ][Wk] }} by (eapply wf_exp_eq_conv' with (A:={{{ A[σ∘Wk] }}}); mauto 2 using sub_lookup_var1).
  assert {{ Γ, A[σ] ⊢ #1[q σ,,#0] ≈ #0 : A[Wk∘Wk][q σ,,#0] }} by mauto 3.

  assert {{ Γ, A[σ] ⊢s q (q (q σ))∘(Id,,#0,,refl A[σ][Wk] #0) ≈ (q (q σ)∘(Id,,#0)),,refl A[σ][Wk] #0 : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }}.
  {
    etransitivity.
    - eapply wf_sub_eq_extend_compose; eauto; [mautosolve 2 |].
      eapply wf_conv'; [mautosolve 2 |].
      symmetry.
      transitivity {{{ (Eq A[Wk∘Wk] #1 #0)[q (q σ)][Wk] }}}; [mautosolve 3 |].
      eapply exp_eq_sub_cong_typ1; mautosolve 2.
    - econstructor; [mautosolve 2 | mautosolve 2 |].
      eapply wf_exp_eq_conv'.
      + econstructor; [mautosolve 2 | mautosolve 2 |].
        eapply wf_conv'; [econstructor |]; mautosolve 2.
      + etransitivity; [mautosolve 2 |].
        symmetry.
        etransitivity;
          [eapply exp_eq_sub_cong_typ2'; mautosolve 2 | etransitivity];
          econstructor; mauto 2.
  }

  assert {{ Γ, A[σ] ⊢ A[Wk∘Wk][q (q σ)∘(Id,,#0)] ≈ A[Wk][q σ] : Type@i }} by mauto 3.
  assert {{ Γ, A[σ] ⊢ A[Wk∘Wk][q (q σ)∘(Id,,#0)] ≈ A[σ][Wk] : Type@i }} by mauto 2.

  assert {{ Γ, A[σ] ⊢ #0[q (q σ)∘(Id,,#0)] ≈ #0 : A[σ][Wk] }}.
  {
    transitivity {{{ #0[q σ,,#0] }}}; [| eassumption].
    eapply wf_exp_eq_conv'; [econstructor; [| eassumption] |]; mautosolve 3.
  }
  assert {{ Γ, A[σ] ⊢ #0[q (q σ)∘(Id,,#0)] ≈ #0 : A[Wk∘Wk][q (q σ)∘(Id,,#0)] }} by (eapply wf_exp_eq_conv'; mauto 2).

  assert {{ Γ, A[σ] ⊢ #1[q (q σ)∘(Id,,#0)] ≈ #0 : A[σ][Wk] }}.
  {
    transitivity {{{ #1[q σ,,#0] }}}; [| eassumption].
    eapply wf_exp_eq_conv'; [econstructor; [| eassumption] |]; mautosolve 3.
  }
  assert {{ Γ, A[σ] ⊢ #1[q (q σ)∘(Id,,#0)] ≈ #0 : A[Wk∘Wk][q (q σ)∘(Id,,#0)] }} by (eapply wf_exp_eq_conv'; mauto 2).

  assert {{ Γ, A[σ] ⊢s q (q (q σ))∘(Id,,#0,,refl A[σ][Wk] #0) ≈ q σ,,#0,,refl A[σ][Wk] #0 : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }}.
  {
    etransitivity; [eassumption |].
    econstructor; [mautosolve 2 | mautosolve 2 |].
    eapply exp_eq_refl.
    eapply wf_conv'; [mautosolve 2 |].
    symmetry.
    etransitivity; econstructor; mauto 2.
  }

  assert {{ Γ, A[σ] ⊢s Id∘q σ : Δ, A }} by mauto 3.
  assert {{ Γ, A[σ] ⊢s Id∘q σ ≈ q σ : Δ, A }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ #0[q σ] ≈ #0 : A[σ∘Wk] }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ #0[q σ] ≈ #0 : A[σ][Wk] }} by mauto 3.
  assert {{ Γ, A[σ] ⊢ #0[q σ] ≈ #0 : A[Wk][q σ] }} by (eapply wf_exp_eq_conv'; mauto 2).
  assert {{ Γ, A[σ] ⊢s (Id,,#0)∘q σ : Δ, A, A[Wk] }} by (econstructor; mauto 2).
  assert {{ Γ, A[σ] ⊢s (Id,,#0)∘q σ ≈ q σ,,#0 : Δ, A, A[Wk] }}.
  {
    etransitivity; [eapply wf_sub_eq_extend_compose; mautosolve 2 |].
    econstructor; [eassumption | eassumption |].
    eapply wf_exp_eq_conv'; [mautosolve 2 |].
    eapply exp_eq_sub_cong_typ2'; mauto 2.
  }

  assert {{ Δ, A ⊢ A[Wk∘Wk][Id,,#0] ≈ A[Wk] : Type@i }}
    by (transitivity {{{ A[Wk][Wk][Id,,#0] }}}; [eapply exp_eq_sub_cong_typ1 |]; mauto 3).
  assert {{ Δ, A ⊢ #0[Id,,#0] ≈ #0 : A[Wk] }} by (eapply wf_exp_eq_conv'; [econstructor |]; mauto 2).
  assert {{ Δ, A ⊢ A[Wk∘Wk][Id,,#0] : Type@i }} by (eapply exp_sub_typ; mauto 2).
  assert {{ Δ, A ⊢ #0[Id,,#0] ≈ #0 : A[Wk∘Wk][Id,,#0] }} by (eapply wf_exp_eq_conv'; mauto 2).
  assert {{ Δ, A ⊢ #1[Id,,#0] ≈ #0 : A[Wk] }}.
  {
    transitivity {{{ #0[Id] }}}; [| mautosolve 2].
    eapply wf_exp_eq_conv'; [econstructor |]; try mautosolve 2.
    eapply wf_conv'; mauto 4.
  }
  assert {{ Δ, A ⊢ #1[Id,,#0] ≈ #0 : A[Wk∘Wk][Id,,#0] }} by (eapply wf_exp_eq_conv'; mauto 2).

  assert {{ Δ, A ⊢ (Eq A[Wk∘Wk] #1 #0)[Id,,#0] ≈ Eq A[Wk] #0 #0 : Type@i }}.
  {
    transitivity {{{ Eq A[Wk∘Wk][Id,,#0] #1[Id,,#0] #0[Id,,#0]}}}; [| mautosolve 2].
    eapply wf_exp_eq_eq_sub; mauto 2.
  }

  assert {{ Δ, A ⊢ refl A[Wk] #0 : (Eq A[Wk∘Wk] #1 #0)[Id,,#0] }}.
  {
    eapply wf_conv'; [mautosolve 2 |].
    symmetry.
    etransitivity; econstructor; mauto 2.
  }

  assert {{ Γ, A[σ] ⊢ (Eq A[Wk] #0 #0)[q σ] ≈ Eq A[σ][Wk] #0 #0 : Type@i }}
    by (etransitivity; [econstructor |]; mauto 2).
  assert {{ Γ, A[σ] ⊢ A[Wk∘Wk][(Id,,#0)∘q σ] ≈ A[σ][Wk] : Type@i }} by mauto 3.
  assert {{ Γ, A[σ] ⊢ #1[(Id,,#0)∘q σ] ≈ #0 : A[σ][Wk] }}
    by (transitivity {{{ #1[q σ,,#0] }}}; [eapply wf_exp_eq_conv' |]; mauto 2; econstructor; mauto 3).
  assert {{ Γ, A[σ] ⊢ #1[(Id,,#0)∘q σ] ≈ #0 : A[Wk∘Wk][(Id,,#0)∘q σ] }} by (eapply wf_exp_eq_conv'; mauto 2).

  assert {{ Γ, A[σ] ⊢ #0[(Id,,#0)∘q σ] ≈ #0 : A[σ][Wk] }}.
  {
    transitivity {{{ #0[q σ,,#0] }}}; [eapply wf_exp_eq_conv'; [| eassumption] | mautosolve 2].
    econstructor; mauto 3.
  }
  assert {{ Γ, A[σ] ⊢ #0[(Id,,#0)∘q σ] ≈ #0 : A[Wk∘Wk][(Id,,#0)∘q σ] }} by (eapply wf_exp_eq_conv'; mauto 2).

  assert {{ Γ, A[σ] ⊢ (Eq A[Wk∘Wk] #1 #0)[(Id,,#0)∘q σ] ≈ Eq A[σ][Wk] #0 #0 : Type@i }}
    by (etransitivity; econstructor; mauto 2).

  assert {{ Γ, A[σ] ⊢s (Id,,#0,,refl A[Wk] #0)∘q σ ≈ q σ,,#0,,refl A[σ][Wk] #0 : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }}.
  {
    etransitivity; [eapply wf_sub_eq_extend_compose; mautosolve 2 |].
    econstructor; eauto.
    etransitivity.
    - eapply wf_exp_eq_conv'; [mautosolve 2 |].
      etransitivity; mauto 2.
    - eapply wf_exp_eq_conv'; [econstructor; mautosolve 2 |].
      etransitivity; mauto 2.
  }

  assert {{ Γ, A[σ] ⊢s q (q (q σ))∘(Id,,#0,,refl A[σ][Wk] #0) ≈ (Id,,#0,,refl A[Wk] #0)∘q σ : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} by mauto 3.

  assert {{ Δ, A ⊢s Id,,#0,,refl A[Wk] #0 : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} by (econstructor; mauto 2).

  repeat (split; [eassumption |]).
  intros.
  assert {{ Γ ⊢ A[Wk][σ,,M1] : Type@i }} by (eapply exp_sub_typ; mauto 2).
  assert {{ Γ ⊢ A[Wk][σ,,M1] ≈ A[σ] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ M2 : A[Wk][σ,,M1] }} by mauto 3.
  assert {{ Γ ⊢s σ,,M1 : Δ, A }} by mauto 2.
  assert {{ Γ ⊢s σ,,M1,,M2 : Δ, A, A[Wk] }} by mauto 2.
  assert {{ Γ ⊢ A[Wk∘Wk][σ,,M1,,M2] ≈ A[σ] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ #1[σ,,M1,,M2] ≈ M1 : A[Wk∘Wk][σ,,M1,,M2] }} by (eapply wf_exp_eq_conv'; mauto 2 using sub_lookup_var1).
  assert {{ Γ ⊢ #0[σ,,M1,,M2] ≈ M2 : A[Wk∘Wk][σ,,M1,,M2] }} by (eapply wf_exp_eq_conv' with (A:={{{ A[σ] }}}); mauto 2 using sub_lookup_var0).
  assert {{ Γ ⊢ (Eq A[Wk∘Wk] #1 #0)[σ,,M1,,M2] ≈ Eq A[σ] M1 M2 : Type@i }}.
  {
    transitivity {{{ Eq A[Wk∘Wk][σ,,M1,,M2] #1[σ,,M1,,M2] #0[σ,,M1,,M2] }}}; [| mautosolve 2].
    eapply wf_exp_eq_eq_sub; mauto 2.
  }
  assert {{ Γ ⊢s Id,,M1 : Γ, A[σ] }} by mauto 2.
  assert {{ Γ ⊢ A[σ][Wk][Id,,M1] ≈ A[σ] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ M2 : A[σ][Wk][Id,,M1] }} by (eapply wf_conv'; revgoals; mauto 2).
  assert {{ Γ ⊢s Id,,M1,,M2 : Γ, A[σ], A[σ][Wk] }} by mauto 2.

  assert {{ Γ ⊢ #0[σ,,M1] ≈ M1 : A[Wk][σ,,M1] }} by (eapply wf_exp_eq_conv'; [eapply wf_exp_eq_var_0_sub with (A:=A) |]; mauto 3).

  assert {{ Γ ⊢ (Eq A[Wk] #0 #0)[σ,,M1] ≈ Eq A[σ] M1 M1 : Type@i }} by (etransitivity; econstructor; mauto 2).

  assert {{ Γ ⊢ A[σ][Wk∘Wk][Id,,M1,,M2] ≈ A[σ] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ A[Wk∘Wk][σ,,M1,,M2] ≈ A[σ] : Type@i }} by mauto 2.

  assert {{ Γ ⊢ #1[Id,,M1,,M2] ≈ M1 : A[σ] }} by mauto 2 using id_sub_lookup_var1.
  assert {{ Γ ⊢ #1[Id,,M1,,M2] ≈ M1 : A[σ][Wk∘Wk][Id,,M1,,M2] }} by (eapply wf_exp_eq_conv'; mauto 2).

  assert {{ Γ ⊢ #0[Id,,M1,,M2] ≈ M2 : A[σ] }} by (eapply wf_exp_eq_conv'; mauto 2).
  assert {{ Γ ⊢ #0[Id,,M1,,M2] ≈ M2 : A[σ][Wk∘Wk][Id,,M1,,M2] }} by (eapply wf_exp_eq_conv'; mauto 2).

  assert {{ Γ ⊢ (Eq A[Wk∘Wk] #1 #0)[σ,,M1,,M2] ≈ Eq A[σ] M1 M2 : Type@i }}
    by (etransitivity; econstructor; mauto 2).
  assert {{ Γ ⊢ (Eq A[σ][Wk∘Wk] #1 #0)[Id,,M1,,M2] ≈ Eq A[σ] M1 M2 : Type@i }}
    by (etransitivity; econstructor; mauto 2).

  assert {{ Γ, A[σ], A[σ][Wk], Eq A[σ][Wk∘Wk] #1 #0 ⊢s q (q σ)∘Wk : Δ, A, A[Wk] }} by mauto 2.
  assert {{ Γ, A[σ], A[σ][Wk], Eq A[σ][Wk∘Wk] #1 #0 ⊢ (Eq A[Wk∘Wk] #1 #0)[q (q σ)∘Wk] ≈ (Eq A[σ][Wk∘Wk] #1 #0)[Wk] : Type@i }}
    by (etransitivity; [symmetry |]; mauto 2 using exp_eq_sub_compose_typ).

  assert {{ Γ, A[σ], A[σ][Wk], Eq A[σ][Wk∘Wk] #1 #0 ⊢ #0 : (Eq A[Wk∘Wk] #1 #0)[q (q σ)∘Wk] }} by (eapply wf_conv'; mauto 2).

  assert {{ Γ ⊢s (q σ∘Wk)∘(Id,,M1,,M2) : Δ, A }} by (econstructor; mauto 2).
  assert {{ Γ ⊢s (q σ∘Wk)∘(Id,,M1,,M2) ≈ σ,,M1 : Δ, A }}.
  {
    etransitivity; [eapply wf_sub_eq_compose_assoc; eassumption |].
    transitivity {{{ q σ∘(Id,,M1) }}}; [| mautosolve 3].
    econstructor; mauto 2.
  }

  assert {{ Γ ⊢ A[Wk][(q σ∘Wk)∘(Id,,M1,,M2)] ≈ A[σ] : Type@i }} by (transitivity {{{ A[Wk][σ,,M1] }}}; mauto 2).
  assert {{ Γ ⊢ #0[Id,,M1,,M2] ≈ M2 : A[Wk][(q σ∘Wk)∘(Id,,M1,,M2)] }} by (eapply wf_exp_eq_conv'; revgoals; mauto 2).

  assert {{ Γ, A[σ], A[σ][Wk] ⊢ #0 : A[Wk][q σ∘Wk] }} by (eapply wf_conv'; mauto 2).
  assert {{ Γ ⊢s q (q σ)∘(Id,,M1,,M2) ≈ σ,,M1,,M2 : Δ, A, A[Wk] }}
    by (etransitivity; [eapply wf_sub_eq_extend_compose | econstructor]; mauto 2).

  repeat (split; [eassumption |]).
  intros.
  assert {{ Γ ⊢ N : (Eq A[σ][Wk∘Wk] #1 #0)[Id,,M1,,M2] }} by (eapply wf_conv'; mauto 2).
  assert {{ Γ ⊢s Id,,M1,,M2,,N : Γ, A[σ], A[σ][Wk], Eq A[σ][Wk∘Wk] #1 #0 }} by mauto 2.

  assert {{ Γ ⊢ N : (Eq A[Wk∘Wk] #1 #0)[σ,,M1,,M2] }} by (eapply wf_conv' with (A:={{{Eq A[σ] M1 M2}}}); mauto 2).
  assert {{ Γ ⊢s σ,,M1,,M2,,N : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} by mauto 2.
  assert {{ Γ ⊢s (q (q σ)∘Wk)∘(Id,,M1,,M2,,N) : Δ, A, A[Wk] }} by mauto 2.
  assert {{ Γ ⊢s (q (q σ)∘Wk)∘(Id,,M1,,M2,,N) ≈ σ,,M1,,M2 : Δ, A, A[Wk] }}.
  {
    transitivity {{{ q (q σ)∘Wk∘(Id,,M1,,M2,,N) }}}; [mautosolve 2 |].
    transitivity {{{ q (q σ)∘(Id,,M1,,M2) }}}; [| mautosolve 3].
    econstructor; mauto 2.
  }

  assert {{ Γ ⊢ (Eq A[Wk∘Wk] #1 #0)[(q (q σ)∘Wk)∘(Id,,M1,,M2,,N)] ≈ Eq A[σ] M1 M2 : Type@i }} by mauto 3.
  assert {{ Γ ⊢ #0[Id,,M1,,M2,,N] ≈ N : (Eq A[Wk∘Wk] #1 #0)[(q (q σ)∘Wk)∘(Id,,M1,,M2,,N)] }}
    by (eapply wf_exp_eq_conv' with (A:={{{ Eq A[σ] M1 M2 }}}); [econstructor |]; mauto 2).
  etransitivity; mautosolve 2.
Qed.

Lemma glu_rel_eq_eqrec_synprop_gen_A : forall {Γ σ Δ i A},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ, A[σ], A[σ][Wk] ⊢s q (q σ) : Δ, A, A[Wk] }} /\
    {{ Γ, A[σ] ⊢ A[Wk][q σ] ≈ A[σ][Wk] : Type@i }} /\
    {{ Γ, A[σ], A[σ][Wk] ⊢ A[Wk][q σ∘Wk] ≈ A[σ][Wk∘Wk] : Type@i }} /\
    {{ Γ, A[σ], A[σ][Wk] ⊢ (Eq A[Wk∘Wk] #1 #0)[q (q σ)] ≈ Eq A[σ][Wk∘Wk] #1 #0 : Type@i }} /\
    {{ Δ, A ⊢s Id,,#0,,refl A[Wk] #0 : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} /\
    {{ ⊢ Γ, A[σ], A[σ][Wk], (Eq A[Wk∘Wk] #1 #0)[q (q σ)] }} /\
    {{ Δ, A ⊢ (Eq A[Wk∘Wk] #1 #0)[Id,,#0] ≈ Eq A[Wk] #0 #0 : Type@i }} /\
    {{ Δ, A ⊢s Id,,#0,,refl A[Wk] #0 : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} /\
    {{ Γ, A[σ] ⊢ (Eq A[σ][Wk∘Wk] #1 #0)[Id,,#0] ≈ Eq A[σ][Wk] #0 #0 : Type@i }} /\
    {{ Γ, A[σ] ⊢ (Eq A[σ][Wk∘Wk] #0 #0)[Id,,#0] ≈ Eq A[σ][Wk] #0 #0 : Type@i }} /\
    {{ Γ, A[σ] ⊢s Id,,#0,,refl A[σ][Wk] #0 : Γ, A[σ], A[σ][Wk], Eq A[σ][Wk∘Wk] #1 #0 }} /\
    {{ Γ, A[σ], A[σ][Wk], Eq A[σ][Wk∘Wk] #1 #0 ⊢s q (q (q σ)) : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} /\
    {{ Γ, A[σ] ⊢s q (q (q σ))∘(Id,,#0,,refl A[σ][Wk] #0) ≈ (Id,,#0,,refl A[Wk] #0)∘q σ : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }}.
Proof.
  intros * ? H0 **.
  eapply glu_rel_eq_eqrec_synprop_gen in H0; mauto 2.
  firstorder.
Qed.

Lemma glu_rel_eq_eqrec_synprop_gen_M1M2 : forall {Γ σ Δ i A M1 M2},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M1 : A[σ] }} ->
    {{ Γ ⊢ M2 : A[σ] }} ->
    {{ Γ ⊢ (Eq A[Wk] #0 #0)[σ,,M1] ≈ Eq A[σ] M1 M1 : Type@i }} /\
    {{ Γ ⊢ (Eq A[σ][Wk∘Wk] #1 #0)[Id,,M1,,M2] ≈ Eq A[σ] M1 M2 : Type@i }} /\
    {{ Γ ⊢ (Eq A[Wk∘Wk] #1 #0)[σ,,M1,,M2] ≈ Eq A[σ] M1 M2 : Type@i }}.
Proof.
  intros * ? H0 **.
  eapply glu_rel_eq_eqrec_synprop_gen in H0; mauto 2.
  firstorder.
Qed.

Lemma glu_rel_eq_eqrec_synprop_gen_N : forall {Γ σ Δ i A M1 M2 N},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M1 : A[σ] }} ->
    {{ Γ ⊢ M2 : A[σ] }} ->
    {{ Γ ⊢ N : Eq A[σ] M1 M2 }} ->
    {{ Γ ⊢s q (q (q σ))∘(Id,,M1,,M2,,N) ≈ (σ,,M1,,M2,,N) : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }}.
Proof.
  intros * ? H0 **.
  eapply glu_rel_eq_eqrec_synprop_gen in H0; mauto 2.
  firstorder.
Qed.

Lemma wf_exp_eq_eqrec_id0refl0σm_σmmreflm : forall {Γ Δ i σ A M},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢s (Id,,#0,,refl A[Wk] #0)∘(σ,,M) ≈ σ,,M,,M,,refl A[σ] M : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }}.
Proof.
  intros.
  gen_presups.
  assert {{ ⊢ Δ, A }} by mauto 2.
  assert {{ Δ, A ⊢s Wk : Δ }} by mauto 2.
  assert {{ Δ, A ⊢ A[Wk] : Type@i }} by mauto 2.
  assert {{ Γ ⊢s Id∘(σ,,M) : Δ, A }} by (econstructor; mauto 2).
  assert {{ Γ ⊢s Id∘(σ,,M) ≈ (σ,,M) : Δ, A }} by mauto 3.
  assert {{ Γ ⊢ #0[σ,,M] ≈ M : A[σ] }} by mauto 2.
  assert {{ Γ ⊢s Wk∘(σ,,M) ≈ σ : Δ }} by mauto 2.
  assert {{ Δ, A ⊢ #0 : A[Wk][Id] }} by (eapply wf_conv'; mauto 3).
  assert {{ Δ, A ⊢s Id,,#0 : Δ, A, A[Wk] }} by mauto 3.
  assert {{ Γ ⊢ #0[σ,,M] ≈ M : A[Wk][Id∘(σ,,M)] }}.
  {
    eapply wf_exp_eq_conv'; [mautosolve 2 |].
    eapply exp_eq_compose_typ_twice; mauto 2.
    transitivity {{{ Wk∘(σ,,M) }}}; [mautosolve 2 |].
    econstructor; mauto 2.
  }
  etransitivity; [eapply wf_sub_eq_extend_compose; mauto 2 |].
  - eapply wf_conv'; [| symmetry; eapply glu_rel_eq_eqrec_synprop_gen_A]; mauto 3.
  - econstructor; [| mautosolve 3 |].
    + etransitivity; [eapply wf_sub_eq_extend_compose; mauto 3 | mauto 2].
    + assert {{ Γ ⊢s (Id,,#0)∘(σ,,M) ≈ (σ,,M,,M) : Δ, A, A[Wk] }} by (transitivity {{{ (Id∘(σ,,M),,#0[σ,,M])}}}; mauto 2; econstructor; mauto 2).
      gen_presups.
      eapply glu_rel_eq_eqrec_synprop_gen_M1M2 in HN0; mauto 2.
      destruct_conjs.
      eapply wf_exp_eq_conv' with (i:=i) (A:={{{ Eq A[σ] M M }}}); mauto 2.
      * transitivity {{{refl A[Wk][σ,,M] #0[σ,,M] }}}.
        -- eapply wf_exp_eq_conv'; mauto 3.
        -- symmetry.
           eapply wf_exp_eq_refl_cong; mauto 2.
           eapply exp_eq_compose_typ_twice; mauto 2.
      * transitivity {{{ (Eq A[Wk∘Wk] #1 #0)[σ,,M,,M] }}}; mauto 2.
        eapply wf_exp_eq_conv'; [eapply wf_exp_eq_sub_cong |]; mauto 3.
Qed.

Lemma wf_exp_eq_σM1M2N : forall {Γ Δ i σ A M1 M2 N},
  {{ Γ ⊢s σ : Δ }} ->
  {{ Δ ⊢ A : Type@i }} ->
  {{ Δ ⊢ M1 : A }} ->
  {{ Δ ⊢ M2 : A }} ->
  {{ Δ ⊢ N : Eq A M1 M2 }} ->
  {{ Γ ⊢s σ,,M1[σ],,M2[σ],,N[σ] ≈ (Id,,M1,,M2,,N)∘σ : Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }}.
Proof.
  intros.
  gen_presups.
  assert {{ ⊢ Δ, A }} by mauto 2.
  assert {{ Δ, A ⊢s Wk : Δ }} by mauto 2.
  assert {{ Δ, A ⊢ A[Wk] : Type@i }} by mauto 2.
  assert {{ ⊢ Δ, A, A[Wk] }} by mauto 2.
  assert {{ Γ ⊢s σ,,M1[σ] ≈ (Id,,M1)∘σ : Δ, A }}.
  {
    etransitivity; [| symmetry; eapply wf_sub_eq_extend_compose]; mauto 2.
    eapply wf_sub_eq_extend_cong; mauto 3.
  }
  assert {{ Γ ⊢s σ,,M1[σ],,M2[σ] ≈ (Id,,M1,,M2)∘σ : Δ, A, A[Wk] }}.
  {
    etransitivity.
    - eapply wf_sub_eq_extend_cong; [mautosolve 2 | mautosolve 2 |].
      eapply wf_exp_eq_conv'; [mautosolve 3 |].
      eapply exp_eq_compose_typ_twice; mauto 3.
      symmetry. mauto 3.
    - symmetry; eapply wf_sub_eq_extend_compose; mauto 2.
      eapply wf_conv'; mauto 3.
  }
  etransitivity.
  - eapply wf_sub_eq_extend_cong; [mautosolve 2 | mautosolve 2 |].
    eapply wf_exp_eq_conv'; mauto 3.
  - symmetry; eapply wf_sub_eq_extend_compose; mauto 2.
    eapply wf_conv'; mauto 3.
Qed.

Lemma wf_exp_eq_eqrec_cong_sub : forall {Γ σ Δ i j A A' M1 M1' M2 M2' N N' B B' BR BR'},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Δ ⊢ M1 : A }} ->
    {{ Δ ⊢ M2 : A }} ->
    {{ Δ, A ⊢ BR : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢ B : Type@j }} ->
    {{ Δ ⊢ N : Eq A M1 M2 }} ->
    {{ Γ ⊢ A[σ] ≈ A' : Type@i }} ->
    {{ Γ ⊢ M1[σ] ≈ M1' : A[σ] }} ->
    {{ Γ ⊢ M2[σ] ≈ M2' : A[σ] }} ->
    {{ Γ ⊢ N[σ] ≈ N' : Eq A[σ] M1[σ] M2[σ]}} ->
    {{ Γ, A[σ] ⊢ BR[q σ] ≈ BR' : B[Id,,#0,,refl A[Wk] #0][q σ] }} ->
    {{ Γ, A[σ], A[σ][Wk], (Eq A[Wk∘Wk] #1 #0)[q (q σ)] ⊢ B[q (q (q σ))] ≈ B' : Type@j }} ->
    {{ Γ ⊢ eqrec N as Eq A M1 M2 return B | refl -> BR end[σ] ≈
           eqrec N' as Eq A' M1' M2' return B' | refl -> BR' end : B[Id,,M1,,M2,,N][σ] }}.
Proof.
  intros.
  assert {{ Γ ⊢ B[σ,,M1[σ],,M2[σ],,N[σ]] ≈ B[Id,,M1,,M2,,N][σ] : Type@j }}
    by (eapply exp_eq_compose_typ_twice; mauto 2 using wf_exp_eq_σM1M2N).
  assert {{ Γ ⊢ B[Id,,M1,,M2,,N][σ] ≈ B[σ,,M1[σ],,M2[σ],,N[σ]] : Type@j }} by mauto 2.
  gen_presups.
  transitivity {{{ eqrec N[σ] as Eq A[σ] M1[σ] M2[σ] return B[q (q (q σ))] | refl -> BR[q σ] end }}}.
  - mauto 3.
  - eapply wf_exp_eq_conv' with (A:={{{(B[q (q (q σ))])[(Id,,M1[σ],,M2[σ],,N[σ])]}}}).
    + eapply wf_exp_eq_eqrec_cong with (j:=j); mauto 2.
      * eapply ctxeq_exp_eq; mauto 2.
        eapply wf_ctx_eq_extend''; eapply glu_rel_eq_eqrec_synprop_gen_A; mauto 2.
      * eapply wf_exp_eq_conv'; mauto 2.
        eapply @wf_eq_typ_exp_sub_cong_twice with (Δ':={{{ Γ, A[σ], A[σ][Wk], Eq A[σ][Wk∘Wk] #1 #0 }}}); mauto 2;
          try (eapply glu_rel_eq_eqrec_synprop_gen_A; mautosolve 2).
        symmetry.
        eapply glu_rel_eq_eqrec_synprop_gen_A; mauto 2.
    + eapply wf_eq_typ_exp_sub_cong_twice; mauto 2.
      * eapply glu_rel_eq_eqrec_synprop_gen_A; mauto 2.
      * erewrite glu_rel_eq_eqrec_synprop_gen_N; mauto 2 using wf_exp_eq_σM1M2N.
Qed.

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
  assert {{ ⊩ Γ }} by mauto 2.
  assert {{ ⊩ Γ, A }} by mauto 2.
  assert {{ Γ, A ⊩ A[Wk] : Type@i }} as HAWk by mauto 3.
  assert {{ ⊩ Γ, A, A[Wk] }} by mauto 3.
  saturate_syn_judge.
  assert {{ Γ ⊩s Id,,M1 : Γ, A }} by (eapply glu_rel_sub_extend; mauto 4).
  assert {{ Γ, A, A[Wk] ⊩ Eq A[Wk ∘ Wk] #1 #0 : Type@i }} as HEq
    by (eapply glu_rel_eq; [mauto | |]; rewrite <- @exp_eq_sub_compose_typ with (i := i); mauto 3).
  assert {{ ⊩ Γ, A, A[Wk], Eq A[Wk ∘ Wk] #1 #0 }} by mauto 2.
  assert {{ Γ ⊩s Id,,M1,,M2,,N : Γ, A, A[Wk], Eq A[Wk ∘ Wk] #1 #0 }}.
  {
    assert {{ Γ ⊩s Id,,M1,,M2 : Γ, A, A[Wk] }} by (eapply glu_rel_sub_extend; mauto 4).
    eapply glu_rel_sub_extend; [mautosolve 2 | eassumption | mautosolve 4].
  }
  saturate_syn_judge.
  assert {{ Γ, A ⊢s Id,,#0,,refl A[Wk] #0 : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }}.
  {
    assert {{ Γ, A ⊢s Id,,#0 : Γ, A, A[Wk] }} by mauto 3.
    assert {{ Γ, A ⊢ (Eq A[Wk∘Wk] #1 #0)[Id,,#0] ≈ Eq A[Wk] #0 #0 : Type@i }} by (eapply glu_rel_eq_eqrec_synprop_gen_A; mauto 2).
    econstructor; mauto 3.
    bulky_rewrite.
    mauto 3.
  }

  assert {{ ⊩ Γ }} as [SbΓ] by mauto 2.
  pose (SbΓA := cons_glu_sub_pred i Γ {{{ A }}} SbΓ).
  assert {{ EG Γ, A ∈ glu_ctx_env ↘ SbΓA }} by (invert_glu_rel_exp HA; econstructor; mauto 3; reflexivity).
  pose (SbΓAA := cons_glu_sub_pred i {{{ Γ , A }}} {{{ A[Wk] }}} SbΓA).
  assert {{ EG Γ, A, A[Wk] ∈ glu_ctx_env ↘ SbΓAA }} by (invert_glu_rel_exp HAWk; econstructor; mauto 3; reflexivity).
  pose (SbΓAAEq := cons_glu_sub_pred i {{{ Γ, A, A[Wk] }}} {{{ Eq A[Wk∘Wk] #1 #0 }}} SbΓAA).
  assert {{ EG Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ∈ glu_ctx_env ↘ SbΓAAEq }} by (invert_glu_rel_exp HEq; econstructor; mauto 3; reflexivity).

  (* TODO *)
  clear HAWk. clear H1.
  invert_sem_judge.
  clear H29.
  eexists; split; eauto.
  exists j; intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 2.
  (on_all_hyp: destruct_glu_rel_by_assumption SbΓ).
  simplify_evals.
  handle_functional_glu_univ_elem.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
  apply_predicate_equivalence.
  unfold univ_glu_exp_pred' in *.
  destruct_all.
  handle_functional_glu_univ_elem.
  repeat match goal with
         | H: ?i < S ?i |- _ => idtac H; clear H
         | H: {{ DG 𝕌@_ ∈ glu_univ_elem _ ↘ _ ↘ _ }} |- _ => idtac H; clear H
         | H: {{ DG Eq ^_ ^_ ^_ ∈ glu_univ_elem _ ↘ _ ↘ _ }} |- _ => idtac H; clear H
         end.
  (on_all_hyp: destruct_glu_rel_by_assumption SbΓA).
  (on_all_hyp: destruct_glu_rel_by_assumption SbΓAAEq).
  simplify_evals.
  match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
  apply_predicate_equivalence.
  unfold univ_glu_exp_pred' in *.
  destruct_all.
  handle_functional_glu_univ_elem.
  repeat match goal with
         | H: ?i < S ?i |- _ => clear H
         | H: {{ DG 𝕌@_ ∈ glu_univ_elem _ ↘ _ ↘ _ }} |- _ => clear H
         end.

  match goal with
  | [ _ : {{ ⟦ A ⟧ ρ ↘ ^?a' }} ,
        _ : {{ ⟦ M1 ⟧ ρ ↘ ^?m1' }} ,
          _ : {{ ⟦ M2 ⟧ ρ ↘ ^?m2' }} ,
            _ : {{ ⟦ N ⟧ ρ ↘ ^?n' }} ,
              H : {{ ⟦ B ⟧ ρ ↦ ^?m1' ↦ ^?m1' ↦ refl ^?m1' ↘ ^?b0 }} ,
                _ : {{ ⟦ B ⟧ ρ ↦ ^?m1' ↦ ^?m2' ↦ ^?n' ↘ ^?b1 }} ,
                  _ : {{ ⟦ BR ⟧ ρ ↦ ^?m1' ↘ ^?br' }} |- _
            ] =>
    rename a' into a;
    rename n' into n;
    rename m1' into m1'';
    rename m2' into m2'';
    clear H;
    rename b1 into b;
    rename br' into br
  end; rename m1'' into m1; rename m2'' into m2.

  repeat invert_glu_rel1.
  rename Γ0 into Δ.
  saturate_glu_typ_from_el.
  saturate_glu_info.

  match goal with
  | [ H : {{ Δ ⊢ (Eq A M1 M2)[σ] ≈ Eq ^?A' ^?M1' ^?M2' : Type@i }} |- _ ] =>
      rename A' into Aσ;
      rename M1' into M1σ;
      rename M2' into M2σ
  end.

  enough (exists mr, {{ ⟦ eqrec N as Eq A M1 M2 return B | refl -> BR end ⟧ ρ ↘ mr }} /\ {{ Δ ⊢ eqrec N as Eq A M1 M2 return B | refl -> BR end[σ] : B[Id,,M1,,M2,,N][σ] ® mr ∈ El1 }}) as [? [? ?]] by (econstructor; [mauto | | |]; eassumption).
  destruct_glu_eq; rename Γ0 into Δ.
  - rename M'' into Mσ.
    assert {{ Δ ⊢ Mσ : Aσ }} by (gen_presups; trivial).
    assert {{ Δ ⊢ Aσ ≈ A[σ] : Type@i }} as HrwAσ' by mauto 3. rewrite HrwAσ' in *.
    assert {{ Δ ⊢ A[σ] ≈ Aσ : Type@i }} by mauto 2.
    assert {{ Δ ⊢ M1σ ≈ M1[σ] : A[σ] }} as HrwM1σ' by mauto 3.
    assert {{ Δ ⊢ M2σ ≈ M2[σ] : A[σ] }} as HrwM2' by mauto 3.
    assert (SbΓA Δ {{{σ,,Mσ}}} d{{{ρ ↦ m'}}}) by (eapply cons_glu_sub_pred_helper; mauto 3).
    assert {{ Δ ⊢ (Eq A M1 M2)[σ] ≈ Eq A[σ] M1[σ] M2[σ] : Type@i }} by mauto 2.
    assert {{ Δ ⊢ Eq A[σ] M1[σ] M2[σ] ≈ Eq A[σ] Mσ Mσ : Type@i }} by (eapply wf_exp_eq_eq_cong; mauto 3).
    assert {{ Δ ⊢ (Eq A M1 M2)[σ] ≈ Eq A[σ] Mσ Mσ : Type@i }} by mauto 2.
    assert {{ Δ ⊢s (Id,,#0,,refl A[Wk] #0)∘(σ,,Mσ) ≈ (Id,,M1,,M2,,N)∘σ : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0}}.
    {
      etransitivity; [eapply wf_exp_eq_eqrec_id0refl0σm_σmmreflm|]; mauto 3.
      etransitivity; [|eapply wf_exp_eq_σM1M2N]; mauto 3.
      repeat (eapply wf_sub_eq_extend_cong; mauto 2).
      - eapply wf_exp_eq_conv'; mauto 2; mauto 3.
      - eapply wf_exp_eq_conv'; [|symmetry; eapply glu_rel_eq_eqrec_synprop_gen_M1M2]; mauto 2.
        transitivity {{{ refl Aσ Mσ }}}; [| mautosolve 3].
        assert {{ Δ ⊢ Mσ ≈ Mσ : A[σ] }}; mautosolve 2.
    }
    assert {{ Δ ⊢ B[Id,,#0,,refl A[Wk] #0][σ,,Mσ] ≈ B[Id,,M1,,M2,,N][σ] : Type@j }} by mauto 3.
    assert {{ Δ ⊢ BR[σ,,Mσ] ≈ eqrec N as Eq A M1 M2 return B | refl -> BR end[σ] : B[Id,,#0,,refl A[Wk] #0][σ,,Mσ] }}.
    {
      bulky_rewrite1.
      assert {{ ⊢ Δ, A[σ] ≈ Δ, Aσ }} by (eapply wf_ctx_eq_extend'; mauto 3).
      assert {{ Δ, A[σ] ⊢ A[σ][Wk] ≈ Aσ[Wk] : Type@i }} by (eapply exp_eq_sub_cong_typ1; mauto 3).
      assert {{ Δ, A[σ] ⊢s Id,,#0 : Δ, A[σ], A[σ][Wk] }} by (gen_presups; econstructor; mauto 3).
      assert {{ Δ, A[σ], A[σ][Wk] ⊢s Wk∘Wk : Δ }} by (do 3 (econstructor; mauto 3)).
      assert {{ ⊢ Δ, A[σ], A[σ][Wk], (Eq A[Wk∘Wk] #1 #0)[q (q σ)] }} by (eapply glu_rel_eq_eqrec_synprop_gen_A; mauto 3).
      assert {{ Δ, A[σ], A[σ][Wk] ⊢s q (q σ) : Γ, A, A[Wk] }} by (eapply glu_rel_eq_eqrec_synprop_gen_A; mauto 3).
      assert {{ Δ, A[σ], A[σ][Wk], (Eq A[Wk∘Wk] #1 #0)[(q (q σ))] ⊢s q (q (q σ)) : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} by mauto 3.
      assert {{ Δ, A[σ], A[σ][Wk], Eq A[σ][Wk∘Wk] #1 #0 ⊢s q (q (q σ)) : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }}.
      {
        eapply ctxeq_sub; mauto 2.
        eapply wf_ctx_eq_extend''; mauto 2.
        etransitivity; [eapply glu_rel_eq_eqrec_synprop_gen_A|]; mauto 3.
      }
      assert {{ Δ ⊢ refl Aσ Mσ : Eq A[σ] Mσ Mσ }} by (gen_presups; eapply wf_conv'; mauto 2).
      transitivity {{{ eqrec (refl Aσ Mσ) as Eq Aσ Mσ Mσ return B[q (q (q σ))] | refl -> BR[q σ] end }}}.
      - eapply wf_exp_eq_conv' with (i:=j).
        + symmetry.
          etransitivity; [eapply wf_exp_eq_eqrec_beta with (j:=j)|]; mauto 2.
          * eapply @exp_sub_typ with (Δ:={{{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0}}}); mauto 2.
            eapply ctxeq_sub; mauto 2.
            eapply @wf_ctx_eq_extend' with (i:=i); mauto 2.
            eapply wf_exp_eq_eq_cong; mauto 3.
          * assert {{ Δ, A[σ] ⊢ Aσ[Wk] ≈ A[σ][Wk] : Type@i }} by mauto 2.
            assert {{ Δ, A[σ] ⊢ Eq Aσ[Wk] #0 #0 ≈ (Eq A[σ][Wk∘Wk] #1 #0)[Id,,#0] : Type@i }}.
            {
              transitivity {{{ Eq A[σ][Wk] #0 #0 }}}.
              - assert {{ Δ, A[σ] ⊢ #0 : Aσ[Wk] }} by (eapply wf_conv'; mauto 3).
                apply wf_exp_eq_eq_cong; mauto 2.
              - symmetry.
                eapply glu_rel_eq_eqrec_synprop_gen_A; mauto 2.
            }
            eapply wf_conv'; [eapply wf_exp_sub|]; mauto 3.
            eapply @ctxeq_exp_eq with (Γ:={{{ Δ, A[σ] }}}); mauto 2 using wf_ctx_eq_extend''.
            eapply wf_eq_typ_exp_sub_cong_twice; mauto 3.
            -- econstructor; mauto 2.
               eapply wf_conv'; mauto 2.
               gen_presups.
               econstructor; mauto 3.
            -- symmetry.
               etransitivity; [|eapply glu_rel_eq_eqrec_synprop_gen_A]; mauto 2.
               eapply wf_sub_eq_compose_cong; mauto 2.
               eapply wf_sub_eq_extend_cong; mauto 2.
               eapply wf_exp_eq_conv'; [eapply wf_exp_eq_refl_cong|]; mauto 2.
               eapply wf_exp_eq_conv'; mauto 3.
          * eapply wf_exp_eq_conv' with (i:=j) (A:={{{ B[σ,,Mσ,,Mσ,,refl Aσ Mσ] }}}); mauto 2.
            -- symmetry. eapply wf_exp_eq_conv' with (i:=j); [eapply exp_eq_compose_exp_twice|]; mauto 3.
               symmetry. eapply exp_eq_compose_typ_twice; mauto 2 using wf_exp_eq_eqrec_id0refl0σm_σmmreflm.
               symmetry. etransitivity; [eapply wf_exp_eq_eqrec_id0refl0σm_σmmreflm|]; mauto 2.
               repeat (eapply wf_sub_eq_extend_cong; mauto 2).
               ++ eapply wf_exp_eq_conv'; mauto 3.
               ++ eapply wf_exp_eq_conv'; [|symmetry; eapply glu_rel_eq_eqrec_synprop_gen_M1M2]; mauto 3.
            -- eapply exp_eq_compose_typ_twice; mauto 2.
               symmetry. eapply glu_rel_eq_eqrec_synprop_gen_N; mauto 2.
        + eapply exp_eq_sub_sub_compose_cong_typ; mauto 2.
          transitivity {{{ σ,,Mσ,,Mσ,,refl Aσ Mσ }}}.
          eapply glu_rel_eq_eqrec_synprop_gen_N; mauto 2.
          transitivity {{{σ,,M1[σ],,M2[σ],,N[σ]}}}; mauto 2 using wf_exp_eq_σM1M2N.
          repeat (eapply wf_sub_eq_extend_cong; mauto 2).
          * eapply wf_exp_eq_conv' with (A:={{{ A[σ] }}}); mauto 3.
          * eapply wf_exp_eq_conv'; [|symmetry; eapply glu_rel_eq_eqrec_synprop_gen_M1M2]; mauto 3.
      - symmetry.
        eapply @wf_exp_eq_eqrec_cong_sub with (Γ:=Δ) (Δ:=Γ) (j:=j); mauto 3.
        eapply exp_eq_refl.
        mauto 3.
    }
    (on_all_hyp: destruct_glu_rel_by_assumption SbΓA).
    simplify_evals.
    eexists; split; mauto 3.

    match goal with
    | [ _ : {{ ⟦ B ⟧ ρ ↦ m' ↦ m' ↦ refl m' ↘ ^?b0 }} ,
          _ : {{ ⟦ BR ⟧ ρ ↦ m' ↘ ^?br0 }} |- _  ] =>
      rename b0 into b';
      rename br0 into br'
    end.

    (* glu_univ_elem j P1 El1 b *)
    (* glu_univ_elem i0 P2 El2 b' *)
    (* by relating b and b', we can show El2 is equivalent to El1 by glu_univ_elem_resp_per_univ *)
    assert (exists R, {{ DF b ≈ b' ∈ per_univ_elem j ↘ R }}).
    {
      assert {{ Γ ⊨ A : Type@i }} as HrelA by mauto 3.
      assert {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊨ B : Type@j }} as HrelB by mauto 3.
      pose proof HrelA as HrelA'.
      invert_rel_exp_of_typ HrelA.
      destruct_all.
      eapply eval_eqrec_relΓAAEq_helper in HrelA' as [env_relΓAAEq [equiv_ΓAAEq HΓAAEq]]; eauto.
      assert ({{ Dom ρ ↦ m1 ↦ m2 ↦ refl m' ≈ ρ ↦ m' ↦ m' ↦ refl m' ∈ env_relΓAAEq }}).
      {
        eapply HΓAAEq; eauto.
        - eapply (@glu_ctx_env_per_env Γ); mauto.
        - symmetry; eassumption.
        - econstructor; [intuition | |];
            [> etransitivity; [symmetry |]; eassumption ..].
      }
      invert_rel_exp_of_typ HrelB.
      (on_all_hyp: fun H => unshelve eapply (rel_exp_under_ctx_implies_rel_typ_under_ctx _) in H as [elem_relB]; shelve_unifiable; [eassumption |]).
      gen ρ. intros.
      (on_all_hyp: destruct_rel_by_assumption env_relΓAAEq).
      simplify_evals. mauto.
    }
    deex.
    assert {{ DG b' ∈ glu_univ_elem j ↘ P1 ↘ El1 }} by (rewrite <- H45; eassumption).
    eapply glu_univ_elem_trm_resp_typ_exp_eq; eauto.
    eapply glu_univ_elem_trm_resp_exp_eq; eauto.
    eapply glu_univ_elem_exp_conv'; [| | eassumption |]; mauto 3.
    bulky_rewrite.
  - eexists; split; mauto 3.
    eapply realize_glu_elem_bot; mauto 3.
    destruct_by_head glu_bot.
    econstructor; mauto 3; [| econstructor].
    + eapply glu_univ_elem_typ_resp_exp_eq; mauto 3.
    + assert {{ ⊨ Γ }} by mauto 3.
      assert {{ Γ ⊨ A : Type@i }} by mauto 3.
      assert {{ Γ ⊨ M1 : A }} by mauto 3.
      assert {{ Γ ⊨ M2 : A }} by mauto 3.
      assert {{ Γ, A ⊨ BR : B[Id,,#0,,refl A[Wk] #0] }} by mauto.
      assert {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊨ B : Type@j }} by mauto 3.
      unfold valid_ctx in *. unfold per_ctx in *. deex.
      eapply @eval_eqrec_neut_same_ctx with (A:=A) (M1:=M1) (M2:=M2); mauto 3.
      eapply (@glu_ctx_env_per_env Γ); mauto.
    + intros Ψ τ w **.
      match goal with
      | _: glu_univ_elem _ ?P' _ a |- _ =>
          rename P' into P
      end.
      assert {{ ⊢ Ψ }} by mauto 3.
      assert {{ Ψ ⊢s τ : Δ }} by mauto 3.
      assert {{ Ψ ⊢s σ∘τ : Γ }} by mauto 3.
      assert {{ Ψ ⊢s σ∘τ ® ρ ∈ SbΓ }} by (eapply glu_ctx_env_sub_monotone; eassumption).
      assert (P Ψ {{{ A[σ∘τ] }}}).
      {
        eapply glu_univ_elem_typ_resp_exp_eq with (A:={{{ A[σ][τ] }}}); mauto 3.
        eapply glu_univ_elem_typ_monotone; mauto 3.
      }
      assert {{ Ψ, A[σ∘τ] ⊢s q (σ∘τ) ® ρ ↦ ⇑! a (length Ψ) ∈ SbΓA }}.
      {
        assert {{ Ψ, A[σ∘τ] ⊢ A[(σ∘τ)][Wk] ≈ A[Wk][q (σ∘τ)] : Type@i }}.
        {
          symmetry.
          eapply (@glu_rel_eq_eqrec_synprop_gen_A _ _ Γ); mauto 3.
        }
        unfold SbΓA. eapply cons_glu_sub_pred_helper; mauto 3.
        - eapply glu_ctx_env_sub_monotone; mauto 3.
        - eapply glu_univ_elem_trm_resp_typ_exp_eq; eauto.
          + eapply glu_univ_elem_trm_resp_exp_eq; eauto.
            eapply var0_glu_elem; mauto 3.
            mauto 3.
          + assert {{ Ψ, A[σ∘τ] ⊢s Wk : Ψ }} by mauto 3.
            mauto 2.
      }
      assert {{ Ψ, A[σ∘τ], A[σ∘τ][Wk] ⊢s q (q (σ∘τ)) ® ρ ↦ ⇑! a (length Ψ) ↦ ⇑! a (S (length Ψ)) ∈ SbΓAA }}.
      {
        unfold SbΓAA.
        assert {{ Ψ ⊢ A[σ∘τ] : Type@i }} by mauto 2.
        assert {{ ⊢ Ψ, A[σ∘τ] }} by mauto 2.
        assert {{ Ψ, A[σ∘τ] ⊢w Wk : Ψ }} by mauto 2.
        eapply cons_glu_sub_pred_helper; mauto 3.
        - assert {{ ⊢ Ψ, A[σ∘τ], A[σ∘τ][Wk] }} by mauto 3.
          assert {{ Ψ, A[σ∘τ], A[σ∘τ][Wk] ⊢w Wk : Ψ, A[σ∘τ] }} by mauto 2.
          eapply glu_ctx_env_sub_monotone; mauto 2.
        - eapply glu_univ_elem_trm_resp_typ_exp_eq; [idtac|idtac|symmetry; eapply glu_rel_eq_eqrec_synprop_gen_A]; mauto 3.
          erewrite wf_exp_eq_eqrec_Aσwkwk_Aσwkwk; eauto.
          replace (S (length Ψ)) with (length ({{{ Ψ, A[σ∘τ] }}})) by auto.
          eapply var0_glu_elem; mauto 2.
          eapply glu_univ_elem_typ_monotone; mauto 2.
      }
      assert {{ Ψ, A[σ∘τ], A[σ∘τ][Wk], (Eq A[Wk∘Wk] #1 #0)[q (q (σ∘τ))] ⊢s
                                              q (q (q (σ∘τ))) ® ρ ↦ ⇑! a (length Ψ) ↦ ⇑! a (S (length Ψ)) ↦ ⇑! (Eq a (⇑! a (length Ψ)) (⇑! a (S (length Ψ)))) (S (S (length Ψ))) ∈ SbΓAAEq }}.
      {
        unfold SbΓAAEq.
        assert {{ ⟦ Eq A[Wk∘Wk] #1 #0 ⟧ (ρ ↦ ⇑! a (length Ψ) ↦ ⇑! a (S (length Ψ))) ↘ Eq a (⇑! a (length Ψ)) (⇑! a (S (length Ψ)))}}
          by (econstructor; mauto 3; constructor).
        assert {{ ⊢ Ψ, A[σ∘τ], A[σ∘τ][Wk], (Eq A[Wk∘Wk] #1 #0)[q (q (σ∘τ))] }} by (eapply glu_rel_eq_eqrec_synprop_gen_A; mauto 3).
        apply_relation_equivalence.
        eapply @cons_glu_sub_pred_helper with
          (P:=eq_glu_typ_pred i d{{{⇑! a (length Ψ)}}} d{{{⇑! a (S (length Ψ))}}} P El)
          (El:=eq_glu_exp_pred i d{{{⇑! a (length Ψ)}}} d{{{⇑! a (S (length Ψ))}}} R P El); mauto 2.
        - eapply glu_ctx_env_sub_monotone; mauto 2.
        - glu_univ_elem_econstructor; mauto 2.
          + eapply var_per_elem; mauto 2.
          + eapply var_per_elem; mauto 2.
        - assert {{ ⊢ Ψ, A[σ∘τ] }} by mauto 3.
          assert {{ Ψ, A[σ∘τ] ⊢ A[σ∘τ][Wk] : Type@i }} by (eapply exp_sub_typ; mauto 2).
          assert {{ Ψ, A[σ∘τ], A[σ∘τ][Wk], (Eq A[Wk∘Wk] #1 #0)[q (q (σ∘τ))] ⊢s Wk∘Wk : Ψ, A[σ∘τ] }} by (econstructor; mauto 3).
          assert {{ Ψ, A[σ∘τ], A[σ∘τ][Wk], (Eq A[Wk∘Wk] #1 #0)[q (q (σ∘τ))] ⊢ #0 : (Eq A[Wk∘Wk] #1 #0)[q (q (σ∘τ))∘Wk] }} by mauto 4.
          assert {{ Ψ, A[σ∘τ], A[σ∘τ][Wk], (Eq A[Wk∘Wk] #1 #0)[q (q (σ∘τ))] ⊢ #2 : A[σ∘τ][Wk][Wk][Wk] }} by mauto 4.
          assert {{ Ψ, A[σ∘τ], A[σ∘τ][Wk], (Eq A[Wk∘Wk] #1 #0)[q (q (σ∘τ))] ⊢ A[σ∘τ][Wk][Wk∘Wk] ≈ A[σ∘τ][Wk][Wk][Wk] : Type@i }}
            by (eapply exp_eq_compose_typ; mauto 2; econstructor; mauto 2).
          assert {{ Ψ, A[σ∘τ], A[σ∘τ][Wk], (Eq A[Wk∘Wk] #1 #0)[q (q (σ∘τ))] ⊢ A[σ∘τ][Wk∘Wk∘Wk] ≈ A[σ∘τ][Wk][Wk∘Wk] : Type@i }}
            by (eapply exp_eq_compose_typ; mauto 2; econstructor; mauto 2).
          eapply mk_eq_glu_exp_pred with (B:={{{ A[σ∘τ][Wk][Wk][Wk] }}}) (M:={{{ #2 }}}) (N:={{{ #1 }}}); mauto 3.
          + transitivity {{{ (Eq A[Wk∘Wk] #1 #0)[q (q (σ∘τ))][Wk] }}}; [eapply exp_eq_compose_typ|]; mauto 2.
            transitivity {{{ (Eq A[σ∘τ][Wk∘Wk] #1 #0)[Wk] }}}; [eapply wf_eq_typ_exp_sub_cong|]; [eapply glu_rel_eq_eqrec_synprop_gen_A|idtac|idtac]; mauto 2.
            transitivity {{{ (Eq A[σ∘τ][Wk∘Wk][Wk] #1[Wk] #0[Wk]) }}}.
            * eapply wf_exp_eq_eq_sub; mauto 3.
              eapply exp_sub_typ; mauto 3.
              econstructor; mauto 3.
            * assert {{ Ψ, A[σ∘τ], A[σ∘τ][Wk] ⊢ A[σ∘τ][Wk∘Wk] ≈ A[σ∘τ][Wk][Wk] : Type@i }} by (eapply exp_eq_compose_typ; mauto 2; econstructor; mauto 2).
              assert {{ Ψ, A[σ∘τ], A[σ∘τ][Wk], (Eq A[Wk∘Wk] #1 #0)[q (q (σ∘τ))] ⊢ A[σ∘τ][Wk∘Wk][Wk] ≈ A[σ∘τ][Wk][Wk][Wk] : Type@i }} by (eapply wf_eq_typ_exp_sub_cong; mauto 2).
              eapply wf_exp_eq_eq_cong; mauto 2; try (eapply wf_exp_eq_conv'; [apply wf_exp_eq_var_weaken|]; mautosolve 2).
          + repeat (eapply exp_sub_typ; mauto 3).
          + do 2 (eapply glu_univ_elem_typ_resp_exp_eq; [eassumption | | mautosolve 2]).
            eapply glu_univ_elem_typ_monotone; mauto 2.
            eapply weakening_compose; mauto 3.
            repeat (eapply weakening_compose; mauto 3).
          + eapply glu_univ_elem_trm_resp_typ_exp_eq with (A:=({{{ A[σ∘τ][Wk][Wk∘Wk] }}})); mauto 2.
            eapply glu_univ_elem_trm_resp_exp_eq with (M:=({{{ #0[Wk∘Wk] }}})); eauto 2.
            * eapply glu_univ_elem_exp_monotone with (Γ:={{{ Ψ, A[σ∘τ] }}}); mauto 2.
              -- eapply var0_glu_elem; mauto 2.
              -- eapply weakening_compose; mauto 3.
            * transitivity {{{ #0[Wk][Wk]}}}.
              ++ eapply wf_exp_eq_conv' with (i:=i); [eapply wf_exp_eq_sub_compose with (A:={{{ A[σ∘τ][Wk] }}})|]; mauto 3.
              ++ rewrite H87.
                 transitivity {{{ #1[Wk] }}}; [| mautosolve 3].
                 eapply wf_exp_eq_sub_cong; mauto 3.
          + eapply glu_univ_elem_trm_resp_exp_eq with (M:=({{{ #0[Wk] }}})); mauto 2.
            eapply glu_univ_elem_exp_monotone with (Γ:={{{ Ψ, A[σ∘τ], A[σ∘τ][Wk] }}}); mauto 3.
            replace (S (length Ψ)) with (length ({{{ Ψ, A[σ∘τ] }}})) by auto.
              eapply var0_glu_elem; mauto 2.
              eapply glu_univ_elem_typ_monotone; mauto 2.
          + econstructor.
            econstructor; [eapply var_per_bot |].
            intros Ψ' τ' **.
            match_by_head1 read_ne ltac:(fun H => inversion H; subst). simpl.
            match goal with
            | [ H : {{ Ψ' ⊢w τ' : ^?Ψ0 }} |- _ ] =>
                eapply var_weaken_gen with (Γ1:=nil) (Γ2:={{{Ψ, A[σ∘τ], A[σ∘τ][Wk]}}}) in H as Hvar; simpl in *; eauto
            end.
            eapply wf_exp_eq_conv'; [mautosolve 2 |].
            eapply wf_exp_eq_conv'; [| mautosolve 3].
            eapply wf_exp_eq_sub_cong; [| mautosolve 3].
            eapply exp_eq_sub_compose_typ; mautosolve 2.
      }
      clear_glu_ctx Δ.
      destruct_glu_rel_exp_with_sub_nouip.
      simplify_evals.
      match_by_head glu_univ_elem ltac:(fun H => directed invert_glu_univ_elem_nouip H).
      dir_inversion_clear_by_head read_ne.
      handle_functional_glu_univ_elem.
      inversion_clear_by_head eq_glu_exp_pred.
      destruct_glu_eq.
      unfold univ_glu_exp_pred' in *.
      destruct_conjs.
      clear_dups.
      rename Γ0 into Ψ.

      match goal with
      | _ : {{ Rtyp a in length Ψ ↘ ^?VAστ' }} ,
          _ : {{ Rnf ⇓ a m1 in length Ψ ↘ ^?VM1στ' }} ,
            _ : {{ Rnf ⇓ a m2 in length Ψ ↘ ^?VM2στ' }} |- _  =>
        rename VAστ' into VAστ;
        rename VM1στ' into VM1στ;
        rename VM2στ' into VM2στ
      end.

      assert {{ Ψ ⊢ A[σ∘τ] ® glu_typ_top i a}} as [] by (eapply realize_glu_typ_top; mauto 2).
      assert {{ Ψ ⊢ M1[σ∘τ] : A[σ∘τ] ® m1 ∈ glu_elem_top i a }} as [] by (eapply realize_glu_elem_top; eassumption).
      assert {{ Ψ ⊢ M2[σ∘τ] : A[σ∘τ] ® m2 ∈ glu_elem_top i a }} as [] by (eapply realize_glu_elem_top with (El:=El); eauto).
      assert {{ Ψ , A[σ∘τ] ⊢ BR[q (σ∘τ)] : B[Id,,#0,,refl A[Wk] #0][q (σ∘τ)] ® m5 ∈ glu_elem_top i0 m }} as [] by (eapply realize_glu_elem_top; eauto).
      assert {{ Ψ, A[σ∘τ], A[σ∘τ][Wk], (Eq A[Wk∘Wk] #1 #0)[q (q (σ∘τ))] ⊢ B[q (q (q (σ∘τ)))] ® glu_typ_top j m4 }} as [] by (eapply realize_glu_typ_top; eauto).
      assert {{ Γ ⊢ eqrec N as Eq A M1 M2 return B | refl -> BR end : B[Id,,M1,,M2,,N] }} by mauto 2.
      assert {{ Ψ ⊢ B[Id,,M1,,M2,,N][σ][τ] ≈ B[Id,,M1,,M2,,N][σ∘τ] : Type@j }} as -> by mauto 3.
      assert {{ Ψ ⊢ eqrec N as Eq A M1 M2 return B | refl -> BR end[σ][τ] ≈ eqrec N as Eq A M1 M2 return B | refl -> BR end[σ∘τ] : B[Id,,M1,,M2,,N][σ∘τ] }} as -> by mauto 3.
      assert {{ Ψ ⊢ A[σ∘τ][Id] ≈ A[σ∘τ] : Type@i }} by mauto 2.
      eapply (@wf_exp_eq_eqrec_cong_sub _ _ Γ i j); fold nf_to_exp; fold ne_to_exp; eauto.
      * transitivity {{{ A[σ∘τ][Id] }}}; mauto 3.
      * assert {{ Ψ ⊢ M1[σ∘τ][Id] ≈ VM1στ : A[σ∘τ][Id] }} by mauto 3.
        eapply wf_exp_eq_conv'; mauto 2.
        transitivity {{{ M1[σ∘τ][Id] }}}; [mauto 4 | mauto 2].
      * assert {{ Ψ ⊢ M2[σ∘τ][Id] ≈ VM2στ : A[σ∘τ][Id] }} by mauto 3.
        eapply wf_exp_eq_conv'; mauto 2.
        transitivity {{{ M2[σ∘τ][Id] }}}; [mauto 4 | mauto 2].
      * destruct_by_head glu_bot.
        assert {{ Ψ ⊢ (Eq A M1 M2)[σ∘τ] ≈ Eq A[σ∘τ] M1[σ∘τ] M2[σ∘τ] : Type@i }} by mauto 2.
        assert {{ Γ ⊢ Eq A M1 M2 : Type@i }} by mauto 2.
        assert {{ Ψ ⊢ (Eq A M1 M2)[σ∘τ][Id] ≈ (Eq A M1 M2)[σ∘τ] : Type@i }} by mauto 3.
        eapply wf_exp_eq_conv' with (A:={{{ (Eq A M1 M2)[σ∘τ][Id] }}}); [| mauto 2].
        transitivity {{{ N[σ∘τ][Id] }}}; [mautosolve 4 | mauto 3].
      * assert {{ Ψ , A[σ∘τ] ⊢w Id : Ψ , A[σ∘τ] }} by mauto 3.
        assert {{ Ψ , A[σ∘τ] ⊢ BR[q (σ∘τ)][Id] ≈ BR' : B[Id,,#0,,refl A[Wk] #0][q (σ∘τ)][Id] }} by mauto 2.
        clear dependent Γ. clear dependent Δ. gen_presups.
        eapply wf_exp_eq_conv' with (A:={{{ B[Id,,#0,,refl A[Wk] #0][q (σ∘τ)][Id] }}}); mauto 2.
        transitivity {{{ BR[q (σ∘τ)][Id] }}}; [mautosolve 4 | mautosolve 2].
      * transitivity {{{ B[q (q (q (σ∘τ)))][Id] }}}; mauto 4.
Qed.

#[export]
Hint Resolve glu_rel_eq_eqrec : mctt.
