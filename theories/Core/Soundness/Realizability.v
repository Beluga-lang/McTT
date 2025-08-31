From Coq Require Import Nat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Soundness.LogicalRelation Require Export Core.
Import Domain_Notations.

Open Scope list_scope.

Lemma wf_ctx_sub_ctx_lookup : forall n A Γ,
    {{ #n : A ∈ Γ }} ->
    forall Δ,
      {{ ⊢ Δ ⊆ Γ}} ->
      exists Δ1 A0 Δ2 A',
        Δ = Δ1 ++ A0 :: Δ2 /\
          n = length Δ1 /\
          A' = iter (S n) (fun A => {{{ A[Wk] }}}) A0 /\
          {{ #n : A' ∈ Δ }} /\
          {{ Δ ⊢ A' ⊆ A }}.
Proof.
  induction 1; intros; progressive_inversion.
  - exists nil.
    repeat eexists; mauto 4.
  - edestruct IHctx_lookup as [Δ1 [? [? [? [? [? [? []]]]]]]]; eauto 3.
    exists (A0 :: Δ1). subst.
    repeat eexists; mauto 4.
Qed.

Lemma var_arith : forall Γ1 Γ2 (A : typ),
    length (Γ1 ++ A :: Γ2) - length Γ2 - 1 = length Γ1.
Proof.
  intros.
  rewrite List.length_app. simpl.
  lia.
Qed.

Lemma var_weaken_gen : forall Δ σ Γ,
    {{ Δ ⊢w σ : Γ }} ->
    forall Γ1 Γ2 A0,
      Γ = Γ1 ++ A0 :: Γ2 ->
      {{ Δ ⊢ #(length Γ1)[σ] ≈ #(length Δ - length Γ2 - 1) : ^(iter (S (length Γ1)) (fun A => {{{ A[Wk] }}}) A0)[σ] }}.
Proof.
  induction 1; intros; subst; gen_presups.
  - pose proof (app_ctx_vlookup _ _ _ _ ltac:(eassumption) eq_refl) as Hvar.
    gen_presup Hvar.
    clear_dups.
    apply wf_sub_id_inversion in Hτ.
    pose proof (wf_ctx_sub_length _ _ Hτ).
    transitivity {{{ #(length Γ1)[Id] }}}; [mauto 3 |].
    replace (length Γ) with (length (Γ1 ++ {{{ Γ2, A0 }}})) by lia.
    rewrite var_arith, H.
    bulky_rewrite.
  - pose proof (app_ctx_vlookup _ _ _ _ HΔ0 eq_refl) as Hvar.
    pose proof (app_ctx_lookup Γ1 A0 Γ2 _ eq_refl).
    gen_presup Hvar.
    clear_dups.
    assert {{ ⊢ Δ', A }} by mauto 3.
    assert {{ Δ', A ⊢s Wk : ^(Γ1 ++ {{{ Γ2, A0 }}}) }} by mauto 3.
    transitivity {{{ #(length Γ1)[Wk∘τ] }}}; [mauto 3 |].
    rewrite H1.
    etransitivity; [eapply wf_exp_eq_sub_compose; mauto 3 |].
    pose proof (wf_ctx_sub_length _ _ H0).

    rewrite <- @exp_eq_sub_compose_typ; mauto 2.
    deepexec wf_ctx_sub_ctx_lookup ltac:(fun H => destruct H as [Γ1' [? [Γ2' [? [-> [? [-> []]]]]]]]).
    repeat rewrite List.length_app in *.
    replace (length Γ1) with (length Γ1') in * by lia.
    clear_refl_eqs.
    replace (length Γ2) with (length Γ2') by (simpl in *; lia).

    etransitivity.
    + eapply wf_exp_eq_sub_cong; [ |mauto 3].
      eapply wf_exp_eq_subtyp'.
      * eapply wf_exp_eq_var_weaken; [mauto 3|]; eauto.
      * mauto 4.
    + eapply wf_exp_eq_subtyp'.
      * eapply IHweakening with (Γ1 := A :: _).
        reflexivity.
      * eapply wf_subtyp_subst; [ |mauto 3].
        simpl. eapply wf_subtyp_subst; mauto 3.
Qed.

Lemma var_glu_elem_bot : forall a i P El Γ A,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ, A ⊢ #0 : A[Wk] ® !(length Γ) ∈ glu_elem_bot i a }}.
Proof.
  intros. saturate_glu_info.
  econstructor; mauto 4.
  - eapply glu_univ_elem_typ_monotone; eauto.
    mauto 4.
  - intros. progressive_inversion.
    exact (var_weaken_gen _ _ _ H2 nil _ _ eq_refl).
Qed.

#[local]
Hint Rewrite -> wf_sub_eq_extend_compose using mauto 4 : mctt.

Theorem realize_glu_univ_elem_gen : forall a i P El,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    (forall Γ A R,
        {{ DF a ≈ a ∈ per_univ_elem i ↘ R }} ->
        {{ Γ ⊢ A ® P }} ->
        {{ Γ ⊢ A ® glu_typ_top i a }}) /\
      (forall Γ M A m,
          (** We repeat this to get the relation between [a] and [P]
              more easily after applying [induction 1.] *)
          {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
          {{ Γ ⊢ M : A ® m ∈ glu_elem_bot i a }} ->
          {{ Γ ⊢ M : A ® ⇑ a m ∈ El }}) /\
      (forall Γ M A m R,
          (** We repeat this to get the relation between [a] and [P]
              more easily after applying [induction 1.] *)
          {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
          {{ Γ ⊢ M : A ® m ∈ El }} ->
          {{ DF a ≈ a ∈ per_univ_elem i ↘ R }} ->
          {{ Dom m ≈ m ∈ R }} ->
          {{ Γ ⊢ M : A ® m ∈ glu_elem_top i a }}).
Proof.
  simpl. induction 1 using glu_univ_elem_ind.
  all:split; [| split]; intros;
    apply_equiv_left;
    gen_presups;
    try match_by_head1 per_univ_elem ltac:(fun H => pose proof (per_univ_then_per_top_typ H));
    match_by_head glu_elem_bot ltac:(fun H => destruct H as []);
    destruct_all.
  - econstructor; eauto; intros.
    progressive_inversion.
    transitivity {{{ Type@j[σ] }}}; mauto 4.
  - handle_functional_glu_univ_elem.
    match_by_head glu_univ_elem invert_glu_univ_elem_nouip.
    clear_dups.
    apply_equiv_left.
    repeat split; eauto.
    repeat eexists.
    + glu_univ_elem_econstructor; eauto; reflexivity.
    + simpl. repeat split.
      * rewrite <- H5. trivial.
      * intros.
        saturate_weakening_escape.
        rewrite <- wf_exp_eq_typ_sub; try eassumption.
        rewrite <- H5.
        firstorder.
  - deepexec glu_univ_elem_per_univ ltac:(fun H => pose proof H).
    unfold per_univ in H10. deex.
    firstorder.
    specialize (H _ _ _ H8) as [? []].
    econstructor; mauto 3.
    + apply_equiv_left. trivial.
    + intros.
      saturate_weakening_escape.
      deepexec H ltac:(fun H => destruct H).
      progressive_invert H14.
      deepexec H18 ltac:(fun H => pose proof H).
      functional_read_rewrite_clear.
      bulky_rewrite.

  - econstructor; eauto; intros.
    progressive_inversion.
    transitivity {{{ ℕ[σ] }}}; mauto 3.
  - handle_functional_glu_univ_elem.
    match_by_head glu_univ_elem invert_glu_univ_elem_nouip.
    apply_equiv_left.
    repeat split; eauto.
    econstructor; trivial.

    intros.
    saturate_weakening_escape.
    assert {{ Δ ⊢ A[σ] ≈ ℕ[σ] : Type @ i }} by mauto 3.
    rewrite <- wf_exp_eq_nat_sub; try eassumption.
    mauto 3.
  - econstructor; mauto 3.
    + bulky_rewrite. mauto 3.
    + apply_equiv_left. trivial.
    + intros.
      saturate_weakening_escape.
      bulky_rewrite.
      mauto using glu_nat_readback.

  - match_by_head pi_glu_typ_pred progressive_invert.
    handle_per_univ_elem_irrel.
    invert_per_univ_elem H6.
    econstructor; eauto; intros.
    + gen_presups. trivial.
    + saturate_weakening_escape.
      assert {{ Γ ⊢w Id : Γ }} by mauto 4.
      assert {{ Δ ⊢ IT[σ] ® IP }} by (eapply glu_univ_elem_typ_monotone; mauto 2).
      dir_inversion_clear_by_head read_typ.
      assert {{ Γ ⊢ IT ® glu_typ_top i a }} as [] by mauto 3.
      bulky_rewrite.
      simpl. apply wf_exp_eq_pi_cong'; [firstorder |].
      pose proof (var_per_elem (length Δ) H0).
      destruct_rel_mod_eval.
      simplify_evals.
      destruct (H2 _ ltac:(eassumption) _ ltac:(eassumption)) as [? []].
      assert (IEl {{{ Δ, IT[σ] }}} {{{ IT[σ][Wk] }}} {{{ #0 }}} d{{{ ⇑! a (length Δ) }}}) by mauto 3 using var_glu_elem_bot.
      autorewrite with mctt in H30.
      specialize (H14 {{{ Δ, IT[σ] }}} {{{ σ∘Wk }}} _ _ ltac:(mauto) ltac:(eassumption) ltac:(eassumption)).
      specialize (H8 _ _ _ ltac:(eassumption) ltac:(eassumption)) as [].
      etransitivity; [| eapply H32]; mauto 3.
  - handle_functional_glu_univ_elem.
    apply_equiv_left.
    invert_glu_rel1.
    econstructor; try eapply per_bot_then_per_elem; eauto.

    intros.
    saturate_weakening_escape.
    saturate_glu_info.
    match_by_head1 per_univ_elem invert_per_univ_elem.
    destruct_rel_mod_eval.
    simplify_evals.
    eexists; repeat split; mauto 3.
    eapply H2; eauto.
    assert {{ Δ ⊢ M[σ] : A[σ] }} by mauto 3.
    bulky_rewrite_in H23.
    unshelve (econstructor; eauto).
    + trivial.
    + eassert {{ Δ ⊢ M[σ] N : ^_ }} by (eapply wf_app'; eassumption).
      autorewrite with mctt in H25.
      trivial.
    + mauto using domain_app_per.
    + intros.
      saturate_weakening_escape.
      progressive_invert H26.
      destruct (H15 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) equiv_n).
      handle_functional_glu_univ_elem.
      autorewrite with mctt.

      etransitivity.
      * rewrite sub_decompose_q_typ; mauto 4.
      * simpl.
        rewrite <- @sub_eq_q_sigma_id_extend; mauto 4.
        rewrite <- @exp_eq_sub_compose_typ; mauto 3;
          [eapply wf_exp_eq_app_cong' |].
        -- specialize (H12 _ {{{σ ∘ σ0}}} _ ltac:(mauto 3) ltac:(eassumption)).
           rewrite wf_exp_eq_sub_compose with (M := M) in H12; mauto 3.
           bulky_rewrite_in H12.
        -- rewrite <- @exp_eq_sub_compose_typ; mauto 3.
        -- econstructor; mauto 3.
           autorewrite with mctt.
           rewrite <- @exp_eq_sub_compose_typ; mauto 3.

  - handle_functional_glu_univ_elem.
    handle_per_univ_elem_irrel.
    pose proof H8.
    invert_per_univ_elem H8.
    econstructor; mauto 3.
    + invert_glu_rel1. trivial.
    + eapply glu_univ_elem_trm_typ; eauto.
    + intros.
      saturate_weakening_escape.
      invert_glu_rel1. clear_dups.
      progressive_invert H20.

      destruct (H11 _ _ _ ltac:(eassumption) ltac:(eassumption)) as [].
      assert {{ Δ ⊢ IT[σ] ® IP }} by (eapply glu_univ_elem_typ_monotone; mauto 2).
      specialize (H26 _ _ _ H19 H9).
      rewrite H5 in *.
      autorewrite with mctt.
      eassert {{ Δ ⊢ M[σ] : ^_ }} by (mauto 2).
      autorewrite with mctt in H28.
      rewrite @wf_exp_eq_pi_eta' with (M := {{{ M[σ] }}}); [| trivial].
      cbn [nf_to_exp].
      eapply wf_exp_eq_fn_cong'; eauto.

      pose proof (var_per_elem (length Δ) H0).
      destruct_rel_mod_eval.
      simplify_evals.
      destruct (H2 _ ltac:(eassumption) _ ltac:(eassumption)) as [? []].
      specialize (H12 _ _ _ _ ltac:(trivial) (var_glu_elem_bot _ _ _ _ _ _ H H27)).
      autorewrite with mctt in H12.
      specialize (H14 {{{Δ, IT[σ]}}} {{{σ ∘ Wk}}} _ _ ltac:(mauto) ltac:(eassumption) ltac:(eassumption)) as [? []].
      apply_equiv_left.
      destruct_rel_mod_app.
      simplify_evals.
      deepexec H1 ltac:(fun H => pose proof H).
      specialize (H31 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)) as [].
      specialize (H38 _ {{{Id}}} _ ltac:(mauto 3) ltac:(eassumption)).
      do 2 (rewrite wf_exp_eq_sub_id in H38; mauto 3).
      etransitivity; [|eassumption].
      simpl.
      assert {{ Δ, IT[σ] ⊢ #0 : IT[σ∘Wk] }} by (rewrite <- @exp_eq_sub_compose_typ; mauto 3).
      rewrite <- @sub_eq_q_sigma_id_extend; mauto 4.
      rewrite <- @exp_eq_sub_compose_typ; mauto 2.
      * eapply wf_exp_eq_app_cong'; [| mauto 3].
        symmetry.
        rewrite <- wf_exp_eq_pi_sub; mauto 4.
      * eapply sub_q; mauto 4.
      * gen_presup H39; econstructor; mauto 3.

  - match_by_head sigma_glu_typ_pred progressive_invert.
    handle_per_univ_elem_irrel.
    invert_per_univ_elem H6.
    econstructor; eauto; intros.
    + gen_presups. trivial.
    + saturate_weakening_escape.
      destruct_rel_mod_eval. simplify_evals.
      assert {{ Γ ⊢w Id : Γ }} by mauto 4.
      assert {{ Δ ⊢ FT[σ] ® FP }} by mauto 3.
      assert (FP Γ {{{ FT[Id] }}}) as HFTId by mauto 3.
      bulky_rewrite_in HFTId.
      assert {{ Γ ⊢ FT[Id] ≈ FT : Type@i }} by mauto 3.
      dir_inversion_clear_by_head read_typ.
      assert {{ Γ ⊢ FT ® glu_typ_top i a }} as [] by mauto 3.
      bulky_rewrite.
      simpl. apply wf_exp_eq_sigma_cong'; [firstorder |].
      pose proof (var_per_elem (length Δ) H0).
      destruct_rel_mod_eval. simplify_evals. 
      destruct (H2 _ ltac:(eassumption) _ ltac:(eassumption)) as [? []].
      assert (FEl {{{ Δ, FT[σ] }}} {{{ FT[σ][Wk] }}} {{{ #0 }}} d{{{ ⇑! a (length Δ) }}}) by mauto 3 using var_glu_elem_bot.
      autorewrite with mctt in H31.
      specialize (H14 {{{ Δ, FT[σ] }}} {{{ σ∘Wk }}} _ _ ltac:(mauto) ltac:(eassumption) ltac:(eassumption)).
      specialize (H8 _ _ _ ltac:(eassumption) ltac:(eassumption)) as [].
      etransitivity; [| eapply H33]; mauto 3.
  
  - handle_functional_glu_univ_elem.
    apply_equiv_left.
    invert_glu_rel1.
    invert_glu_univ_elem H9.
    invert_per_univ_elem H17.
    assert (fst_rel d{{{ ⇑ a fst m  }}} d{{{ ⇑ a fst m  }}}) as equiv_fst. {
      eapply per_bot_then_per_elem; eauto.
      apply fst_bot_per_bot. auto.
    }
    destruct_rel_mod_eval. simplify_evals.
    eapply mk_sigma_glu_exp_pred with (equiv_m:=equiv_fst); mauto 3.
    + eapply per_bot_then_per_elem; eauto.
    + intros.
      assert (HSig : 
        forall {Δ σ}, {{Δ ⊢s σ : Γ }} -> {{ Δ ⊢ A[σ] ≈ Σ FT[σ] ST[q σ] : Type@i }}). {
        intros. 
        assert {{ Δ0 ⊢ (Σ FT ST)[σ0] ≈ Σ FT[σ0] ST[q σ0] : Type@i }}. {
          eapply wf_exp_eq_conv' with (A:={{{Type@i}}}); mauto 3.
          apply exp_eq_refl; econstructor; mauto 3.
        }
        rewrite <- H25.
        eapply wf_eq_typ_exp_sub_cong; mauto 3.
      }
      assert (FEl Δ {{{ FT[σ] }}} {{{ (fst M)[σ] }}} d{{{ ⇑ a fst m }}}). {
        eapply H14; mauto 3.
        econstructor; mauto 3.
        * eapply wf_exp_sub; mauto 3.
        * intros.
          saturate_weakening_escape.
          dependent destruction H25.
          assert {{ Δ0 ⊢w σ∘σ0 : Γ  }} by mauto 3.
          specialize (H12 _ {{{σ∘σ0}}} _ ltac:(eassumption) ltac:(eassumption) ).
          assert {{ Δ0 ⊢ FT[σ][σ0] ≈ FT[σ∘σ0] : Type@i }} by mauto 3.  
          assert {{ Δ0 ⊢ (fst M)[σ][σ0] ≈ (fst M)[σ∘σ0] : FT[σ∘σ0] }}. {
            symmetry; eapply wf_exp_eq_sub_compose; mauto 3.
          }
          assert {{ Δ0 ⊢ (fst M[σ∘σ0]) ≈ (fst M)[σ∘σ0] : FT[σ∘σ0] }}. {
            symmetry; eapply wf_exp_eq_fst_sub; mauto 3.
          }
          assert {{ Δ0, FT[σ∘σ0] ⊢ ST[q (σ∘σ0)] : Type@i }}. {
            eapply wf_conv'; [eapply wf_exp_sub | ]; mauto 4.
          }
          eapply wf_exp_eq_conv; mauto 3.
          rewrite H30. rewrite <- H31. 
          eapply wf_exp_eq_fst_cong; mauto 3; fold nf_to_exp; fold ne_to_exp.
          eapply wf_exp_eq_conv'; mauto 3.
      }
      split; auto.
      assert {{ Δ ⊢ ST[Id,,fst M][σ] ≈ ST[σ,,(fst M)[σ]] : Type@i }} by 
        (eapply exp_eq_elim_sub_lhs_typ_gen; mauto 3).
      eapply H2; mauto 3. 
      eapply H1 with (equiv_c:=equiv_fst) in H21 as Hglu.
      eapply mk_glu_elem_bot; mauto 3.
      gen_presups. eapply wf_conv; [eapply wf_exp_sub| | ]; mauto 3.
      intros.

      dependent destruction H27.
      assert {{ Δ0 ⊢w σ∘σ0 : Γ }} by mauto 3.
      assert {{ Δ0 ⊢s σ∘σ0 : Γ }} by mauto 3.
      specialize (H12 _ {{{σ∘σ0}}} _ ltac:(eassumption) ltac:(eassumption) ).
      assert {{ Δ0 ⊢ ST[σ∘σ0,,fst M[σ∘σ0]] ≈ ST[Id,,fst M][σ∘σ0] : Type@i }}. {
        assert {{ Δ0 ⊢s σ∘σ0,,fst M[σ∘σ0] : Γ , FT }}. {
          econstructor; mauto 3.
          specialize (HSig _ _ ltac:(eassumption)).
          eapply wf_fst with (B:= {{{ ST[q (σ∘σ0)]}}}) (i:=i); mauto 3.
        }
        transitivity {{{ ST[σ∘σ0,,(fst M)[σ∘σ0]]}}}.
        eapply wf_exp_eq_conv'; [eapply wf_exp_eq_sub_cong | ]; mauto 3.
        eapply wf_sub_eq_extend_cong; mauto 3.
        symmetry; eapply wf_exp_eq_fst_sub; mauto 3.
        symmetry; eapply exp_eq_elim_sub_lhs_typ_gen; mauto 3.
      }
      assert {{ Δ0 ⊢ ST[σ,,(fst M)[σ]][σ0] ≈ ST[Id,,(fst M)][σ∘σ0] : Type@i }}. {
        assert {{ Γ ⊢s Id,,fst M : Γ , FT }}. {
          econstructor; mauto 3.
          eapply wf_conv'; [eapply wf_fst | ]; mauto 3.
        }
        transitivity {{{  ST[Id,,(fst M)][σ][σ0] }}}.
        eapply wf_eq_typ_exp_sub_cong; mauto 3.
        symmetry; eapply exp_eq_compose_typ; mauto 3.
      }
      assert {{ Δ0 ⊢ (snd M)[σ][σ0] ≈ (snd M)[σ∘σ0] : ST[Id,,(fst M)][σ∘σ0] }} by (symmetry; eapply wf_exp_eq_sub_compose; mauto 3).
      assert {{ Δ0 ⊢ (snd M[σ∘σ0]) ≈ (snd M)[σ∘σ0] : ST[Id,,(fst M)][σ∘σ0] }}. {
        eapply wf_exp_eq_conv'; [symmetry; eapply wf_exp_eq_snd_sub | ]; mauto 3.
      }
      assert {{ Δ0 ⊢ FT[σ∘σ0] : Type@i }} by mauto 3. 
      assert {{ Δ0, FT[σ∘σ0] ⊢ ST[q (σ∘σ0)] : Type@i }} by (eapply wf_conv'; [eapply wf_exp_sub | ]; mauto 4).
      rewrite H31. rewrite H32. rewrite <- H33.
      eapply wf_exp_eq_conv with (i:=i); [eapply wf_exp_eq_snd_cong | |]; mauto 3; fold nf_to_exp; fold ne_to_exp.
      gen_presups; mauto 3.
      transitivity {{{ST[σ∘σ0,,fst M[σ∘σ0]] }}}; mauto 3.
      eapply exp_eq_elim_sub_rhs_typ; mauto 3.
      eapply wf_fst; mauto 3.
      erewrite <- HSig; mauto 3.

  - handle_functional_glu_univ_elem.
    handle_per_univ_elem_irrel.
    pose proof H8.
    invert_per_univ_elem H8.
    econstructor; mauto 3.
    + invert_glu_rel1. trivial.
    + eapply glu_univ_elem_trm_typ; eauto.
    + intros.
      saturate_weakening_escape.
      invert_glu_rel1. clear_dups.
      progressive_invert H23.
      rewrite H21 in H4.
      replace (S (length Δ)) with (length ({{{ Δ, FT[σ] }}})) in * by (simpl; auto).

      assert {{ Δ, FT[σ] ⊢ ST[q σ] ≈ B' : Type@i }}. {
        assert {{ Dom (⇑! a (length Δ)) ≈ ⇑! a (length Δ) ∈ fst_rel }} by (eapply var_per_elem; eauto).
        destruct_by_head rel_mod_proj.
        destruct_rel_mod_eval.
        simplify_evals.
        assert (glu_typ_top i b {{{ Δ, FT[σ] }}} {{{ ST[σ∘Wk,,#0] }}}). {
          assert (HElB' : FEl {{{ Δ, FT[σ] }}} {{{ FT[σ][Wk] }}} {{{ #0 }}} d{{{ ⇑! a (length Δ) }}}). 
          {
            eapply H12; mauto 3.
            eapply var_glu_elem_bot; eauto.
          }
          assert {{ Δ, FT[σ] ⊢ FT[σ][Wk] ≈ FT[σ∘Wk] : Type@i }} by (symmetry; eapply exp_eq_compose_typ; mauto 4).
          rewrite H5 in HElB'.
          assert {{ Δ, FT[σ] ⊢w σ∘Wk : Γ}}. {
            eapply weakening_compose; mauto 3.
          }
          assert (SP d{{{ ⇑! a (length Δ) }}} H28 {{{ Δ, FT[σ] }}} {{{ ST[σ∘Wk,,#0] }}}) by mauto.
          eapply H2 with (equiv_c:=H28) in H9 .  destruct_all.
          mauto.
        }
        destruct H5. 
        eapply H24 with (σ:={{{ Id }}} ) in H23 as HB.
        simpl in *. functional_read_rewrite_clear.
        rewrite <- HB. mauto 3.
        apply weakening_id; mauto.
      }

      destruct_by_head rel_mod_proj.
      destruct_rel_mod_eval.
      simplify_evals.
      assert {{ Γ ⊢w Id : Γ }} by mauto 4.
      destruct (H17 _ σ ltac:(eassumption)) as [].
      simplify_evals.
      rename b0 into m1. rename c into m2.
      assert (HSP: SP m1 equiv_m Δ {{{ ST[σ,,(fst M)[σ]] }}}) by eauto.
      eapply H2 with (equiv_c:=equiv_m) in H26 as IH; eauto. destruct_all.
      eapply H1 with (equiv_c:=equiv_m) in H26 as Hgluu; eauto.
      eapply H13 with (R:=fst_rel) in H7; eauto.
      eapply H25 in HSP; mauto 3.
      eapply H30 with (R:=(x m1 m1 equiv_b_b')) in H24; mauto 3.
      assert {{ Δ ⊢ A[σ] ≈ Σ FT[σ] ST[q σ] : Type@i }}. {
         assert {{ Δ ⊢ (Σ FT ST)[σ] ≈ Σ FT[σ] ST[q σ] : Type@i }}. {
          eapply wf_exp_eq_conv' with (A:={{{Type@i}}}); mauto 3.
          apply exp_eq_refl; econstructor; mauto 3.
        }
        rewrite <- H32.
        eapply wf_eq_typ_exp_sub_cong; mauto 3.
      }
      rewrite H32.
      transitivity {{{ ⟨ fst M[σ] ; snd M[σ] : ST[q σ] ⟩}}}.
      eapply wf_exp_eq_sigma_eta'; mauto 3.
      eapply wf_exp_eq_pair_cong with (i:=i); mauto 3; fold nf_to_exp; fold ne_to_exp.
      * destruct H7.
        eapply H37 with (σ:={{{ Id }}}) in H23_ ; mauto 3.
        assert {{ Δ ⊢ FT[σ][Id] ≈ FT[σ] : Type@i }} by mauto 3.
        bulky_rewrite_in H23_.
        rewrite <- H23_. symmetry. mauto 3. 
      * assert {{ Δ ⊢w Id : Δ }} by mauto using weakening_id.
        destruct H24.
        eapply H38 with (σ:={{{ Id }}}) in H23_0; mauto 3.
        assert {{ Δ ⊢ fst M[σ] ≈ (fst M)[σ] : FT[σ] }} by (symmetry; mauto 3).
        apply invert_eq_sub_id_typ in H23_0.
        apply invert_eq_sub_id in H23_0.
        eapply wf_exp_eq_conv'; [rewrite <- H23_0 | ]; mauto 3.
        eapply wf_exp_eq_conv'; [symmetry; eapply wf_exp_eq_snd_sub | ]; mauto 3.
        eapply wf_eq_typ_exp_sub_cong; mauto 3.
        etransitivity; [| symmetry; eapply exp_eq_elim_sub_rhs_typ ]; mauto 3.
        eapply wf_eq_typ_exp_sub_cong; mauto 3.
        eapply wf_sub_eq_extend_cong; mauto 3.
        gen_presups; mauto 3.

  - match_by_head eq_glu_typ_pred progressive_invert.
    econstructor; eauto; intros.
    + gen_presups; trivial.
    + saturate_weakening_escape.
      dir_inversion_clear_by_head read_typ.
      assert {{ Γ ⊢ B ® glu_typ_top i a }} as [] by mauto 3.
      assert {{ Γ ⊢ M : B ® m ∈ glu_elem_top i a }} as [] by mauto 3.
      assert {{ Γ ⊢ N : B ® n ∈ glu_elem_top i a }} as [] by mauto 3.
      bulky_rewrite.
      simpl.
      eapply wf_exp_eq_eq_cong; firstorder.

  - handle_functional_glu_univ_elem.
    invert_glu_rel1.
    mauto.

  - handle_functional_glu_univ_elem.
    invert_glu_rel1.
    econstructor; intros; mauto 3.

    saturate_weakening_escape.
    destruct_glu_eq;
      dir_inversion_clear_by_head read_nf.
    + pose proof (PER_refl1 _ _ _ _ _ H21).
      gen_presups.
      assert {{ Γ ⊢ B ® glu_typ_top i a }} as [] by mauto 3.
      assert {{ Γ ⊢ N : B ® m' ∈ glu_elem_top i a }} as [] by (rewrite <- H19; mauto 2).
      assert {{ Γ ⊢ Eq B M N ≈ Eq B N N : Type@i }} by (eapply wf_exp_eq_eq_cong; mauto 3).
      assert {{ Γ ⊢ Eq B M'' M'' ≈ Eq B N N : Type@i }} by (eapply wf_exp_eq_eq_cong; mauto 3).
      assert {{ Γ ⊢ A ≈ Eq B N N : Type@i }} by mauto 3.
      assert {{ Γ ⊢ refl B M'' ≈ refl B N : Eq B M'' M'' }} by mauto 3.
      assert {{ Γ ⊢ refl B M'' ≈ refl B N : Eq B N N }} by mauto 3.
      assert {{ Γ ⊢ M' ≈ refl B N : A }} by mauto 4.
      simpl.

      transitivity {{{ (refl B N)[σ] }}}; [mauto 3 |].
      bulky_rewrite.
      transitivity {{{ refl (B[σ]) (N[σ]) }}};
        [ eapply wf_exp_eq_conv'; [econstructor |]; mauto 3 |].
      econstructor; mauto 3.
    + firstorder.

  - econstructor; eauto.
    intros.
    progressive_inversion.
    firstorder.
  - handle_functional_glu_univ_elem.
    apply_equiv_left.
    econstructor; eauto.
  - handle_functional_glu_univ_elem.
    invert_glu_rel1.
    econstructor; eauto.
    + intros s. destruct (H3 s) as [? []].
      mauto.
    + intros.
      progressive_inversion.
      specialize (H11 (length Δ)) as [? []].
      firstorder.
Qed.

Corollary realize_glu_typ_top : forall a i P El,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ A,
      {{ Γ ⊢ A ® P }} ->
      {{ Γ ⊢ A ® glu_typ_top i a }}.
Proof.
  intros.
  pose proof H.
  eapply glu_univ_elem_per_univ in H.
  simpl in *. destruct_all.
  eapply realize_glu_univ_elem_gen; eauto.
Qed.

Theorem realize_glu_elem_bot : forall a i P El,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ A M m,
      {{ Γ ⊢ M : A ® m ∈ glu_elem_bot i a }} ->
      {{ Γ ⊢ M : A ® ⇑ a m ∈ El }}.
Proof.
  intros.
  eapply realize_glu_univ_elem_gen; eauto.
Qed.

Theorem realize_glu_elem_top : forall a i P El,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ A M m,
      {{ Γ ⊢ M : A ® m ∈ El }} ->
      {{ Γ ⊢ M : A ® m ∈ glu_elem_top i a }}.
Proof.
  intros.
  pose proof H.
  eapply glu_univ_elem_per_univ in H.
  simpl in *. destruct_all.
  eapply realize_glu_univ_elem_gen; eauto.
  eapply glu_univ_elem_per_elem; eauto.
Qed.

#[export]
Hint Resolve realize_glu_typ_top realize_glu_elem_top : mctt.

Corollary var0_glu_elem : forall {i a P El Γ A},
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Γ, A ⊢ #0 : A[Wk] ® ⇑! a (length Γ) ∈ El }}.
Proof.
  intros.
  eapply realize_glu_elem_bot; mauto 4.
  eauto using var_glu_elem_bot.
Qed.
