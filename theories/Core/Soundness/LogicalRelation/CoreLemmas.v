From Coq Require Import Equivalence Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Soundness.LogicalRelation Require Import CoreTactics Definitions.
From Mctt.Core.Soundness.Weakening Require Export Lemmas.
Import Domain_Notations.

Lemma glu_nat_per_nat : forall Γ M a,
    glu_nat Γ M a ->
    {{ Dom a ≈ a ∈ per_nat }}.
Proof.
  induction 1; mauto.
Qed.

#[local]
Hint Resolve glu_nat_per_nat : mctt.

Lemma glu_nat_escape : forall Γ M a,
    glu_nat Γ M a ->
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ M : ℕ }}.
Proof.
  induction 1; intros;
    try match goal with
    | H : _ |- _ => solve [gen_presup H; mauto]
    end.
  assert {{ Γ ⊢w Id : Γ }} by mauto.
  match_by_head (per_bot m m) ltac:(fun H => specialize (H (length Γ)) as [M' []]).
  clear_dups.
  assert {{ Γ ⊢ M[Id] ≈ M' : ℕ }} by mauto.
  gen_presups.
  mauto.
Qed.

#[export]
Hint Resolve glu_nat_escape : mctt.

Lemma glu_nat_resp_ctx_eq : forall Γ M a Δ,
    glu_nat Γ M a ->
    {{ ⊢ Γ ≈ Δ }} ->
    glu_nat Δ M a.
Proof.
  induction 1; intros; mauto.
Qed.

#[local]
Hint Resolve glu_nat_resp_ctx_eq : mctt.

Add Parametric Morphism : glu_nat
    with signature wf_ctx_eq ==> eq ==> eq ==> iff as glu_ctx_env_sub_morphism_iff1.
Proof.
  split; mauto using glu_nat_resp_ctx_eq.
Qed.

Lemma glu_nat_resp_exp_eq : forall Γ M a,
    glu_nat Γ M a ->
    forall M',
    {{ Γ ⊢ M ≈ M' : ℕ }} ->
    glu_nat Γ M' a.
Proof.
  induction 1; intros; mauto 4.
  econstructor; trivial.
  intros.
  transitivity {{{ M[σ] }}}; mauto.
Qed.

#[local]
Hint Resolve glu_nat_resp_exp_eq : mctt.

Add Parametric Morphism Γ : (glu_nat Γ)
    with signature wf_exp_eq Γ {{{ ℕ }}} ==> eq ==> iff as glu_ctx_env_sub_morphism_iff2.
Proof.
  split; mauto using glu_nat_resp_exp_eq.
Qed.

Lemma glu_nat_readback : forall Γ M a,
    glu_nat Γ M a ->
    forall Δ σ M',
      {{ Δ ⊢w σ : Γ }} ->
      {{ Rnf ⇓ ℕ a in length Δ ↘ M' }} ->
      {{ Δ ⊢ M[σ] ≈ M' : ℕ }}.
Proof.
  induction 1; intros; progressive_inversion; gen_presups.
  - transitivity {{{ zero[σ] }}}; mauto 4.
  - assert {{ Δ ⊢ M'[σ] ≈ M0 : ℕ }} by mauto 4.
    transitivity {{{ (succ M')[σ] }}}; mauto 3.
    transitivity {{{ succ M'[σ] }}}; mauto 4.
  - mauto 4.
Qed.

#[global]
Ltac simpl_glu_rel :=
  apply_equiv_left;
  repeat invert_glu_rel1;
  apply_equiv_left;
  destruct_all;
  gen_presups.

Lemma glu_univ_elem_univ_lvl : forall i P El a,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ A,
      {{ Γ ⊢ A ® P }} ->
      {{ Γ ⊢ A : Type@i }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel; trivial.
Qed.

Lemma glu_univ_elem_typ_resp_exp_eq : forall i P El a,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ A A',
      {{ Γ ⊢ A ® P }} ->
      {{ Γ ⊢ A ≈ A' : Type@i }} ->
      {{ Γ ⊢ A' ® P }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel; mauto 4.

  split; [trivial |].
  intros.
  transitivity {{{ A[σ] }}}; mauto 4.
Qed.

Add Parametric Morphism i P El a (H : glu_univ_elem i P El a) Γ : (P Γ)
    with signature wf_exp_eq Γ {{{ Type@i }}} ==> iff as glu_univ_elem_typ_morphism_iff1.
Proof.
  split; intros; eapply glu_univ_elem_typ_resp_exp_eq; mauto 2.
Qed.

#[global]
Ltac destruct_glu_eq :=
  match_by_head1 glu_eq ltac:(fun H => dependent destruction H).

Lemma glu_univ_elem_trm_resp_typ_exp_eq : forall i P El a,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ M A m A',
      {{ Γ ⊢ M : A ® m ∈ El }} ->
      {{ Γ ⊢ A ≈ A' : Type@i }} ->
      {{ Γ ⊢ M : A' ® m ∈ El }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel; repeat split; intros; mauto 3.
  - firstorder.
  - econstructor; mauto 3.
  - destruct_by_head sigma_glu_exp_pred.
    econstructor; mauto 3.
  - econstructor; mauto 3.
    destruct_glu_eq; econstructor; mauto 3.
    intros.
    assert {{ Δ ⊢ A[σ] ≈ A'[σ] : Type@i }}; mauto 3.
  - transitivity {{{ A[σ] }}}; mauto 4.
  - assert {{ Δ ⊢ A[σ] ≈ A'[σ] : Type@i }}; mauto 3.
Qed.

Add Parametric Morphism i P El a (H : glu_univ_elem i P El a) Γ : (El Γ)
    with signature wf_exp_eq Γ {{{Type@i}}} ==> eq ==> eq ==> iff as glu_univ_elem_trm_morphism_iff1.
Proof.
  split; intros;
    eapply glu_univ_elem_trm_resp_typ_exp_eq;
    mauto 2.
Qed.

Lemma glu_univ_elem_resp_ctx_eq : forall i P El a,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ Δ,
      {{ ⊢ Γ ≈ Δ }} ->
      (forall A, {{ Γ ⊢ A ® P }} -> {{ Δ ⊢ A ® P }}) /\
        (forall A M m, {{ Γ ⊢ M : A ® m ∈ El }} -> {{ Δ ⊢ M : A ® m ∈ El }}).
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; split; intros;
    simpl_glu_rel; mauto 2;
    repeat match goal with
      | H: glu_univ_elem _ ?P ?El _ |- _ =>
          assert ((forall A : typ, {{ Γ ⊢ A ® P }} -> {{ Δ ⊢ A ® P }}) /\ (forall A M m, {{ Γ ⊢ M : A ® m ∈ El }} -> {{ Δ ⊢ M : A ® m ∈ El }})) as [] by eauto 2;
          fail_if_dup
      end;
    econstructor; mauto 4 using glu_nat_resp_ctx_eq.

  - split; mauto.
  - destruct_glu_eq; econstructor; mauto 4.
  - split; mauto 4.
Qed.

Lemma glu_univ_elem_typ_resp_ctx_eq : forall i P El a,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ A Δ,
      {{ Γ ⊢ A ® P }} ->
      {{ ⊢ Γ ≈ Δ }} ->
      {{ Δ ⊢ A ® P }}.
Proof.
  intros; gen A;
  eapply proj1; eauto using glu_univ_elem_resp_ctx_eq.
Qed.

Add Parametric Morphism i P El a (H : glu_univ_elem i P El a) : P
    with signature wf_ctx_eq ==> eq ==> iff as glu_univ_elem_typ_morphism_iff2.
Proof.
  intros.
  split; intros;
    eapply glu_univ_elem_typ_resp_ctx_eq;
    mauto 2.
Qed.

Lemma glu_univ_elem_trm_resp_ctx_eq : forall i P El a,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ A M m Δ,
      {{ Γ ⊢ M : A ® m ∈ El }} ->
      {{ ⊢ Γ ≈ Δ }} ->
      {{ Δ ⊢ M : A ® m ∈ El }}.
Proof.
  intros; gen m M A;
  eapply proj2; eauto using glu_univ_elem_resp_ctx_eq.
Qed.

Add Parametric Morphism i P El a (H : glu_univ_elem i P El a) : El
    with signature wf_ctx_eq ==> eq ==> eq ==> eq ==> iff as glu_univ_elem_trm_morphism_iff2.
Proof.
  intros.
  split; intros;
    eapply glu_univ_elem_trm_resp_ctx_eq;
    mauto 2.
Qed.

Lemma glu_nat_resp_wk' : forall Γ M a,
    glu_nat Γ M a ->
    forall Δ σ,
      {{ Γ ⊢ M : ℕ }} ->
      {{ Δ ⊢w σ : Γ }} ->
      glu_nat Δ {{{ M[σ] }}} a.
Proof.
  induction 1; intros; gen_presups.
  - econstructor.
    transitivity {{{ zero[σ] }}}; mauto.
  - econstructor; [ |mauto].
    transitivity {{{ (succ M')[σ] }}}; mauto 4.
  - econstructor; trivial.
    intros Δ' τ M' **.
    gen_presups.
    assert {{ Δ' ⊢w σ∘τ : Γ }} by mauto.
    assert {{ Δ' ⊢ M[σ∘τ] ≈ M' : ℕ }} by mauto 4.
    transitivity {{{ M[σ∘τ] }}}; mauto 4.
Qed.

Lemma glu_nat_resp_wk : forall Γ M a,
    glu_nat Γ M a ->
    forall Δ σ,
      {{ Δ ⊢w σ : Γ }} ->
      glu_nat Δ {{{ M[σ] }}} a.
Proof.
  mauto using glu_nat_resp_wk'.
Qed.

#[export]
Hint Resolve glu_nat_resp_wk : mctt.

Lemma glu_univ_elem_trm_escape : forall i P El a,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ M A m,
      {{ Γ ⊢ M : A ® m ∈ El }} ->
      {{ Γ ⊢ M : A }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel; mauto 4.
Qed.

Lemma glu_univ_elem_per_univ : forall i P El a,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ Dom a ≈ a ∈ per_univ i }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros; eexists;
    try solve [per_univ_elem_econstructor; mauto 3; try reflexivity].

  - subst. eapply per_univ_elem_core_univ'; trivial.
    reflexivity.
  - match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    mauto.
  - match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    per_univ_elem_econstructor; mauto.
Qed.

#[export]
Hint Resolve glu_univ_elem_per_univ : mctt.

Lemma glu_univ_elem_per_elem : forall i P El a,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ M A m R,
      {{ Γ ⊢ M : A ® m ∈ El }} ->
      {{ DF a ≈ a ∈ per_univ_elem i ↘ R }} ->
      {{ Dom m ≈ m ∈ R }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem_nouip H);
    simpl_glu_rel;
    try fold (per_univ j m m);
    mauto 4.

  - intros.
    destruct_rel_mod_app_nouip.
    destruct_rel_mod_eval_nouip.
    functional_eval_rewrite_clear.
    do_per_univ_elem_irrel_assert.
    econstructor; firstorder eauto.
  - destruct_by_head rel_mod_proj.
    destruct_rel_mod_eval_nouip.
    simplify_evals.
    functional_eval_rewrite_clear.
    do_per_univ_elem_irrel_assert.  
    econstructor; firstorder eauto.
    intuition.
  - handle_per_univ_elem_irrel.
    pose proof (PER_refl1 _ R).
    destruct_glu_eq; saturate_refl_for R; econstructor; mauto.
Qed.

Lemma glu_univ_elem_trm_typ : forall i P El a,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ M A m,
      {{ Γ ⊢ M : A ® m ∈ El }} ->
      {{ Γ ⊢ A ® P }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel;
    mauto 4.

  - econstructor; eauto.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    intros ? ? N n ? ? equiv_n.
    destruct_rel_mod_eval.
    enough (exists mn : domain, {{ $| m & n |↘ mn }} /\  {{ Δ ⊢ M[σ] N : OT[σ,,N] ® mn ∈ OEl n equiv_n }}) as [? []]; eauto 3.
Qed.

Lemma glu_univ_elem_trm_univ_lvl : forall i P El a,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ M A m,
      {{ Γ ⊢ M : A ® m ∈ El }} ->
      {{ Γ ⊢ A : Type@i }}.
Proof.
  intros. eapply glu_univ_elem_univ_lvl; [| eapply glu_univ_elem_trm_typ]; eassumption.
Qed.

Lemma glu_univ_elem_trm_resp_exp_eq : forall i P El a,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Γ A M m M',
      {{ Γ ⊢ M : A ® m ∈ El }} ->
      {{ Γ ⊢ M ≈ M' : A }} ->
      {{ Γ ⊢ M' : A ® m ∈ El }}.
Proof.
  simpl.
  induction 1 using glu_univ_elem_ind; intros;
    simpl_glu_rel;
    repeat split; mauto 3.

  - repeat eexists; try split; eauto.
    eapply glu_univ_elem_typ_resp_exp_eq; mauto.

  - econstructor; eauto.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    intros.
    destruct_rel_mod_eval.
    assert {{ Δ ⊢ N : IT[σ] }} by eauto using glu_univ_elem_trm_escape.
    assert (exists mn : domain, {{ $| m & n |↘ mn }} /\  {{ Δ ⊢ M[σ] N : OT[σ,,N] ® mn ∈ OEl n equiv_n }}) as [? []] by intuition.
    eexists; split; eauto.
    enough {{ Δ ⊢ M[σ] N ≈ M'[σ] N : OT[σ,,N] }} by eauto.
    assert {{ Γ ⊢ M ≈ M' : Π IT OT }} as Hty by mauto.
    eassert {{ Δ ⊢ IT[σ] : Type@_ }} by mauto 3.
    eapply wf_exp_eq_sub_cong with (Γ := Δ) in Hty; [| eapply sub_eq_refl; mauto 3].
    autorewrite with mctt in Hty.
    eapply wf_exp_eq_app_cong with (N := N) (N' := N) in Hty; try pi_univ_level_tac; [|mauto 2].
    autorewrite with mctt in Hty.
    eassumption.
  - eapply mk_sigma_glu_exp_pred with (equiv_m:=equiv_m); eauto.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    intros.
    eapply H16 in H17 as H'; eauto. destruct_all.
    destruct_rel_mod_eval. simplify_evals.
    assert {{ Δ ⊢s Id∘σ : Γ }} by mauto 4.
    assert {{ Δ ⊢s σ,,(fst M)[σ] : Γ , FT }}. {
      econstructor; mauto 4.
      eapply wf_exp_sub; mauto 3.
    }
    assert {{ Δ ⊢ (fst M)[σ] ≈ (fst M')[σ] : FT[σ] }} by (eapply wf_exp_eq_sub_cong; mauto 3).
    assert {{ Δ ⊢ ST[σ,,(fst M)[σ]] ≈ ST[σ,,(fst M')[σ]] : Type@i }} by (eapply wf_exp_eq_conv'; [eapply wf_exp_eq_sub_cong |]; mauto 4).
    assert {{ Δ ⊢ (snd M)[σ] ≈ (snd M')[σ] : ST[σ,,(fst M)[σ]] }}. {
      eapply wf_exp_eq_conv'; [eapply wf_exp_eq_sub_cong |]; mauto 3.
      symmetry.
      eapply exp_eq_compose_typ_twice; mauto 3. econstructor; mauto 3.
      eapply wf_conv; [eapply wf_fst with (A:=FT) | |]; mauto 3.
      symmetry; etransitivity; [eapply wf_sub_eq_extend_compose|]; mauto 3.
      eapply sub_id_typ; mauto 3.
      eapply wf_sub_eq_extend_cong; mauto 3.
      eapply wf_exp_eq_conv with (A:={{{ FT[σ] }}}); [eapply wf_exp_eq_sub_cong | | ]; mauto 4.
      eapply wf_exp_eq_conv; [eapply wf_exp_eq_sub_cong | | ]; mauto 4.
    }
    split. 
    + eapply IHglu_univ_elem; mauto 3.
    + eapply glu_univ_elem_trm_resp_typ_exp_eq; eauto.
  - econstructor; eauto.
    destruct_glu_eq; econstructor; mauto 3.
    intros.
    enough {{ Δ ⊢ M'0[σ] ≈ M'[σ] : A[σ] }}; mauto 4.
  - intros.
    enough {{ Δ ⊢ M[σ] ≈ M'[σ] : A[σ] }}; mauto 4.
Qed.

Add Parametric Morphism i P El a (H : glu_univ_elem i P El a) Γ T : (El Γ T)
    with signature wf_exp_eq Γ T ==> eq ==> iff as glu_univ_elem_trm_morphism_iff3.
Proof.
  split; intros;
    eapply glu_univ_elem_trm_resp_exp_eq;
    mauto 2.
Qed.

Lemma glu_univ_elem_core_univ' : forall j i typ_rel el_rel,
    j < i ->
    (typ_rel <∙> univ_glu_typ_pred j i) ->
    (el_rel <∙> univ_glu_exp_pred j i) ->
    {{ DG 𝕌@j ∈ glu_univ_elem i ↘ typ_rel ↘ el_rel }}.
Proof.
  intros.
  unshelve basic_glu_univ_elem_econstructor; mautosolve.
Qed.

#[export]
Hint Resolve glu_univ_elem_core_univ' : mctt.

Ltac glu_univ_elem_econstructor :=
  eapply glu_univ_elem_core_univ' + basic_glu_univ_elem_econstructor.

Lemma glu_univ_elem_univ_simple_constructor : forall {i},
    glu_univ_elem (S i) (univ_glu_typ_pred i (S i)) (univ_glu_exp_pred i (S i)) d{{{ 𝕌@i }}}.
Proof.
  intros.
  glu_univ_elem_econstructor; mauto; reflexivity.
Qed.

#[export]
Hint Resolve glu_univ_elem_univ_simple_constructor : mctt.

Ltac clear_predicate_equivalence :=
  repeat match goal with
    | H : ?R1 <∙> ?R2 |- _ =>
        (unify R1 R2; clear H) + (is_var R1; clear R1 H) + (is_var R2; clear R2 H)
    end.

Ltac rewrite_predicate_equivalence_left :=
  repeat match goal with
    | H : ?R1 <∙> ?R2 |- _ =>
        try setoid_rewrite H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite H in H');
        let T := type of H in
        fold (id T) in H;
        clear_predicate_equivalence
    end; unfold id in *.

Ltac rewrite_predicate_equivalence_right :=
  repeat match goal with
    | H : ?R1 <∙> ?R2 |- _ =>
        try setoid_rewrite <- H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite <- H in H');
        let T := type of H in
        fold (id T) in H;
        clear_predicate_equivalence
    end; unfold id in *.

Ltac apply_predicate_equivalence :=
  clear_predicate_equivalence;
  rewrite_predicate_equivalence_right;
  clear_predicate_equivalence;
  rewrite_predicate_equivalence_left;
  clear_predicate_equivalence.

(** *** Simple Morphism instance for [glu_univ_elem] *)
Add Parametric Morphism i : (glu_univ_elem i)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> iff as simple_glu_univ_elem_morphism_iff.
Proof with mautosolve.
  intros P P' ? El El'.
  split; intro Horig; [gen El' P' | gen El P];
    induction Horig using glu_univ_elem_ind; unshelve glu_univ_elem_econstructor;
    try (etransitivity; [symmetry + idtac|]; eassumption); eauto.
Qed.

(** *** Morphism instances for [neut_glu_*_pred]s *)
Add Parametric Morphism i : (neut_glu_typ_pred i)
    with signature per_bot ==> eq ==> eq ==> iff as neut_glu_typ_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition;
    match_by_head per_bot ltac:(fun H => specialize (H (length Δ)) as [? []]);
    functional_read_rewrite_clear; intuition.
Qed.

Add Parametric Morphism i : (neut_glu_typ_pred i)
    with signature per_bot ==> glu_typ_pred_equivalence as neut_glu_typ_pred_morphism_glu_typ_pred_equivalence.
Proof with mautosolve.
  split; apply neut_glu_typ_pred_morphism_iff; mauto.
Qed.

Add Parametric Morphism i : (neut_glu_exp_pred i)
    with signature per_bot ==> eq ==> eq ==> eq ==> eq ==> iff as neut_glu_exp_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition;
    match_by_head per_bot ltac:(fun H => specialize (H (length Δ)) as [? []]);
    functional_read_rewrite_clear; intuition;
    match_by_head per_bot ltac:(fun H => rewrite H in *); eassumption.
Qed.

Add Parametric Morphism i : (neut_glu_exp_pred i)
    with signature per_bot ==> glu_exp_pred_equivalence as neut_glu_exp_pred_morphism_glu_exp_pred_equivalence.
Proof with mautosolve.
  split; apply neut_glu_exp_pred_morphism_iff; mauto.
Qed.

(** *** Morphism instances for [pi_glu_*_pred]s *)
Add Parametric Morphism i IR : (pi_glu_typ_pred i IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> eq ==> eq ==> iff as pi_glu_typ_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism i IR : (pi_glu_typ_pred i IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> glu_typ_pred_equivalence as pi_glu_typ_pred_morphism_glu_typ_pred_equivalence.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism i IR : (pi_glu_exp_pred i IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> relation_equivalence ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff as pi_glu_exp_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism i IR : (pi_glu_exp_pred i IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> relation_equivalence ==> eq ==> glu_exp_pred_equivalence as pi_glu_exp_pred_morphism_glu_exp_pred_equivalence.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

(** *** Morphism instances for [eq_glu_*_pred]s *)
Add Parametric Morphism i m n : (eq_glu_typ_pred i m n)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> eq ==> iff as eq_glu_typ_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism i m n : (eq_glu_typ_pred i m n)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> glu_typ_pred_equivalence as eq_glu_typ_pred_morphism_glu_typ_pred_equivalence.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism i m n IR : (eq_glu_exp_pred i m n IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> eq ==> eq ==> eq ==> iff as eq_glu_exp_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; destruct_glu_eq; repeat (econstructor; intuition).
Qed.

Add Parametric Morphism i m n IR : (eq_glu_exp_pred i m n IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> glu_exp_pred_equivalence as eq_glu_exp_pred_morphism_glu_exp_pred_equivalence.
Proof with mautosolve.
  split; intros []; destruct_glu_eq; repeat (econstructor; intuition).
Qed.

Lemma functional_glu_univ_elem : forall i a P P' El El',
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P' ↘ El' }} ->
    (P <∙> P') /\ (El <∙> El').
Proof.
  simpl.
  intros * Ha Ha'. gen P' El'.
  induction Ha using glu_univ_elem_ind; intros; basic_invert_glu_univ_elem Ha';
    apply_predicate_equivalence; try solve [split; reflexivity].
  - assert ((IP <∙> IP0) /\ (IEl <∙> IEl0)) as [] by mauto.
    apply_predicate_equivalence.
    handle_per_univ_elem_irrel.
    (on_all_hyp: fun H => directed invert_per_univ_elem H).
    handle_per_univ_elem_irrel.
    split; [intros Γ C | intros Γ M C m].
    + split; intros []; econstructor; intuition;
        [ rename equiv_m into equiv0_m; assert (equiv_m : in_rel m m) by intuition
        | assert (equiv0_m : in_rel0 m m) by intuition ];
        destruct_rel_mod_eval;
        functional_eval_rewrite_clear;
        assert ((OP m equiv_m <∙> OP0 m equiv0_m) /\ (OEl m equiv_m <∙> OEl0 m equiv0_m)) as [] by mauto 3;
        intuition.
    + split; intros []; econstructor; intuition;
        [ rename equiv_n into equiv0_n; assert (equiv_n : in_rel n n) by intuition
        | assert (equiv0_n : in_rel0 n n) by intuition];
        destruct_rel_mod_eval;
        [ assert (exists m0n, {{ $| m0 & n |↘ m0n }} /\ {{ Δ ⊢ M0[σ] N : OT[σ,,N] ® m0n ∈ OEl n equiv_n }}) by intuition
        | assert (exists m0n, {{ $| m0 & n |↘ m0n }} /\ {{ Δ ⊢ M0[σ] N : OT[σ,,N] ® m0n ∈ OEl0 n equiv0_n }}) by intuition];
        destruct_conjs;
        assert ((OP n equiv_n <∙> OP0 n equiv0_n) /\ (OEl n equiv_n <∙> OEl0 n equiv0_n)) as [] by mauto 3;
        eexists; split; intuition.
  - assert ((FP <∙> FP0) /\ (FEl <∙> FEl0)) as [] by mauto.
    apply_predicate_equivalence.
    handle_per_univ_elem_irrel.
    (on_all_hyp: fun H => directed invert_per_univ_elem H).
     split; [intros Γ C | intros Γ M C m].
     + split; intros []; econstructor; intuition;
       [ rename equiv_m into equiv0_m; assert (equiv_m : fst_rel m m) by intuition
       | assert (equiv0_m : fst_rel0 m m) by intuition];
       destruct_rel_mod_eval;
       functional_eval_rewrite_clear;
       assert ((SP m equiv_m <∙> SP0 m equiv0_m) /\ (SEl m equiv_m <∙> SEl0 m equiv0_m)) as [] by mauto 3; intuition.
     + split; intros [].
       * assert (equiv0_m : fst_rel0 m1 m1) by intuition.
         eapply mk_sigma_glu_exp_pred with (equiv_m:=equiv0_m); intuition.
         rename equiv_m' into equiv0_m'.
         assert (equiv_m' : fst_rel m' m') by intuition.
         destruct_rel_mod_eval. simplify_evals.
         assert ((SP m' equiv_m' <∙> SP0 m' equiv0_m') /\ (SEl m' equiv_m' <∙> SEl0 m' equiv0_m')) as [] by mauto 3; intuition.
         destruct_rel_mod_eval. simplify_evals.
         assert ((SP m1 equiv_m <∙> SP0 m1 equiv0_m) /\ (SEl m1 equiv_m <∙> SEl0 m1 equiv0_m)) as [] by mauto 3; intuition.
       * rename equiv_m into equiv0_m.
         assert (equiv_m : fst_rel m1 m1) by intuition.
         eapply mk_sigma_glu_exp_pred with (equiv_m:=equiv_m); intuition.
         assert (equiv0_m' : fst_rel0 m' m') by intuition.
         destruct_rel_mod_eval. simplify_evals.
         assert ((SP m' equiv_m' <∙> SP0 m' equiv0_m') /\ (SEl m' equiv_m' <∙> SEl0 m' equiv0_m')) as [] by mauto 3; intuition.
         destruct_rel_mod_eval. simplify_evals.
         assert ((SP m1 equiv_m <∙> SP0 m1 equiv0_m) /\ (SEl m1 equiv_m <∙> SEl0 m1 equiv0_m)) as [] by mauto 3; intuition.
  - assert ((P <∙> P0) /\ (El <∙> El0)) as [] by mauto.
    apply_predicate_equivalence.
    handle_per_univ_elem_irrel.
    split; [intros Γ C | intros Γ M C m'].
    + split; intros []; econstructor; intuition.
    + split; intros []; econstructor; intuition;
        destruct_glu_eq;
        econstructor; intros; apply_equiv_right; mauto 4.
Qed.

Ltac apply_functional_glu_univ_elem1 :=
  let tactic_error o1 o2 := fail 2 "functional_glu_univ_elem biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : {{ DG ^?a ∈ glu_univ_elem ?i ↘ ?P1 ↘ ?El1 }},
      H2 : {{ DG ^?a ∈ glu_univ_elem ?i' ↘ ?P2 ↘ ?El2 }} |- _ =>
      unify i i';
      assert_fails (unify P1 P2; unify El1 El2);
      match goal with
      | H : P1 <∙> P2, H0 : El1 <∙> El2 |- _ => fail 1
      | H : P1 <∙> P2, H0 : El2 <∙> El1 |- _ => fail 1
      | H : P2 <∙> P1, H0 : El1 <∙> El2 |- _ => fail 1
      | H : P2 <∙> P1, H0 : El2 <∙> El1 |- _ => fail 1
      | _ => assert ((P1 <∙> P2) /\ (El1 <∙> El2)) as [] by (eapply functional_glu_univ_elem; [apply H1 | apply H2]) || tactic_error P1 P2
      end
  end.

Ltac apply_functional_glu_univ_elem :=
  repeat apply_functional_glu_univ_elem1.

Ltac handle_functional_glu_univ_elem :=
  functional_eval_rewrite_clear;
  fold glu_typ_pred in *;
  fold glu_exp_pred in *;
  apply_functional_glu_univ_elem;
  apply_predicate_equivalence;
  clear_dups.

Lemma glu_univ_elem_pi_clean_inversion1 : forall {i a ρ B in_rel P El},
  {{ DF a ≈ a ∈ per_univ_elem i ↘ in_rel }} ->
  {{ DG Π a ρ B ∈ glu_univ_elem i ↘ P ↘ El }} ->
  exists IP IEl (OP : forall c (equiv_c_c : {{ Dom c ≈ c ∈ in_rel }}), glu_typ_pred)
     (OEl : forall c (equiv_c_c : {{ Dom c ≈ c ∈ in_rel }}), glu_exp_pred) elem_rel,
      {{ DG a ∈ glu_univ_elem i ↘ IP ↘ IEl }} /\
        (forall c (equiv_c : {{ Dom c ≈ c ∈ in_rel }}) b,
            {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
            {{ DG b ∈ glu_univ_elem i ↘ OP _ equiv_c ↘ OEl _ equiv_c }}) /\
        {{ DF Π a ρ B ≈ Π a ρ B ∈ per_univ_elem i ↘ elem_rel }} /\
        (P <∙> pi_glu_typ_pred i in_rel IP IEl OP) /\
        (El <∙> pi_glu_exp_pred i in_rel IP IEl elem_rel OEl).
Proof.
  intros *.
  simpl.
  intros Hinper Hglu.
  basic_invert_glu_univ_elem Hglu.
  handle_functional_glu_univ_elem.
  handle_per_univ_elem_irrel.
  do 5 eexists.
  repeat split.
  1,3: eassumption.
  1: instantiate (1 := fun c equiv_c Γ A M m => forall (b : domain) Pb Elb,
                          {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
                          {{ DG b ∈ glu_univ_elem i ↘ Pb ↘ Elb }} ->
                          {{ Γ ⊢ M : A ® m ∈ Elb }}).
  1: instantiate (1 := fun c equiv_c Γ A => forall (b : domain) Pb Elb,
                          {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
                          {{ DG b ∈ glu_univ_elem i ↘ Pb ↘ Elb }} ->
                          {{ Γ ⊢ A ® Pb }}).
  2-5: intros []; econstructor; mauto.
  all: intros.
  - assert {{ Dom c ≈ c ∈ in_rel0 }} as equiv0_c by intuition.
    assert {{ DG b ∈ glu_univ_elem i ↘ OP c equiv0_c ↘ OEl c equiv0_c }} by mauto 3.
    apply -> simple_glu_univ_elem_morphism_iff; [| reflexivity | |]; [eauto | |].
    + intros ? ? ? ?.
      split; intros; handle_functional_glu_univ_elem; intuition.
    + intros ? ?.
      split; [intros; handle_functional_glu_univ_elem |]; intuition.
  - assert {{ Dom m ≈ m ∈ in_rel0 }} as equiv0_m by intuition.
    assert {{ DG b ∈ glu_univ_elem i ↘ OP m equiv0_m ↘ OEl m equiv0_m }} by mauto 3.
    handle_functional_glu_univ_elem.
    intuition.
  - match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    destruct_rel_mod_eval.
    intuition.
  - assert {{ Dom n ≈ n ∈ in_rel0 }} as equiv0_n by intuition.
    assert (exists mn : domain, {{ $| m & n |↘ mn }} /\ {{ Δ ⊢ M[σ] N : OT[σ,,N] ® mn ∈ OEl n equiv0_n }}) by mauto 3.
    destruct_conjs.
    eexists.
    intuition.
    assert {{ DG b ∈ glu_univ_elem i ↘ OP n equiv0_n ↘ OEl n equiv0_n }} by mauto 3.
    handle_functional_glu_univ_elem.
    intuition.
  - assert (exists mn : domain,
               {{ $| m & n |↘ mn }} /\
                 (forall (b : domain) (Pb : glu_typ_pred) (Elb : glu_exp_pred),
                     {{ ⟦ B ⟧ ρ ↦ n ↘ b }} ->
                     {{ DG b ∈ glu_univ_elem i ↘ Pb ↘ Elb }} ->
                     {{ Δ ⊢ M[σ] N : OT[σ,,N] ® mn ∈ Elb }})) by intuition.
    destruct_conjs.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    handle_per_univ_elem_irrel.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    functional_eval_rewrite_clear.
    eexists.
    intuition.
Qed.

Lemma glu_univ_elem_pi_clean_inversion2 : forall {i a ρ B in_rel IP IEl P El},
  {{ DF a ≈ a ∈ per_univ_elem i ↘ in_rel }} ->
  {{ DG a ∈ glu_univ_elem i ↘ IP ↘ IEl }} ->
  {{ DG Π a ρ B ∈ glu_univ_elem i ↘ P ↘ El }} ->
  exists (OP : forall c (equiv_c_c : {{ Dom c ≈ c ∈ in_rel }}), glu_typ_pred)
     (OEl : forall c (equiv_c_c : {{ Dom c ≈ c ∈ in_rel }}), glu_exp_pred) elem_rel,
    (forall c (equiv_c : {{ Dom c ≈ c ∈ in_rel }}) b,
        {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
        {{ DG b ∈ glu_univ_elem i ↘ OP _ equiv_c ↘ OEl _ equiv_c }}) /\
      {{ DF Π a ρ B ≈ Π a ρ B ∈ per_univ_elem i ↘ elem_rel }} /\
      (P <∙> pi_glu_typ_pred i in_rel IP IEl OP) /\
      (El <∙> pi_glu_exp_pred i in_rel IP IEl elem_rel OEl).
Proof.
  intros *.
  simpl.
  intros Hinper Hinglu Hglu.
  unshelve eapply (glu_univ_elem_pi_clean_inversion1 _) in Hglu; shelve_unifiable; [eassumption |];
    destruct Hglu as [? [? [? [? [? [? [? [? []]]]]]]]].
  handle_functional_glu_univ_elem.
  do 3 eexists.
  repeat split; try eassumption;
    intros []; econstructor; mauto.
Qed.

Lemma glu_univ_elem_sigma_clean_inversion1 : forall {i a ρ B fst_rel P El},
  {{ DF a ≈ a ∈ per_univ_elem i ↘ fst_rel }} ->
  {{ DG Σ a ρ B ∈ glu_univ_elem i ↘ P ↘ El }} ->
  exists FP FEl (SP : forall c (equiv_c_c : {{ Dom c ≈ c ∈ fst_rel }}), glu_typ_pred)
     (SEl : forall c (equiv_c_c : {{ Dom c ≈ c ∈ fst_rel }}), glu_exp_pred) elem_rel,
      {{ DG a ∈ glu_univ_elem i ↘ FP ↘ FEl }} /\
        (forall c (equiv_c : {{ Dom c ≈ c ∈ fst_rel }}) b,
            {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
            {{ DG b ∈ glu_univ_elem i ↘ SP _ equiv_c ↘ SEl _ equiv_c }}) /\
        {{ DF Σ a ρ B ≈ Σ a ρ B ∈ per_univ_elem i ↘ elem_rel }} /\
        (P <∙> sigma_glu_typ_pred i fst_rel FP FEl SP) /\
        (El <∙> sigma_glu_exp_pred i fst_rel FP FEl elem_rel SP SEl).
Proof.
    intros *.
  simpl.
  intros Hinper Hglu.
  basic_invert_glu_univ_elem Hglu.
  handle_functional_glu_univ_elem.
  handle_per_univ_elem_irrel.
  do 5 eexists.
  repeat split; eauto.
  (* How these are come up with? *)
  1: instantiate (1 := fun c equiv_c Γ A M m => forall (b : domain) Pb Elb,
                          {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
                          {{ DG b ∈ glu_univ_elem i ↘ Pb ↘ Elb }} ->
                          {{ Γ ⊢ M : A ® m ∈ Elb }}).
  1: instantiate (1 := fun c equiv_c Γ A => forall (b : domain) Pb Elb,
                          {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
                          {{ DG b ∈ glu_univ_elem i ↘ Pb ↘ Elb }} ->
                          {{ Γ ⊢ A ® Pb }}).
  - intros. assert {{ Dom c ≈ c ∈ fst_rel0 }} as equiv0_c by intuition.
    assert {{ DG b ∈ glu_univ_elem i ↘ SP c equiv0_c ↘ SEl c equiv0_c }} by mauto 3.
    apply -> simple_glu_univ_elem_morphism_iff; [| reflexivity | |]; [eauto | |].
    + intros ? ? ? ?.
      split; intros; handle_functional_glu_univ_elem; intuition.
    + intros ? ?.
      split; [intros; handle_functional_glu_univ_elem |]; intuition.
  - intros []; econstructor; mauto; intuition.
    assert {{ Dom m ≈ m ∈ fst_rel0 }} as equiv0_m by intuition.
    assert {{ DG b ∈ glu_univ_elem i ↘ SP m equiv0_m ↘ SEl m equiv0_m }} by mauto 3.
    handle_functional_glu_univ_elem.
    intuition.
  - intros.
    dependent destruction H4.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    apply_relation_equivalence.
    econstructor; mauto 3. intros.
    destruct_rel_mod_eval. simplify_evals.
    intuition.
  - intros []. 
    econstructor; mauto 3; intuition.
    + assert {{ Dom m' ≈ m' ∈ fst_rel0 }} as equiv0_m' by intuition;
      assert {{ DG b ∈ glu_univ_elem i ↘ SP m' equiv0_m' ↘ SEl m' equiv0_m' }} by mauto 3.
      handle_functional_glu_univ_elem.
      intuition.
    + assert {{ DG b ∈ glu_univ_elem i ↘ SP m1 equiv_m ↘ SEl m1 equiv_m }} by mauto 3.
      handle_functional_glu_univ_elem.
      intuition.
  - intros []. 
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    assert (equiv0_m : {{ Dom m1 ≈ m1 ∈ fst_rel0 }}) by intuition.
    eapply mk_sigma_glu_exp_pred with (equiv_m:=equiv0_m); intuition;
    destruct_rel_mod_eval; simplify_evals; intuition.
Qed.

Lemma glu_univ_elem_sigma_clean_inversion2 : forall {i a ρ B fst_rel FP FEl P El},
  {{ DF a ≈ a ∈ per_univ_elem i ↘ fst_rel }} ->
  {{ DG a ∈ glu_univ_elem i ↘ FP ↘ FEl }} ->
  {{ DG Σ a ρ B ∈ glu_univ_elem i ↘ P ↘ El }} ->
  exists (SP : forall c (equiv_c_c : {{ Dom c ≈ c ∈ fst_rel }}), glu_typ_pred)
     (SEl : forall c (equiv_c_c : {{ Dom c ≈ c ∈ fst_rel }}), glu_exp_pred) elem_rel,
        (forall c (equiv_c : {{ Dom c ≈ c ∈ fst_rel }}) b,
            {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
            {{ DG b ∈ glu_univ_elem i ↘ SP _ equiv_c ↘ SEl _ equiv_c }}) /\
        {{ DF Σ a ρ B ≈ Σ a ρ B ∈ per_univ_elem i ↘ elem_rel }} /\
        (P <∙> sigma_glu_typ_pred i fst_rel FP FEl SP) /\
        (El <∙> sigma_glu_exp_pred i fst_rel FP FEl elem_rel SP SEl).
Proof.
    intros *.
  simpl.
  intros Hinper Hinglu Hglu.
  unshelve eapply (glu_univ_elem_sigma_clean_inversion1 _) in Hglu; shelve_unifiable; [eassumption |];
    destruct Hglu as [? [? [? [? [? [? [? [? []]]]]]]]];
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
  handle_functional_glu_univ_elem.
  do 3 eexists.
  repeat split; try eassumption; handle_functional_glu_univ_elem;
    auto.
  - per_univ_elem_econstructor; eauto. 
  - intros []. econstructor; mauto; 
    intros; handle_functional_glu_univ_elem; auto.
  - intros []. econstructor; mauto; 
    intros; handle_functional_glu_univ_elem; auto.
  - intros []. econstructor; mauto; 
    intros; handle_functional_glu_univ_elem; auto.
  - intros []. econstructor; mauto; 
    intros; handle_functional_glu_univ_elem; auto.
Qed.

Ltac invert_glu_univ_elem H :=
  (unshelve eapply (glu_univ_elem_pi_clean_inversion2 _ _) in H; shelve_unifiable; [eassumption | eassumption |];
   deex_in H; destruct H as [? [? []]])
  + (unshelve eapply (glu_univ_elem_pi_clean_inversion1 _) in H; shelve_unifiable; [eassumption |];
   deex_in H; destruct H as [? [? [? []]]])
  + (unshelve eapply (glu_univ_elem_sigma_clean_inversion2 _ _) in H; shelve_unifiable; [eassumption | eassumption |];
   deex_in H; destruct H as [? [? []]])
  + (unshelve eapply (glu_univ_elem_sigma_clean_inversion1 _) in H; shelve_unifiable; [eassumption |];
   deex_in H; destruct H as [? [? [? []]]])
  + basic_invert_glu_univ_elem H.

(* TODO: unify with the uip version above *)
Ltac invert_glu_univ_elem_nouip H :=
  (unshelve eapply (glu_univ_elem_pi_clean_inversion2 _ _) in H; shelve_unifiable; [eassumption | eassumption |];
   destruct H as [? [? [? [? [? []]]]]])
  + (unshelve eapply (glu_univ_elem_pi_clean_inversion1 _) in H; shelve_unifiable; [eassumption |];
   destruct H as [? [? [? [? [? [? [? [? []]]]]]]]])
  + (unshelve eapply (glu_univ_elem_sigma_clean_inversion2 _ _) in H; shelve_unifiable; [eassumption | eassumption |];
   destruct H as [? [? [? [? [? []]]]]])
  + (unshelve eapply (glu_univ_elem_sigma_clean_inversion1 _) in H; shelve_unifiable; [eassumption |];
   destruct H as [? [? [? [? [? [? [? [? []]]]]]]]])
  + basic_invert_glu_univ_elem_nouip H.

Lemma glu_nat_resp_per_nat : forall m n,
    {{ Dom m ≈ n ∈ per_nat }} ->
    forall Γ M,
      glu_nat Γ M m ->
      glu_nat Γ M n.
Proof.
  induction 1; intros; progressive_inversion; mauto.
  econstructor.
  - pose proof (PER_refl2 _ per_bot).
    mauto.
  - intros.
    specialize (H (length Δ)).
    destruct_all.
    functional_read_rewrite_clear.
    mauto.
Qed.

#[local]
Hint Resolve glu_nat_resp_per_nat : mctt.

#[local]
Ltac resp_per_IH :=
  match_by_head1 glu_univ_elem
    ltac:(fun H =>
            match goal with
            | H' : _ |- _ => eapply H' in H
            end);
  eauto; intuition.

Lemma glu_univ_elem_resp_per_univ_elem : forall i a a' R,
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
    forall P El,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a' ∈ glu_univ_elem i ↘ P ↘ El }} /\
      (forall Γ M A m m',
          {{ Γ ⊢ M : A ® m ∈ El }} ->
          {{ Dom m ≈ m' ∈ R }} ->
          {{ Γ ⊢ M : A ® m' ∈ El }}).
Proof.
  simpl.
  intros * Hper * Horig.
  pose proof Hper.
  gen P El.

  induction Hper using per_univ_elem_ind; intros; subst;
    saturate_refl_for per_univ_elem;
    invert_glu_univ_elem Horig.

  (* TODO : handle Sigma case uniformly  *)
  1,2,3,5,6:
    split;
    try glu_univ_elem_econstructor;
    try eassumption; mauto 3;
    intros;
    handle_per_univ_elem_irrel;
    handle_functional_glu_univ_elem;
    simpl in *;
    destruct_all;
    mauto 3.

  - repeat split; eauto.
    resp_per_IH.
    mauto.
  - resp_per_IH.
  - invert_per_univ_elem H.
    destruct_rel_mod_eval.
    handle_per_univ_elem_irrel.
    eassert {{ DG ^_ ∈ glu_univ_elem i ↘ OP c equiv_c ↘ OEl c equiv_c }} by eauto 2.
    resp_per_IH.
  - simpl_glu_rel.
    invert_per_univ_elem H10.

    econstructor; mauto 3.
    + eapply H17.
      pose proof (proj1 (H17 _ _) H16).
      simpl in *.

      intros.
      saturate_refl_for in_rel.
      pose proof (H18 _ _ equiv_c_c') as [].
      pose proof (H18 _ _ H19) as [].
      pose proof (H10 _ _ equiv_c_c') as [].
      pose proof (H10 _ _ H19) as [].
      simplify_evals.
      econstructor; eauto.
      symmetry.
      etransitivity.
      * symmetry. eassumption.
      * handle_per_univ_elem_irrel.
        eapply H24.
        eassumption.
    + resp_per_IH.
      destruct_rel_mod_eval.
      handle_per_univ_elem_irrel.
      pose proof (H9 _ equiv_n _ H22).
      eapply H28 in H25 as []; eauto.
      destruct (H15 _ _ _ _ H20 H21 equiv_n) as [? []].
      destruct (H16 _ _ equiv_n) as [].
      simplify_evals.
      eauto.
  - resp_per_IH.
  - pose proof (PER_refl2 _ R). mauto.
  - pose proof (PER_refl2 _ R). mauto.
  - split; intros []; econstructor; intuition.
  - split; intros []; econstructor; intuition;
      destruct_glu_eq;
      econstructor; mauto 3;
      apply_equiv_left.
    + etransitivity; eauto.
      symmetry. trivial.
    + etransitivity; eauto.
    + etransitivity; [| eauto]; eauto.
    + etransitivity; eauto.
      symmetry. trivial.
  - simpl_glu_rel.
    econstructor; eauto.
    destruct_glu_eq; match_by_head1 per_eq progressive_invert; econstructor; mauto 3; intros.
    + etransitivity; mauto.
    + etransitivity; eauto.
      symmetry. eauto.
    + resp_per_IH.
    + match_by_head1 per_bot ltac:(fun H => specialize (H (length Δ))).
      destruct_all.
      functional_read_rewrite_clear.
      mauto.
  - apply neut_glu_typ_pred_morphism_glu_typ_pred_equivalence.
    eassumption.
  - apply neut_glu_exp_pred_morphism_glu_exp_pred_equivalence.
    eassumption.
  - simpl_glu_rel.
    progressive_invert H9.
    econstructor; unfold neut_glu_typ_pred; mauto 3.

    intros.
    specialize (H9 (length Δ)).
    destruct_all.
    functional_read_rewrite_clear.
    mauto.
  (* Sigma case *)
  - match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    mauto. split. 

    + glu_univ_elem_econstructor; mauto 3.
      specialize (IHHper H0 FEl FP) as IH'. 
      destruct_all. intuition.
      intros.
      * destruct_rel_mod_eval.
        destruct_all. simplify_evals.
        specialize (H33 H32 (SEl c equiv_c) (SP c equiv_c)) as IH'.
        intuition. 
      * per_univ_elem_econstructor; mauto 3.
        rewrite H13. split; intros.
        -- destruct_by_head rel_mod_proj. simplify_evals.
           destruct_rel_mod_eval.
           destruct_all. simplify_evals.
           econstructor; mauto 3.
           handle_per_univ_elem_irrel. intuition.
        -- destruct_by_head rel_mod_proj. simplify_evals.
           destruct_rel_mod_eval.
           destruct_all. simplify_evals.
           econstructor; mauto 3.
           handle_per_univ_elem_irrel. intuition.
    + intros;
      handle_per_univ_elem_irrel.
      handle_functional_glu_univ_elem;
      simpl in *;
      destruct_all;
      mauto 3.
      destruct_by_head sigma_glu_exp_pred.
      destruct_by_head rel_mod_proj.
      simplify_evals.

      rewrite H13 in H12. 
      destruct_by_head rel_mod_proj. simplify_evals.
      assert (fst_rel b' b'). {
        etransitivity; [symmetry | ]; eassumption.
      }
      destruct_rel_mod_eval. simplify_evals.
      (* TODO : too slow *)
      handle_per_univ_elem_irrel.

      eapply mk_sigma_glu_exp_pred with (equiv_m:=H16); mauto 3.
      rewrite H13.
      eapply mk_rel_mod_proj with (equiv_b_b':=H16); mauto 3.
      assert (PER (x b b equiv_m)). {
          eapply per_elem_PER; eauto.
      }
      assert (PER (x2 b b' equiv_b_b')). {
        eapply equiv_rel_PER; eauto. split; intros; 
        eapply H150; auto.
      }
      apply H139. apply H150. etransitivity; [symmetry | ]; eassumption.
      intros.
      handle_functional_glu_univ_elem. eauto.
      specialize (H9 _ H16 _ H17) as IH.
      specialize (H9 _ equiv_m _ H27) as IH2.
      specialize (H24 _ _ H26) as IH1. destruct_conjs.
      assert (glu_univ_elem i (SP b equiv_m) (SEl b equiv_m) a'0). {
        specialize (H79 H78 _ _ IH2). destruct_all. auto.
      }
      assert (glu_univ_elem i (SP b' H16) (SEl b' H16) a'0). {
        specialize (H75 H74 _ _ IH). destruct_all. auto.
      }
      handle_functional_glu_univ_elem.
      split.
      eapply IHHper; mauto 3.
      apply H34.
      eapply H83; mauto 3.
      apply H151. apply H150. auto.
Qed.

Lemma glu_univ_elem_resp_per_univ : forall i a a' P El,
    {{ Dom a ≈ a' ∈ per_univ i }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a' ∈ glu_univ_elem i ↘ P ↘ El }}.
Proof.
  intros * [? H] ?.
  eapply glu_univ_elem_resp_per_univ_elem in H; eauto.
  intuition.
Qed.

Lemma glu_univ_elem_resp_per_elem : forall i a a' R P El Γ M A m m',
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ Γ ⊢ M : A ® m ∈ El }} ->
    {{ Dom m ≈ m' ∈ R }} ->
    {{ Γ ⊢ M : A ® m' ∈ El }}.
Proof.
  intros * H ?.
  eapply glu_univ_elem_resp_per_univ_elem in H; eauto.
  intuition.
Qed.


(** *** Morphism instances for [glu_univ_elem] *)
Add Parametric Morphism i : (glu_univ_elem i)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> per_univ i ==> iff as glu_univ_elem_morphism_iff.
Proof with mautosolve.
  intros P P' HPP' El El' HElEl' a a' Haa'.
  rewrite HPP', HElEl'.
  split; intros; eapply glu_univ_elem_resp_per_univ; mauto.
  symmetry; eassumption.
Qed.

Add Parametric Morphism i R : (glu_univ_elem i)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> per_univ_elem i R ==> iff as glu_univ_elem_morphism_iff'.
Proof with mautosolve.
  intros P P' HPP' El El' HElEl' **.
  rewrite HPP', HElEl'.
  split; intros; eapply glu_univ_elem_resp_per_univ; mauto.
  symmetry; mauto.
Qed.

Ltac saturate_glu_by_per1 :=
  match goal with
  | H : glu_univ_elem ?i ?P ?El ?a,
      H1 : per_univ_elem ?i _ ?a ?a' |- _ =>
      assert (glu_univ_elem i P El a') by (rewrite <- H1; eassumption);
      fail_if_dup
  | H : glu_univ_elem ?i ?P ?El ?a',
      H1 : per_univ_elem ?i _ ?a ?a' |- _ =>
      assert (glu_univ_elem i P El a) by (rewrite H1; eassumption);
      fail_if_dup
  end.

Ltac saturate_glu_by_per :=
  clear_dups;
  repeat saturate_glu_by_per1.

Lemma per_univ_glu_univ_elem : forall i a,
    {{ Dom a ≈ a ∈ per_univ i }} ->
    exists P El, {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }}.
Proof.
  simpl.
  intros * [? Hper].
  induction Hper using per_univ_elem_ind; intros;
    try solve [do 2 eexists; unshelve (glu_univ_elem_econstructor; try reflexivity; subst; trivial)].

  - destruct_conjs.
    do 2 eexists.
    glu_univ_elem_econstructor; try (eassumption + reflexivity).
    + saturate_refl; eassumption.
    + instantiate (1 := fun (c : domain) (equiv_c : in_rel c c) Γ A M m =>
                          forall b P El,
                            {{ ⟦ B' ⟧ ρ' ↦ c ↘ b }} ->
                            glu_univ_elem i P El b ->
                            {{ Γ ⊢ M : A ® m ∈ El }}).
      instantiate (1 := fun (c : domain) (equiv_c : in_rel c c) Γ A =>
                          forall b P El,
                            {{ ⟦ B' ⟧ ρ' ↦ c ↘ b }} ->
                            glu_univ_elem i P El b ->
                            {{ Γ ⊢ A ® P }}).
      intros.
      (on_all_hyp: destruct_rel_by_assumption in_rel).
      handle_per_univ_elem_irrel.
      rewrite simple_glu_univ_elem_morphism_iff; try (eassumption + reflexivity);
        split; intros; handle_functional_glu_univ_elem; intuition.
    + enough {{ DF Π a ρ B ≈ Π a' ρ' B' ∈ per_univ_elem i ↘ elem_rel }} by (etransitivity; [symmetry |]; eassumption).
      per_univ_elem_econstructor; mauto.
      intros.
      (on_all_hyp: destruct_rel_by_assumption in_rel).
      econstructor; mauto.
  - destruct_conjs.
    do 2 eexists.
    glu_univ_elem_econstructor; try (eassumption + reflexivity).
    + saturate_refl; eassumption.
    + instantiate (1 := fun (c : domain) (equiv_c : fst_rel c c) Γ A M m =>
                          forall b P El,
                            {{ ⟦ B' ⟧ ρ' ↦ c ↘ b }} ->
                            glu_univ_elem i P El b ->
                            {{ Γ ⊢ M : A ® m ∈ El }}).
      instantiate (1 := fun (c : domain) (equiv_c : fst_rel c c) Γ A =>
                      forall b P El,
                        {{ ⟦ B' ⟧ ρ' ↦ c ↘ b }} ->
                        glu_univ_elem i P El b ->
                        {{ Γ ⊢ A ® P }}).
      intros.
      (on_all_hyp: destruct_rel_by_assumption fst_rel).
      handle_per_univ_elem_irrel.
      rewrite simple_glu_univ_elem_morphism_iff; try (eassumption + reflexivity);
        split; intros; handle_functional_glu_univ_elem; intuition.
    + enough {{ DF Σ a ρ B ≈ Σ a' ρ' B' ∈ per_univ_elem i ↘ elem_rel }} by (etransitivity; [symmetry |]; eassumption).
      per_univ_elem_econstructor; mauto.
      intros.
      (on_all_hyp: destruct_rel_by_assumption fst_rel).
      econstructor; mauto.
  - destruct_conjs.
    saturate_refl.
    do 2 eexists.
    glu_univ_elem_econstructor; eauto; reflexivity.
  - do 2 eexists.
    glu_univ_elem_econstructor; try reflexivity; mauto.
Qed.

#[export]
Hint Resolve per_univ_glu_univ_elem : mctt.

Corollary per_univ_elem_glu_univ_elem : forall i a R,
    {{ DF a ≈ a ∈ per_univ_elem i ↘ R }} ->
    exists P El, {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }}.
Proof.
  intros.
  apply per_univ_glu_univ_elem; mauto.
Qed.

#[export]
Hint Resolve per_univ_elem_glu_univ_elem : mctt.

Ltac saturate_glu_info1 :=
  match goal with
  | H : glu_univ_elem _ ?P _ _,
      H1 : ?P _ _ |- _ =>
      pose proof (glu_univ_elem_univ_lvl _ _ _ _ H _ _ H1);
      fail_if_dup
  | H : glu_univ_elem _ _ ?El _,
      H1 : ?El _ _ _ _ |- _ =>
      pose proof (glu_univ_elem_trm_escape _ _ _ _ H _ _ _ _ H1);
      fail_if_dup
  end.

Ltac saturate_glu_info :=
  clear_dups;
  repeat saturate_glu_info1.

#[local]
Hint Rewrite -> sub_decompose_q using solve [mauto 4] : mctt.

Lemma glu_univ_elem_mut_monotone : forall i a P El,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Δ σ Γ,
      {{ Δ ⊢w σ : Γ }} ->
      (forall A,
        {{ Γ ⊢ A ® P }} ->
        {{ Δ ⊢ A[σ] ® P }}) /\
    (forall M A m,
      {{ Γ ⊢ M : A ® m ∈ El }} ->
      {{ Δ ⊢ M[σ] : A[σ] ® m ∈ El }}).
Proof.
  simpl. induction 1 using glu_univ_elem_ind;
    split; intros;
    saturate_weakening_escape;
    handle_functional_glu_univ_elem;
    simpl in *;
    destruct_all;
    try solve [bulky_rewrite].
  - repeat eexists; mauto 2; bulky_rewrite.
    resp_per_IH.
  - repeat eexists; mauto 2; bulky_rewrite.

  - simpl_glu_rel.
    econstructor; eauto; try solve [bulky_rewrite]; mauto 3.
    + intros.
      eapply IHglu_univ_elem; eauto.
    + intros.
      saturate_weakening_escape.
      saturate_glu_info.
      invert_per_univ_elem H3.
      destruct_rel_mod_eval.
      simplify_evals.
      deepexec H1 ltac:(fun H => pose proof H).
      autorewrite with mctt in *.
      mauto 3.

  - simpl_glu_rel;
    econstructor; mauto 4;
      intros;
      saturate_weakening_escape.
    + eapply IHglu_univ_elem; eauto.
    + saturate_glu_info.
      invert_per_univ_elem H3.
      apply_equiv_left.
      destruct_rel_mod_eval.
      destruct_rel_mod_app.
      simplify_evals.
      deepexec H1 ltac:(fun H => pose proof H).
      autorewrite with mctt in *.
      repeat eexists; eauto.
      assert {{ Δ0 ⊢s σ0,,N : Δ, IT[σ] }}.
      {
        econstructor; mauto 2.
        bulky_rewrite.
      }
      assert {{Δ0 ⊢ M[σ][σ0] N ≈ M[σ∘σ0] N : OT [σ∘σ0,,N]}}.
      {
        rewrite <- @sub_eq_q_sigma_id_extend; mauto 4.
        rewrite <- @exp_eq_sub_compose_typ; mauto 3;
          [eapply wf_exp_eq_app_cong' |];
          mauto 4.
        symmetry.
        bulky_rewrite_in H4.
        assert {{ Δ0 ⊢ Π IT[σ∘σ0] (OT[q (σ∘σ0)]) ≈ (Π IT OT)[σ∘σ0] : Type@_ }} by mauto.
        eapply wf_exp_eq_conv'; mauto 4.
      }

      bulky_rewrite.
      edestruct H11 with (n := n) as [? []];
        simplify_evals; [| | eassumption];
        mauto.
  - simpl_glu_rel.
    econstructor; mauto 4;
      intros;
      saturate_weakening_escape.
    + intros.
      eapply IHglu_univ_elem; eauto.
    + invert_per_univ_elem H3.
      destruct_rel_mod_eval. simplify_evals.
      assert {{ Δ0 ⊢w σ∘σ0 : Γ }} by mauto.
      eapply glu_univ_elem_typ_resp_exp_eq with (A:={{{ST[σ∘σ0,,M]}}}); mauto 3.
      eapply H9; mauto 3.
      eapply glu_univ_elem_trm_resp_typ_exp_eq; mauto 3.
      eapply sub_decompose_q_typ; mauto 3.
      eapply glu_univ_elem_trm_escape; mauto 3.
  - simpl_glu_rel.
    invert_per_univ_elem H3.
    eapply mk_sigma_glu_exp_pred with (equiv_m:=equiv_m); mauto 4.
    + intros; eapply glu_univ_elem_typ_resp_exp_eq; mauto 4.
    + intros.
      destruct_rel_mod_eval. simplify_evals. 
      assert {{ Δ0 ⊢w σ∘σ0 : Γ }} by mauto.
      eapply glu_univ_elem_typ_resp_exp_eq with (A:={{{ST[σ∘σ0,,M']}}}); mauto 3.
      eapply H13; mauto 3.
      eapply glu_univ_elem_trm_resp_typ_exp_eq; mauto 3.
      eapply sub_decompose_q_typ; mauto 3.
      eapply glu_univ_elem_trm_escape; mauto 3.
    + intros. saturate_weakening_escape.
      assert {{ Δ0 ⊢w σ∘σ0 : Γ }} by mauto.
      bulky_rewrite.
      destruct_rel_mod_eval. simplify_evals.
      assert {{ Δ ⊢ fst M[σ] : FT[σ] }}. 
      {
        eapply wf_fst with (B:={{{ST[q σ]}}}) (i:=i); mauto 3.
      }
      assert {{ Δ0 ⊢s σ0,,(fst M[σ])[σ0] : Δ, FT[σ] }}.
      {
        econstructor; mauto 2.
      }
      assert {{ Δ0 ⊢ (fst M)[σ∘σ0] : FT[σ][σ0] }}. {
          eapply wf_conv; [eapply wf_exp_sub | |]; mauto 3.
      }
      assert {{ Δ0 ⊢s σ∘σ0,,(fst M)[σ∘σ0] : Γ , FT }}. {
        econstructor; mauto 2.
        eapply wf_conv;  mauto 3.  
      }
      assert {{ Δ0 ⊢ ST[σ∘σ0,,(fst M)[σ∘σ0]] ≈ ST[q σ][σ0,,(fst M[σ])[σ0]] : Type@i }}. {
        etransitivity; [eapply sub_decompose_q_typ |]; mauto 3.
        eapply wf_eq_typ_exp_sub_cong_twice; mauto 3.
        eapply wf_sub_eq_compose_cong; mauto 3.
        eapply wf_sub_eq_extend_cong; mauto 3.
        etransitivity; [eapply wf_exp_eq_conv; [eapply wf_exp_eq_sub_compose| | ]|]; mauto 3.
        eapply wf_exp_eq_sub_cong; mauto 3.
      }
      assert {{ Δ0 ⊢ ST[Id,,fst M][σ∘σ0] ≈ ST[σ∘σ0,,(fst M)[σ∘σ0]] : Type@i }}. {
        eapply exp_eq_elim_sub_lhs_typ_gen; mauto 3.
      }
      assert {{ Δ0 ⊢ ST[σ∘σ0,,(fst M)[σ∘σ0]] : Type@i }}. {
        gen_presups; mauto 3.
      }
      split.
      eapply glu_univ_elem_trm_resp_exp_eq; mauto 3. intuition.
      etransitivity.
      eapply wf_exp_eq_conv; [eapply wf_exp_eq_sub_compose | |]; mauto 3.
      eapply exp_eq_refl; econstructor; mauto 3.
      eapply wf_exp_eq_conv; [eapply wf_exp_eq_sub_cong | |]; mauto 3.
      eapply glu_univ_elem_trm_resp_typ_exp_eq; mauto 3.
      eapply glu_univ_elem_trm_resp_exp_eq; mauto 3; intuition.
      etransitivity.
      eapply wf_exp_eq_conv; [eapply wf_exp_eq_sub_compose | |]; mauto 3.
      eapply wf_exp_eq_conv; [eapply wf_exp_eq_sub_cong | |]; mauto 3.
      symmetry; etransitivity; [|eapply exp_eq_compose_typ]; mauto 3.
      eapply wf_exp_eq_conv; [eapply wf_exp_eq_sub_cong | |]; mauto 4.
      etransitivity; [|symmetry; eapply wf_sub_eq_extend_compose]; mauto 3.
      eapply wf_sub_eq_extend_cong; mauto 3.
      etransitivity; [eapply wf_exp_eq_sub_compose|]; mauto 3.
      eapply wf_exp_eq_conv; [eapply wf_exp_eq_sub_cong | |]; mauto 3.
  - simpl_glu_rel.
    econstructor; intros; only 1: bulky_rewrite; mauto 3;
      solve [eapply IHglu_univ_elem; eauto].
  - simpl_glu_rel.
    econstructor; intros; only 2: bulky_rewrite; mauto 3;
      try solve [eapply IHglu_univ_elem; eauto].
    destruct_glu_eq; econstructor; eauto; intros.
    + transitivity {{{(refl B M'')[σ]}}}; [mauto 3 |].
      eapply wf_exp_eq_conv';
        [eapply wf_exp_eq_refl_sub'; gen_presups; eauto |].
      symmetry.
      transitivity {{{(Eq B M N)[σ]}}}; mauto 2.
      eapply exp_eq_sub_cong_typ1; eauto.
      econstructor; mauto.
    + mauto 3.
    + mauto 3.
    + eapply IHglu_univ_elem; eauto.
    + assert {{ Δ0 ⊢w σ ∘ σ0 : Γ }} by mauto 4.
      bulky_rewrite.
      etransitivity;
        [| deepexec H13 ltac:(fun H => apply H)].
      mauto 4.
  - destruct_conjs.
    split; [mauto 3 |].
    intros.
    saturate_weakening_escape.
    autorewrite with mctt.
    mauto 3.
  - simpl_glu_rel.
    econstructor; repeat split; mauto 3;
      intros;
      saturate_weakening_escape;
      autorewrite with mctt;
      [mauto 3 |].
    etransitivity.
    + symmetry.
      eapply wf_exp_eq_sub_compose;
        mauto 3.
    + mauto 3.
Qed.

Lemma glu_univ_elem_typ_monotone : forall i a P El Δ σ Γ A,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Δ ⊢w σ : Γ }} ->
    {{ Δ ⊢ A[σ] ® P }}.
Proof.
  intros; gen A.
  eapply proj1; eauto using glu_univ_elem_mut_monotone.
Qed.

Lemma glu_univ_elem_exp_monotone : forall i a P El Δ σ Γ M A m,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ Γ ⊢ M : A ® m ∈ El }} ->
    {{ Δ ⊢w σ : Γ }} ->
    {{ Δ ⊢ M[σ] : A[σ] ® m ∈ El }}.
Proof.
  intros; gen m A M.
  eapply proj2; eauto using glu_univ_elem_mut_monotone.
Qed.

Add Parametric Morphism i a : (glu_elem_bot i a)
    with signature wf_ctx_eq ==> eq ==> eq ==> eq ==> iff as glu_elem_bot_morphism_iff1.
Proof.
  intros Γ Γ' HΓΓ' *.
  split; intros []; econstructor; mauto 4; [rewrite <- HΓΓ' | rewrite -> HΓΓ']; eassumption.
Qed.

Add Parametric Morphism i a Γ : (glu_elem_bot i a Γ)
    with signature wf_exp_eq Γ {{{ Type@i }}} ==> eq ==> eq ==> iff as glu_elem_bot_morphism_iff2.
Proof.
  intros A A' HAA' *.
  split; intros []; econstructor; mauto 3; [rewrite <- HAA' | | rewrite -> HAA' |];
    try eassumption;
    intros;
    assert {{ Δ ⊢ A[σ] ≈ A'[σ] : Type@i }} as HAσA'σ by mauto 4;
    [rewrite <- HAσA'σ | rewrite -> HAσA'σ];
    mauto.
Qed.

Add Parametric Morphism i a Γ A : (glu_elem_bot i a Γ A)
    with signature wf_exp_eq Γ A ==> eq ==> iff as glu_elem_bot_morphism_iff3.
Proof.
  intros M M' HMM' *.
  split; intros []; econstructor; mauto 3; try (gen_presup HMM'; eassumption);
    intros;
    assert {{ Δ ⊢ M[σ] ≈ M'[σ] : A[σ] }} as HMσM'σ by mauto 4;
    [rewrite <- HMσM'σ | rewrite -> HMσM'σ];
    mauto.
Qed.

Add Parametric Morphism i a : (glu_elem_top i a)
    with signature wf_ctx_eq ==> eq ==> eq ==> eq ==> iff as glu_elem_top_morphism_iff1.
Proof.
  intros Γ Γ' HΓΓ' *.
  split; intros []; econstructor; mauto 4; [rewrite <- HΓΓ' | rewrite -> HΓΓ']; eassumption.
Qed.

Add Parametric Morphism i a Γ : (glu_elem_top i a Γ)
    with signature wf_exp_eq Γ {{{ Type@i }}} ==> eq ==> eq ==> iff as glu_elem_top_morphism_iff2.
Proof.
  intros A A' HAA' *.
  split; intros []; econstructor; mauto 3; [rewrite <- HAA' | | rewrite -> HAA' |];
    try eassumption;
    intros;
    assert {{ Δ ⊢ A[σ] ≈ A'[σ] : Type@i }} as HAσA'σ by mauto 4;
    [rewrite <- HAσA'σ | rewrite -> HAσA'σ];
    mauto.
Qed.

Add Parametric Morphism i a Γ A : (glu_elem_top i a Γ A)
    with signature wf_exp_eq Γ A ==> eq ==> iff as glu_elem_top_morphism_iff3.
Proof.
  intros M M' HMM' *.
  split; intros []; econstructor; mauto 3; try (gen_presup HMM'; eassumption);
    intros;
    assert {{ Δ ⊢ M[σ] ≈ M'[σ] : A[σ] }} as HMσM'σ by mauto 4;
    [rewrite <- HMσM'σ | rewrite -> HMσM'σ];
    mauto.
Qed.

Add Parametric Morphism i a : (glu_typ_top i a)
    with signature wf_ctx_eq ==> eq ==> iff as glu_typ_top_morphism_iff1.
Proof.
  intros Γ Γ' HΓΓ' *.
  split; intros []; econstructor; mauto 4.
Qed.

Add Parametric Morphism i a Γ : (glu_typ_top i a Γ)
    with signature wf_exp_eq Γ {{{ Type@i }}} ==> iff as glu_typ_top_morphism_iff2.
Proof.
  intros A A' HAA' *.
  split; intros []; econstructor; mauto 3;
    try (gen_presup HAA'; eassumption);
    intros;
    assert {{ Δ ⊢ A[σ] ≈ A'[σ] : Type@i }} as HAσA'σ by mauto 4;
    [rewrite <- HAσA'σ | rewrite -> HAσA'σ];
    mauto.
Qed.

(** *** Simple Morphism instance for [glu_ctx_env] *)
Add Parametric Morphism : glu_ctx_env
    with signature glu_sub_pred_equivalence ==> eq ==> iff as simple_glu_ctx_env_morphism_iff.
Proof.
  intros Sb Sb' HSbSb' a.
  split; intro Horig; [gen Sb' | gen Sb];
    induction Horig; econstructor;
    try (etransitivity; [symmetry + idtac|]; eassumption); eauto.
Qed.
