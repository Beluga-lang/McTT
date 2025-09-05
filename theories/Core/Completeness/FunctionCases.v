From Coq Require Import Morphisms_Relations Relation_Definitions.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import LogicalRelation TermStructureCases UniverseCases.
Import Domain_Notations.

Lemma rel_exp_of_pi_inversion : forall {Γ M M' A B},
    {{ Γ ⊨ M ≈ M' : Π A B }} ->
    exists env_rel,
      {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }} /\
        exists i,
        forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
        exists in_rel out_rel,
          rel_typ i A ρ A ρ' in_rel /\
            (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_typ i B d{{{ ρ ↦ c }}} B d{{{ ρ' ↦ c' }}} (out_rel c c' equiv_c_c')) /\
            rel_exp M ρ M' ρ'
              (fun f f' : domain => forall (c c' : domain) (equiv_c_c' : in_rel c c'), rel_mod_app f c f' c' (out_rel c c' equiv_c_c')).
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  invert_rel_typ_body_nouip.
  do 2 eexists; repeat split; mauto.
Qed.

Lemma rel_exp_of_pi : forall {Γ env_rel M M' i j A B},
    {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }} ->
	(forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
      exists in_rel out_rel,
        rel_typ i A ρ A ρ' in_rel /\
          (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_typ j B d{{{ ρ ↦ c }}} B d{{{ ρ' ↦ c' }}} (out_rel c c' equiv_c_c')) /\
          rel_exp M ρ M' ρ'
            (fun f f' : domain => forall (c c' : domain) (equiv_c_c' : in_rel c c'), rel_mod_app f c f' c' (out_rel c c' equiv_c_c'))) ->
    {{ Γ ⊨ M ≈ M' : Π A B }}.
Proof.
  intros.
  eexists_rel_exp_with (max i j).
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_rel).
  match goal with
  | _: rel_typ i A ρ A ρ' ?x |- _ =>
      rename x into in_rel
  end.
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  eexists; split; econstructor; mauto.
  - per_univ_elem_econstructor; eauto using per_univ_elem_cumu_max_left.
    + intros.
      (on_all_hyp: destruct_rel_by_assumption in_rel).
      econstructor; eauto using per_univ_elem_cumu_max_right.
    + solve_refl.
  - mauto.
Qed.

Ltac eexists_rel_exp_of_pi :=
  unshelve eapply (rel_exp_of_pi _); shelve_unifiable; [eassumption |].

Ltac extract_output_info_with ρ c ρ' c' env_rel :=
  let Hequiv := fresh "equiv" in
  (assert (Hequiv : {{ Dom ρ ↦ c ≈ ρ' ↦ c' ∈ env_rel }}) by (apply_relation_equivalence; mauto 3);
   apply_relation_equivalence;
   (on_all_hyp: fun H => destruct (H _ _ Hequiv));
   destruct_conjs;
   destruct_by_head rel_typ;
   destruct_by_head rel_exp).

Lemma rel_exp_pi_core : forall {i o B o' B' R out_rel},
    (forall c c',
        R c c' ->
        rel_exp B d{{{ o ↦ c }}} B' d{{{ o' ↦ c' }}} (per_univ i)) ->
    (** We use the next equality to make unification on `out_rel` works *)
    (out_rel = fun c c' (equiv_c_c' : R c c') m m' =>
                 forall R',
                   rel_typ i B d{{{ o ↦ c }}} B' d{{{ o' ↦ c' }}} R' ->
                   R' m m') ->
    (forall c c' (equiv_c_c' : R c c'), rel_typ i B d{{{ o ↦ c }}} B' d{{{ o' ↦ c' }}} (out_rel c c' equiv_c_c')).
Proof with intuition.
  intros.
  subst.
  (on_all_hyp: destruct_rel_by_assumption R).
  econstructor; mauto.
  destruct_by_head per_univ.
  apply -> per_univ_elem_morphism_iff; eauto.
  split; intros; destruct_by_head rel_typ; handle_per_univ_elem_irrel...
  assert (rel_typ i B d{{{ o ↦ c }}} B' d{{{ o' ↦ c' }}} _) by mauto.
  intuition.
Qed.

Lemma rel_exp_pi_cong : forall {i Γ A A' B B'},
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ, A ⊨ B ≈ B' : Type@i }} ->
    {{ Γ ⊨ Π A B ≈ Π A' B' : Type@i }}.
Proof with mautosolve.
  intros * HA HB.
  invert_rel_exp_of_typ HA env_relΓ.
  invert_rel_exp_of_typ HB.
  invert_per_ctx_envs.
  apply_relation_equivalence.
  eexists_rel_exp_of_typ.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head per_univ.
  handle_per_univ_elem_irrel.
  econstructor; mauto.
  eexists.
  per_univ_elem_econstructor; eauto.
  - intros.
    eapply rel_exp_pi_core; mauto 3.
    reflexivity.
  - solve_refl.
Qed.

#[export]
Hint Resolve rel_exp_pi_cong : mctt.

Lemma rel_exp_pi_sub : forall {i Γ σ Δ A B},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ ⊨ A : Type@i }} ->
    {{ Δ, A ⊨ B : Type@i }} ->
    {{ Γ ⊨ (Π A B)[σ] ≈ Π (A[σ]) (B[q σ]) : Type@i }}.
Proof with mautosolve.
  intros * [env_relΓ [? [env_relΔ []]]] HA HB.
  invert_rel_exp_of_typ HA.
  invert_rel_exp_of_typ HB.
  invert_per_ctx_envs.
  match goal with
  | _: _ <~> cons_per_ctx_env env_relΔ ?x |- _ =>
      rename x into elem_relA
  end.
  apply_relation_equivalence.
  eexists_rel_exp_of_typ.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  assert {{ Dom ρ'σ' ≈ ρ'σ' ∈ env_relΔ }} by (etransitivity; [symmetry |]; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head per_univ.
  handle_per_univ_elem_irrel.
  econstructor; mauto.
  eexists.
  per_univ_elem_econstructor; eauto.
  - eapply rel_exp_pi_core; eauto; try reflexivity.
    intros.
    extract_output_info_with ρσ c ρ'σ' c' (cons_per_ctx_env env_relΔ elem_relA); econstructor...
  - solve_refl.
Qed.

#[export]
Hint Resolve rel_exp_pi_sub : mctt.

Lemma rel_exp_fn_cong : forall {i Γ A A' B M M'},
    {{ Γ ⊨ A ≈ A' : Type@i }} ->
    {{ Γ, A ⊨ M ≈ M' : B }} ->
    {{ Γ ⊨ λ A M ≈ λ A' M' : Π A B }}.
Proof with mautosolve.
  intros * HA HM.
  invert_rel_exp_of_typ HA env_relΓ.
  invert_rel_exp HM env_relΓA.
  invert_per_ctx_envs.
  match goal with
  | _: _ <~> cons_per_ctx_env env_relΓ ?x |- _ =>
      rename x into elem_relA
  end.
  handle_per_ctx_env_irrel.
  eexists_rel_exp_of_pi.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head per_univ.
  handle_per_univ_elem_irrel.
  do 2 eexists.
  repeat split; [econstructor | | econstructor]; mauto.
  - eapply rel_exp_pi_core; try reflexivity.
    intros.
    extract_output_info_with ρ c ρ' c' (cons_per_ctx_env env_relΓ elem_relA).
    econstructor...
  - intros.
    extract_output_info_with ρ c ρ' c' (cons_per_ctx_env env_relΓ elem_relA).
    econstructor; mauto.
    intros.
    destruct_by_head rel_typ.
    handle_per_univ_elem_irrel...
Qed.

#[export]
Hint Resolve rel_exp_fn_cong : mctt.

Lemma rel_exp_fn_sub : forall {Γ σ Δ A M B},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ , A ⊨ M : B }} ->
    {{ Γ ⊨ (λ A M)[σ] ≈ λ A[σ] M[q σ] : (Π A B)[σ] }}.
Proof with mautosolve.
  intros * [env_relΓ [? [env_relΔ []]]] HM.
  invert_rel_exp HM.
  invert_per_ctx_envs.
  handle_per_ctx_env_irrel.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  eexists.
  split; econstructor; mauto 4.
  - per_univ_elem_econstructor; [apply per_univ_elem_cumu_max_right | | solve_refl]; eauto.
    intros.
    eapply rel_exp_pi_core; eauto; try reflexivity.
    clear dependent c.
    clear dependent c'.
    intros.
    extract_output_info_with ρσ c ρ'σ' c' (cons_per_ctx_env env_relΔ head_rel).
    econstructor; eauto.
    eexists.
    eapply per_univ_elem_cumu_max_left...
  - intros ? **.
    extract_output_info_with ρσ c ρ'σ' c' (cons_per_ctx_env env_relΔ head_rel).
    econstructor; mauto.
    intros.
    destruct_by_head rel_typ.
    handle_per_univ_elem_irrel...
Qed.

#[export]
Hint Resolve rel_exp_fn_sub : mctt.

Lemma rel_exp_app_cong : forall {Γ M M' A B N N'},
    {{ Γ ⊨ M ≈ M' : Π A B }} ->
    {{ Γ ⊨ N ≈ N' : A }} ->
    {{ Γ ⊨ M N ≈ M' N' : B[Id,,N] }}.
Proof with intuition.
  intros * [env_relΓ]%rel_exp_of_pi_inversion HN.
  destruct_conjs.
  invert_rel_exp HN.
  eexists_rel_exp.
  intros.
  assert (equiv_p'_p' : env_relΓ ρ' ρ') by (etransitivity; [symmetry |]; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  handle_per_univ_elem_irrel.
  destruct_by_head rel_exp.
  simplify_evals.
  match goal with
  | _: {{ ⟦ N ⟧ ρ ↘ ^?n }},
      _: {{ ⟦ N ⟧ ρ' ↘ ^?n0 }},
        _: {{ ⟦ N' ⟧ ρ' ↘ ^?n'0 }},
          _: ?in_rel ?n ?n'0 |- _ =>
      assert (in_rel n n0) by (etransitivity; [| symmetry]; eassumption);
      assert (in_rel n n'0) by intuition;
      (on_all_hyp: destruct_rel_by_assumption in_rel)
  end.
  handle_per_univ_elem_irrel.
  eexists.
  split; econstructor; mauto 3...
Qed.

#[export]
Hint Resolve rel_exp_app_cong : mctt.

Lemma rel_exp_app_sub : forall {Γ σ Δ M A B N},
    {{ Γ ⊨s σ : Δ }} ->
    {{ Δ ⊨ M : Π A B }} ->
    {{ Δ ⊨ N : A }} ->
    {{ Γ ⊨ (M N)[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }}.
Proof with mautosolve.
  intros * Hσ [env_relΔ]%rel_exp_of_pi_inversion HN.
  destruct_conjs.
  invert_rel_sub Hσ.
  invert_rel_exp HN.
  pose env_relΓ.
  pose env_relΔ.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  handle_per_univ_elem_irrel.
  destruct_by_head rel_exp.
  (on_all_hyp_rev: destruct_rel_by_assumption in_rel).
  eexists.
  split; econstructor...
Qed.

#[export]
Hint Resolve rel_exp_app_sub : mctt.

Lemma rel_exp_pi_beta : forall {Γ A M B N},
  {{ Γ , A ⊨ M : B }} ->
  {{ Γ ⊨ N : A }} ->
  {{ Γ ⊨ (λ A M) N ≈ M[Id,,N] : B[Id,,N] }}.
Proof with mautosolve.
  intros * [env_relΓA] HN.
  destruct_conjs.
  invert_rel_exp HN env_relΓ.
  invert_per_ctx_envs.
  handle_per_ctx_env_irrel.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  handle_per_univ_elem_irrel.
  destruct_by_head rel_exp.
  match goal with
  | _: {{ ⟦ N ⟧ ρ ↘ ^?n }},
      _: {{ ⟦ N ⟧ ρ' ↘ ^?n' }} |- _ =>
      extract_output_info_with ρ n ρ' n' (cons_per_ctx_env env_relΓ head_rel)
  end.
  eexists.
  split; econstructor...
Qed.

#[export]
Hint Resolve rel_exp_pi_beta : mctt.

Lemma rel_exp_pi_eta : forall {Γ M A B},
  {{ Γ ⊨ M : Π A B }} ->
  {{ Γ ⊨ M ≈ λ A (M[Wk] #0) : Π A B }}.
Proof with mautosolve.
  intros * [env_relΓ]%rel_exp_of_pi_inversion.
  destruct_conjs.
  eexists_rel_exp_of_pi.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  do 2 eexists.
  repeat split; only 1,3: econstructor; mauto.
  intros.
  (on_all_hyp: destruct_rel_by_assumption in_rel)...
Qed.

#[export]
Hint Resolve rel_exp_pi_eta : mctt.
