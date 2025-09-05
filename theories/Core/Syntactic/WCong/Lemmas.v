From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.WCong Require Export Definitions.
Import Syntax_Notations.

Lemma exp_subst_wcong_sym :
  (forall {M N}, {{ ⊢ M ≈≈ N  }} -> {{ ⊢ N ≈≈ M  }}) /\ 
  (forall {σ τ}, {{ ⊢s σ ≈≈ τ }} -> {{ ⊢s τ ≈≈ σ }}).
Proof.
  intros. apply syntactic_wcong_mut_ind; mauto 3.
Qed.

Corollary exp_wcong_sym : 
  forall {M N}, {{ ⊢ M ≈≈ N  }} -> {{ ⊢ N ≈≈ M  }}.
Proof.
  intros. apply exp_subst_wcong_sym. auto.
Qed.

Corollary subst_wcong_sym : 
  forall {σ τ}, {{ ⊢s σ ≈≈ τ }} -> {{ ⊢s τ ≈≈ σ }}.
Proof.
  intros. apply exp_subst_wcong_sym. auto.
Qed.

#[export]
Hint Resolve exp_wcong_sym subst_wcong_sym : mctt.

Lemma exp_subst_wcong_trans :
  (forall {M N}, {{ ⊢ M ≈≈ N  }} -> (forall N', {{ ⊢ N ≈≈ N'  }} -> {{ ⊢ M ≈≈ N' }})) /\
  (forall {σ τ}, {{ ⊢s σ ≈≈ τ }} -> (forall τ', {{ ⊢s τ ≈≈ τ' }} -> {{ ⊢s σ ≈≈ τ' }})) .
Proof.
  intros. apply syntactic_wcong_mut_ind;
    intros; progressive_inversion; mauto 4.
  - econstructor; mauto 3.
Qed.

Corollary exp_wcong_trans : 
  forall {M N N'}, {{ ⊢ M ≈≈ N  }} -> {{ ⊢ N ≈≈ N'  }} -> {{ ⊢ M ≈≈ N' }}.
Proof.
  intros. eapply exp_subst_wcong_trans; eauto.
Qed.

Corollary subst_wcong_trans : 
  forall {σ τ τ'}, {{ ⊢s σ ≈≈ τ }} -> {{ ⊢s τ ≈≈ τ' }} -> {{ ⊢s σ ≈≈ τ' }}.
Proof.
  intros. eapply exp_subst_wcong_trans; eauto.
Qed.

#[export]
Hint Resolve exp_wcong_trans subst_wcong_trans : mctt.

#[export]
Instance exp_weak_cong_PER : PER exp_weak_cong.
Proof.
  split; mauto.
Qed.

#[export]
Instance subst_weak_cong_PER : PER subst_weak_cong.
Proof.
  split; mauto.
Qed.

Lemma nf_ne_wcong_sym :
  (forall {M N}, {{ ⊢nf M ≈≈ N  }} -> {{ ⊢nf N ≈≈ M  }}) /\ 
  (forall {M N}, {{ ⊢ne M ≈≈ N }} -> {{ ⊢ne N ≈≈ M }}).
Proof.
  intros. apply normal_syntactic_wcong_mut_ind; mauto 5.
Qed.

Corollary nf_wcong_sym : 
  forall {M N}, {{ ⊢nf M ≈≈ N  }} -> {{ ⊢nf N ≈≈ M  }}.
Proof.
  intros. apply nf_ne_wcong_sym. auto.
Qed.

Corollary ne_wcong_sym : 
  forall {M N}, {{ ⊢ne M ≈≈ N }} -> {{ ⊢ne N ≈≈ M }}.
Proof.
  intros. apply nf_ne_wcong_sym. auto.
Qed.

#[export]
Hint Resolve nf_wcong_sym ne_wcong_sym : mctt.

Lemma nf_ne_wcong_trans : 
  (forall {M N}, {{ ⊢nf M ≈≈ N  }} -> (forall N', {{ ⊢nf N ≈≈ N'  }} -> {{ ⊢nf M ≈≈ N' }})) /\
  (forall {M N}, {{ ⊢ne M ≈≈ N }} -> (forall N', {{ ⊢ne N ≈≈ N' }} -> {{ ⊢ne M ≈≈ N' }})) .
Proof.
  intros. apply normal_syntactic_wcong_mut_ind; 
    intros; progressive_inversion; mauto 6.
Qed.

Corollary nf_wcong_trans : 
  forall {M N N'}, {{ ⊢nf M ≈≈ N  }} -> {{ ⊢nf N ≈≈ N'  }} -> {{ ⊢nf M ≈≈ N' }}.
Proof.
  intros. eapply nf_ne_wcong_trans; eauto.
Qed.

Corollary ne_wcong_trans : 
  forall {M N N'}, {{ ⊢ne M ≈≈ N }} -> {{ ⊢ne N ≈≈ N' }} -> {{ ⊢ne M ≈≈ N' }}.
Proof.
  intros. eapply nf_ne_wcong_trans; eauto.
Qed.

#[export]
Hint Resolve nf_wcong_trans ne_wcong_trans : mctt.

#[export]
Instance nf_weak_cong_PER : PER nf_weak_cong.
Proof.
  split; mauto 3.
Qed.

#[export]
Instance ne_weak_cong_PER : PER ne_weak_cong.
Proof.
  split; mauto 3.
Qed.
