From stdpp Require Export list gmap.
From iris.algebra Require Export list cmra.
From iris.algebra Require Import gset.
From iris.algebra Require Import updates local_updates proofmode_classes big_op gmap.

Section unital_properties.
Context `{Countable K} {A : ucmra}.
Implicit Types m : gmap K A.
Implicit Types i : K.
Implicit Types x y : A.

#[local]
Instance singleton_proper i : Proper ((≡) ==> (≡)) (singletonM i : A → gmap K A).
Proof. apply (ne_proper _). Qed.

Lemma singleton_big_opS {X : Type} `{Countable1 : Countable X} (i : K) (M : gset X) (f : X → A):
  M ≠ ∅ →
  (([^op set] x ∈ M, {[i := f x]}) : gmapUR K A) ≡ {[i := [^op set] x ∈ M, f x]}.
Proof.
  induction M as [ | x M IH1] using set_ind_L.
  { set_solver. }
  intros _.
  induction M as [ | y M IH2] using set_ind_L.
  { rewrite union_empty_r_L ?big_opS_singleton //. }
  rewrite big_opS_union; last by set_solver.
  symmetry.
  rewrite big_opS_union; last by set_solver.
  rewrite -singleton_op.
  f_equiv.
  { rewrite ?big_opS_singleton //. }
  rewrite IHM //; set_solver.
Qed.

Lemma singleton_big_opS_le {X : Type} `{Countable1 : Countable X} (i : K) (M : gset X) (f : X → A):
  (([^op set] x ∈ M, {[i := f x]}) : gmapUR K A) ≼  {[i := [^op set] x ∈ M, f x]}.
Proof.
  induction M as [ | x M IH1] using set_ind_L.
  { rewrite big_opS_empty. eexists. rewrite left_id //. }
  rewrite singleton_big_opS; last by set_solver.
  reflexivity.
Qed.

End unital_properties.

From iris.bi Require bi.
From iris.algebra Require Import dfrac_agree.
From Perennial.base_logic Require Import own.
From Perennial.Helpers Require Import ipm.
Set Default Proof Using "Type".

Section big_sepS_split.


  (* TODO: move this to a more shareable place *)
  Lemma big_sepS_singleton_sep_half {K A} `{Countable K} `{!inG Σ (gmapUR K (dfrac_agreeR A))}
    γ (X : gset K) (f : K → A) :
    ([∗ set] s ∈ X, own γ {[ s := to_dfrac_agree (DfracOwn 1) (f s)]}) -∗
    ([∗ set] s ∈ X, own γ {[ s := to_dfrac_agree (DfracOwn (1 / 2)) (f s)]}) ∗
    ([∗ set] s ∈ X, own γ {[ s := to_dfrac_agree (DfracOwn (1 / 2)) (f s)]}).
  Proof.
    iIntros "H".
    rewrite -big_sepS_sep.
    iApply (big_sepS_mono with "H").
    iIntros (x Hin) "H".
    rewrite -own_op singleton_op.
    rewrite -dfrac_agree_op.
    rewrite dfrac_op_own Qp.half_half //.
  Qed.

  Lemma own_gset_to_gmap_singleton_sep_half {K A} `{Countable K} `{!inG Σ (gmapUR K (dfrac_agreeR A))}
    γ (X : gset K) (a : A):
    own γ (gset_to_gmap (to_dfrac_agree (DfracOwn 1) a) X) -∗
    ([∗ set] s ∈ X, own γ {[ s := to_dfrac_agree (DfracOwn (1 / 2)) a]}) ∗
    ([∗ set] s ∈ X, own γ {[ s := to_dfrac_agree (DfracOwn (1 / 2)) a]}).
  Proof.
    rewrite -big_opS_gset_to_gmap big_opS_own_1 -big_sepS_singleton_sep_half //.
  Qed.

  Lemma gset_to_gmap_valid `{Countable K} {A : cmra} (X : gset K) (a : A):
    ✓ a →
    ✓ (gset_to_gmap a X : gmapUR K A).
  Proof.
    intros Hval k. rewrite lookup_gset_to_gmap.
    destruct (guard _); auto.
    rewrite //=.
  Qed.

End big_sepS_split.
