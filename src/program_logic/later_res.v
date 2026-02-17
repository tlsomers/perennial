From iris.proofmode Require Import base tactics classes.
From Perennial.Helpers Require Import ipm.
From Perennial.base_logic Require Export invariants.
From Perennial.program_logic Require Import crash_weakestpre weakestpre.
Set Default Proof Using "Type".


(* This class holds for IrisG instances with certain properties needed to show
   the existence of a token that can be spent to strip a later around a `wpc` *)
Class later_tokG {Λ Σ} (IRISG : irisGS Λ Σ) := {
  f_exp : ∀ n, 10*n ≤ f n;
}.

Section later_tok.

Context `{IRISG: !invGS Σ, trGS Σ}.

Definition later_tokN_def n : iProp Σ := ⧗ (n*2) ∗ £ (n*2).
Local Definition later_tokN_aux : seal ( @later_tokN_def). Proof. by eexists. Qed.
Definition later_tokN := later_tokN_aux.(unseal).
Local Definition later_tokN_unseal :
  @later_tokN = @later_tokN_def := later_tokN_aux.(seal_eq).

Lemma later_tok_split n₁ n₂ :
  later_tokN (n₁ + n₂) ⊣⊢ later_tokN n₁ ∗ later_tokN n₂.
Proof.
  rewrite later_tokN_unseal /later_tokN_def !Nat.mul_add_distr_r tr_split lc_split.
  iSplit; iIntros "[[$$] [$$]]".
Qed.

Global Instance later_tokN_timeless n : Timeless (later_tokN n).
Proof. rewrite later_tokN_unseal /later_tokN_def. apply _. Qed.

Global Instance from_sep_later_tok_add n₁ n₂ :
  FromSep (later_tokN (n₁ + n₂)) (later_tokN n₁) (later_tokN n₂) | 0.
Proof.
  by rewrite /FromSep later_tok_split.
Qed.
Global Instance from_sep_later_tok_S n :
  FromSep (later_tokN (S n)) (later_tokN 1) (later_tokN n) | 1.
Proof.
  by rewrite /FromSep (later_tok_split 1 n).
Qed.

Global Instance combine_sep_later_tok_add n₁ n₂ :
  CombineSepAs (later_tokN n₁) (later_tokN n₂) (later_tokN (n₁ + n₂)) | 1.
Proof.
  by rewrite /CombineSepAs later_tok_split.
Qed.

Global Instance combine_sep_later_tok_S_l n :
  CombineSepAs (later_tokN n) (later_tokN 1) (later_tokN (S n)) | 0.
Proof.
  by rewrite /CombineSepAs comm (later_tok_split 1 n).
Qed.

Global Instance into_sep_later_tok_add n₁ n₂ :
  IntoSep (later_tokN (n₁ + n₂)) (later_tokN n₁) (later_tokN n₂) | 0.
Proof.
  by rewrite /IntoSep later_tok_split.
Qed.
Global Instance into_sep_later_tok_S n :
  IntoSep (later_tokN (S n)) (later_tokN 1) (later_tokN n) | 1.
Proof.
  by rewrite /IntoSep (later_tok_split 1 n).
Qed.

End later_tok.

Notation later_tok := (later_tokN 1).

Section res.

Context `{IRISG: !irisGS Λ Σ, generationGS Λ Σ}.
Context `{LT: !later_tokG IRISG}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φc : iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Lemma later_tokN_use n :
  later_tokN n -∗
  £ (n*2) ∗ |~~> later_tokN (n*10).
Proof using LT.
  rewrite later_tokN_unseal /later_tokN_def.
  iIntros "[H⧗ $]".
  iMod (step_update_tr_use with "H⧗") as "_".
  iIntros "!> [H⧗ H£]".
  assert (n * 10 * 2 ≤ f (n*2)) as Hle.
  { etrans; [|apply f_exp]; lia. }
  iDestruct (tr_weaken with "[$]") as "$"; first done.
  iDestruct (lc_weaken with "[$]") as "$"; done.
Qed.

Definition later_tokN_pure_step E P:
  (later_tokN 2 -∗ |={E}=> P) -∗
  |={E}⧗=> P.
Proof using LT.
  iIntros "HP".
  iApply (physical_step_step); iSplit.
  { iMod tr_persistent_zero as "$". iMod (fupd_mask_subseteq ∅) as "_"; set_solver. }
  iIntros "Hlc Htr".
  iMod (fupd_mask_subseteq ∅) as "Hclose"; [set_solver..|].
  iModIntro. iApply step_fupdN_intro; [done|].
  iNext. iNext. iMod "Hclose".
  rewrite later_tokN_unseal /later_tokN_def.
  iApply "HP".
  iDestruct (lc_weaken with "Hlc") as "$".
  { pose proof (f_exp 1); lia. }
  iDestruct (tr_weaken with "Htr") as "$".
  { pose proof (f_exp 1); lia. }
Qed.

Lemma wpc_later_tok_use2_credits s E e Φ Φc :
  language.to_val e = None →
  later_tok -∗
  (£ 2 -∗ WPC e @ s; E {{ v, later_tok -∗ Φ v }} {{ Φc }}) -∗
  WPC e @ s; E {{ Φ }} {{ Φc }}.
Proof using H IRISG LT Λ Σ.
  iIntros (Hnval) "Htok Hwp".
  iDestruct (later_tokN_use with "Htok") as "[H£ Htok]".
  iDestruct ("Hwp" with "[$]") as "Hwp".
  iApply (wpc_step_update_strong _ _ _ _ _ _ (later_tok) with "[Htok]"); [by rewrite Hnval|done| |].
  - iDestruct (step_update_frame _ _ E with "[$]") as "H"; [set_solver..|].
    rewrite left_id_L. iApply (step_update_wand with "[$]").
    iIntros "/= [$ _]".
  - iApply (wpc_mono with "[$]").
    + iIntros (v) "H tok". by iApply "H".
    + iIntros "$ ? //".
Qed.

Lemma wpc_later_tok_use2 s E e Φ Φc :
  language.to_val e = None →
  later_tok -∗
  ▷▷ WPC e @ s; E {{ v, later_tok -∗ Φ v }} {{ Φc }} -∗
  WPC e @ s; E {{ Φ }} {{ Φc }}.
Proof using H IRISG LT Λ Σ.
  iIntros (?) "Htok Hwp". iApply (wpc_later_tok_use2_credits with "[$]"); auto.
  iIntros "[Hlc1 Hlc2]".
  iApply fupd_wpc.
  iApply (lc_fupd_add_later with "[$]").
  iApply (lc_fupd_add_later with "[$]").
  do 2 iNext. iModIntro.
  iApply "Hwp".
Qed.

Lemma wpc_later_tok_use s E e Φ Φc :
  language.to_val e = None →
  later_tok -∗
  ▷ WPC e @ s; E {{ v, later_tok -∗ Φ v }} {{ Φc }} -∗
  WPC e @ s; E {{ Φ }} {{ Φc }}.
Proof using H IRISG LT Λ Σ.
  iIntros (Hnval) "Htok Hwp".
  iApply (wpc_later_tok_use2 with "[$]"); auto.
Qed.

Lemma wpc_later_tok_invest s E e Φ Φc :
  language.to_val e = None →
  later_tok -∗
  WPC e @ s; E {{ v, later_tokN 10 -∗ Φ v }} {{ Φc }} -∗
  WPC e @ s; E {{ Φ }} {{ Φc }}.
Proof using H IRISG LT Λ Σ.
  iIntros (Hnval) "[Htok Hlc] Hwp".
  iApply (wpc_step_update_strong _ _ _ _ _ _ (later_tokN 10)%I with "[Htok]"); [by rewrite Hnval|done| |].
  - iDestruct (later_tokN_use with "[$]") as "[_ ?]".
    iDestruct (step_update_frame _ _ E with "[$]") as "H"; [set_solver..|].
    rewrite left_id_L //.
  - iApply (wpc_mono with "[$]").
    + iIntros (v) "H tok". by iApply "H".
    + iIntros "$ ? //".
Qed.

Lemma wpc_later_tok_pure_step `{!Inhabited (state Λ)} `{!Inhabited (global_state Λ)} φ s E e1 e2 Φ Φc:
  PureExec φ 1 e1 e2 →
  φ →
  (Φc ∧ ((later_tok ∗ later_tok) -∗ WPC e2 @ s; E {{ Φ }} {{ Φc }})) -∗
  WPC e1 @ s; E {{ Φ }} {{ Φc }}.
Proof using H IRISG LT Λ Σ.
  iIntros (Hexec Hφ) "H".
  specialize (Hexec Hφ).
  inversion Hexec as [|? e1' e2' e3' [Hsafe ?] Hrest]. subst.
  inversion Hrest; subst.
  assert (∀ σ1 g1, reducible e1 σ1 g1).
  { intros. apply reducible_no_obs_reducible. eauto. }
  iApply wpc_lift_step_pstep.
  { eapply (reducible_not_val _ inhabitant inhabitant); eauto. }
  iSplit; [iRight in "H"|iLeft in "H"; by iFrame].
  iIntros. iSplit.
  { iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
    iPureIntro. destruct s; eauto.
  }
  iIntros.
  iApply (later_tokN_pure_step). iIntros "[Htok1 Htok2] !>".
  edestruct (pure_step_det _ _ _ _ _ _ _ H1) as (->&->&->&->&->).
  simpl. iFrame. iSplit; last done. iApply ("H" with "[$]").
Qed.

Lemma wp_later_tok_pure_step `{!Inhabited (state Λ)} `{!Inhabited (global_state Λ)} φ s E e1 e2 Φ:
  PureExec φ 1 e1 e2 →
  φ →
  ((later_tok ∗ later_tok) -∗ WP e2 @ s; E {{ Φ }}) -∗
  WP e1 @ s; E {{ Φ }}.
Proof using H IRISG LT Λ Σ.
  iIntros (Hexec Hφ) "H".
  rewrite wp_eq /wp_def.
  iApply wpc_later_tok_pure_step; auto.
Qed.

End res.
