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

Section res.

Context `{IRISG: !irisGS Λ Σ, generationGS Λ Σ}.
Context `{LT: !later_tokG IRISG}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φc : iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Definition later_tok : iProp Σ := ⧗ 2 ∗ £ 2.

Lemma later_toks_equiv n :
  ⧗ (n*2) ∗ £ (n*2) -∗ Nat.iter n (λ P, later_tok ∗ P) True.
Proof.
  induction n.
  - by iIntros.
  - replace (S n * 2) with (2 + n * 2) by lia.
    iIntros "[[Htr Htr1] [Hlc Hlc1]]".
    rewrite Nat.iter_succ.
    iDestruct (IHn with "[$]") as "$".
    by iFrame.
Qed.

Lemma wpc_later_tok_use2_credits s E e Φ Φc :
  language.to_val e = None →
  later_tok -∗
  (£ 2 -∗ WPC e @ s; E {{ v, later_tok -∗ Φ v }} {{ Φc }}) -∗
  WPC e @ s; E {{ Φ }} {{ Φc }}.
Proof using H IRISG LT Λ Σ.
  iIntros (Hnval) "[Htok Hlc] Hwp".
  iDestruct ("Hwp" with "[$]") as "Hwp".
  iApply (wpc_use_step_strong _ _ _ _ _ _ (later_tok) True%I with "[Htok]"); [by rewrite Hnval|done| |].
  - iSplit; [|done].
    iIntros (P D) "HP".
    iApply (physical_step_tr_use with "Htok").
    iApply (physical_step_wand with "HP"). iIntros "HP H⧗ H£".
    iDestruct (lc_weaken with "[$]") as "$".
    { pose proof (f_exp 2); lia. }
    iDestruct (tr_weaken with "[$]") as "$".
    { pose proof (f_exp 2); lia. }
    done.
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
  WPC e @ s; E {{ v, Nat.iter 10 (λ P, later_tok ∗ P) True%I -∗ Φ v }} {{ Φc }} -∗
  WPC e @ s; E {{ Φ }} {{ Φc }}.
Proof using H IRISG LT Λ Σ.
  iIntros (Hnval) "[Htok Hlc] Hwp".
  iApply (wpc_use_step_strong _ _ _ _ _ _ (Nat.iter 10 (λ P, later_tok ∗ P) True)%I True%I with "[Htok]"); [by rewrite Hnval|done| |].
  - iSplit; [|done].
    iIntros (P D) "HP".
    iApply (physical_step_tr_use with "Htok").
    iApply (physical_step_wand with "HP"). iIntros "HP H⧗ H£".
    iFrame.
    iDestruct (later_toks_equiv 10 with "[-]") as "$"; [|done].
    iDestruct (lc_weaken with "[$]") as "$".
    { pose proof (f_exp 2); lia. }
    iDestruct (tr_weaken with "[$]") as "$".
    { pose proof (f_exp 2); lia. }
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
  iApply wpc_lift_step_physical.
  { unshelve (eapply reducible_not_val; eauto).
    { eapply inhabitant. }
    { eapply inhabitant. }
  }
  iSplit; last first.
  { iLeft in "H". eauto. }
  iIntros. iSplit.
  { iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
    iPureIntro. destruct s; eauto.
  }
  iIntros. iRight in "H".
  iApply (physical_step_step); iSplit.
  { iMod tr_persistent_zero as "$". iMod (fupd_mask_subseteq ∅) as "_"; set_solver. }
  iIntros "Hlc Htr".
  iDestruct (lc_weaken (2+2) with "Hlc") as "[H£1 H£2]".
  { pose proof (f_exp 1); lia. }
  iDestruct (tr_weaken (2+2) with "Htr") as "[H⧗1 H⧗2]".
  { pose proof (f_exp 1); lia. }
  iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
  iModIntro. iApply step_fupd2N_intro. iNext. iNext. iMod "Hclose". iModIntro.
  edestruct (pure_step_det _ _ _ _ _ _ _ H1) as (->&->&->&->&->).
  simpl. iFrame. iApply "H". iFrame.
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
