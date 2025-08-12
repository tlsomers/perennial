From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Export crash_weakestpre staged_invariant_alt wpc_nval.
Set Default Proof Using "Type".
Import uPred.

Definition wp_nval `{!irisGS Λ Σ, !crashGS Σ} E1 P :=
  ((∀ mj q g1 D κs,
       global_state_interp g1 mj D κs -∗ NC q -∗ ||={E1|⊤∖D, ∅|∅}=> ∃ D', ||={∅|∅, E1|⊤∖D'}=>
       ∃ mj', ⌜mj' = mj ∨ (/2 < mj' ≤ mj)%Qp⌝ ∗ global_state_interp g1 mj' D' κs ∗ NC q ∗
        |~{E1, E1}~>
          ∀ g1' κs', global_state_interp g1' mj' D' κs' -∗ NC q -∗ ||={E1|⊤∖D', E1|⊤∖D}=>
            global_state_interp g1' mj D κs' ∗ P ∗ NC q))%I.

Section modality.
Context `{IRISG: !irisGS Λ Σ, !generationGS Λ Σ}.

Lemma wp_nval_strong_mono E P P' :
  wp_nval E P -∗
  (P -∗ |NC={E}=> P') -∗
  wp_nval E P'.
Proof.
  iIntros "Hwp_nval Hwand".
  rewrite /wp_nval. iIntros (?????) "H HNC".
  iMod ("Hwp_nval" with "[$] [$]") as (?) "H".
  iModIntro. iExists _. iMod "H" as (?) "($&$&$&Hstep)".
  iModIntro. iApply (step_update_wand with "[$]").
  iIntros "Hstep" (??) "Hg HNC".
  iMod ("Hstep" with "[$] [$]") as "($&HP&HNC)".
  rewrite ncfupd_eq /ncfupd_def. by iMod ("Hwand" with "[$] [$]") as "$".
Qed.

Lemma wp_nval_intro E P :
  P -∗ wp_nval E P.
Proof.
  rewrite /wp_nval. iIntros "HP" (?????) "H $".
  iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo"; [set_solver..|].
  iFrame "H". iModIntro. iMod "Hclo". iModIntro.
  iSplitR; first (iPureIntro; by left).
  iApply step_update_intro; first set_solver.
  iIntros (??) "$ $". by iFrame.
Qed.

Lemma wp_nval_True E : ⊢ wp_nval E True%I.
Proof.
  by iApply wp_nval_intro.
Qed.

Lemma wp_nval_ncfupd E P :
  wp_nval E (|NC={E}=> P) -∗ wp_nval E P.
Proof.
  iIntros "HP".
  iApply (wp_nval_strong_mono with "HP"); eauto.
Qed.

Lemma ncfupd_wp_nval E P :
  (|NC={E}=> wp_nval E P) -∗ wp_nval E P.
Proof.
  iIntros "HP".
  rewrite /wp_nval. iIntros (?????) "H HNC".
  iIntros. rewrite ncfupd_eq.
  iSpecialize ("HP" with "[$]").
  iMod (fupd_mask_mono with "HP") as "(HP&HNC)"; auto.
  iApply ("HP" with "[$] [$]").
Qed.


Context `{!later_tokG IRISG} `{!pri_invG IRISG}.

Lemma wpc0_mj_le' E s mj1 mj2 e Φ Φc:
  (mj1 = mj2 ∨ /2 < mj1 ≤ mj2)%Qp →
  wpc0 s mj1 E e Φ Φc -∗
  wpc0 s mj2 E e Φ Φc.
Proof using pri_invG0.
  destruct 1 as [->|H]; [eauto|].
  by apply wpc0_mj_le.
Qed.

Lemma wp_nval_wpc_nval E P :
  later_tok -∗
  ▷ wp_nval E (later_tok -∗ P) -∗
  wpc_nval E P.
Proof using later_tokG0 pri_invG0.
  iIntros "Htok Hval" (E' e s Φ Φc Hnval Hsub) "Hwp".
  iDestruct (later_tokN_use with "[$]") as "[[?_] Hcl]".
  rewrite /wp_nval/wpc_nval.
  rewrite ?wpc_unfold /wpc_pre. iIntros (mj).
  rewrite Hnval. iSplit; last first.
  { iDestruct ("Hwp" $! _) as "(_&$)". }
  iIntros (q σ1 g1 D κ κs nt) "Hσ Hg HNC".
  iSplit. { iDestruct ("Hwp" $! mj) as "(Hwp&_)". iDestruct ("Hwp" with "[$] [$] [$]") as "[$ _]". }
  iIntros.
  iApply (physical_step2_atomic2 E (⊤ ∖ D)).
  iMod (fupd_mask_subseteq E) as "Hclo"; [done..|].
  iApply (lc_fupd2_add_laterN with "[$]"). iNext. iNext. iModIntro.
  iMod ("Hval" with "[$] [$]") as (?) ">Hstep".
  iDestruct "Hstep" as (?) "(%Heq&Hg&HNC&Hstep)".
  iDestruct ("Hwp" $! mj') as "(Hwp&_)".
  iDestruct ("Hwp" with "[$] [$] [$] [//]") as "H".
  iApply (physical_step2_step_update with "[$]").
  iApply (physical_step2_step_update with "[Hcl]").
  { iMod "Hcl" as "_". iModIntro. iIntros "/= [H _]". iExact "H". }
  iApply (physical_step2_atomic2 E' (⊤ ∖ D')). iMod "Hclo" as "_".
  iModIntro. iApply (physical_step2_wand_later with "H"); [done..|].
  iIntros "!> (Hσ & Hg & Hwpc & Hfork & HNC)".
  iMod (fupd_mask_subseteq E) as "Hclo"; [done..|].
  iModIntro. iIntros "Htok Hnval".
  iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo'"; [set_solver..|].
  iModIntro. iMod "Hclo'" as "_".
  iMod ("Hnval" with "[$] [$]") as "(Hg&HP&HNC)". iModIntro.
  iMod "Hclo" as "_". iModIntro. iFrame.
  iSplitR "Hfork".
  - iApply (wpc0_mj_le'); first done.
    iApply (wpc0_strong_mono with "Hwpc"); auto. iSplit; last eauto.
    iIntros (?) "HΦ". iModIntro. iApply "HΦ". by iApply "HP".
  - iApply (big_sepL_mono with "[$]").
    iIntros (???) "Hwpc".
    by iApply (wpc0_mj_le').
Qed.

End modality.
