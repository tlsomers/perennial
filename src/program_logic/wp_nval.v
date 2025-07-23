From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Export crash_weakestpre staged_invariant_alt wpc_nval.
Set Default Proof Using "Type".
Import uPred.

Definition logical_step_emp `{!irisGS Λ Σ, !crashGS Σ} E D P : iProp Σ :=
  ∀ Q, (|={E|D}⧗=> Q) -∗ (|={E|D}⧗=> Q ∗ P).
Notation "|~{ E | D }~> P" := (logical_step_emp E D P) (at level 99, P at level 200, format "'[  ' |~{ E | D }~>  '/' P ']'").

Lemma logical_step_emp_wand `{!irisGS Λ Σ, !crashGS Σ} E D P Q :
  (|~{E|D}~> P) -∗  
  (P -∗ Q) -∗
  |~{E|D}~> Q.
Proof.
  iIntros "Hstep HPQ" (R) "HR".
  iDestruct ("Hstep" with "HR") as "HR".
  iApply (physical_step_wand with "HR"). iIntros "[$ P]".
  by iApply "HPQ".
Qed.

Lemma logical_step_emp_intro `{!irisGS Λ Σ, !crashGS Σ} E D P :
  P -∗
  |~{E|D}~> P.
Proof.
  iIntros "HP" (R) "HR".
  iApply (physical_step_wand with "HR"). by iIntros "$".
Qed.

Lemma logical_step_emp_use_tr_simpl `{!irisGS Λ Σ, !crashGS Σ} E D P n :
  ⧗ n -∗
  (|~{E|D}~> ⧗ (f n) -∗ £ (f n) -∗ P) -∗
  |~{E|D}~> P.
Proof.
  iIntros "H⧗ Hstep" (R) "HR".
  iDestruct ("Hstep" with "HR") as "HR".
  iApply (physical_step_tr_use with "[$]").
  iApply (physical_step_wand with "[$]").
  iIntros "($&HP) H⧗ H£".
  by iApply ("HP" with "[$] [$]").
Qed.

Lemma logical_step_apply `{!irisGS Λ Σ, !crashGS Σ} E D P Q :
  (|~{E|D}~> P) -∗
  (|={E|D}⧗=> P -∗ Q) -∗
  |={E|D}⧗=> Q.
Proof.
  iIntros "Hstep HPQ".
  iApply (physical_step_wand with "(Hstep HPQ)").
  iIntros "[HPQ HP]". by iApply "HPQ".
Qed.

Definition wp_nval `{!irisGS Λ Σ, !crashGS Σ} E1 P :=
  ((∀ mj q g1 D κs,
       global_state_interp g1 mj D κs -∗ NC q -∗ ||={E1|⊤∖D, ∅|∅}=> ∃ D', ||={∅|∅, E1|⊤∖D'}=>
       ∃ mj', ⌜mj' = mj ∨ (/2 < mj' ≤ mj)%Qp⌝ ∗ global_state_interp g1 mj' D' κs ∗ NC q ∗
        |~{E1|⊤∖D'}~>
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
  iModIntro. iApply (logical_step_emp_wand with "[$]").
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
  iApply logical_step_emp_intro.
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
  iIntros "[H⧗ H£] Hval" (E' e s Φ Φc Hnval Hsub) "Hwp".
  rewrite /wp_nval/wpc_nval.
  rewrite ?wpc_unfold /wpc_pre. iIntros (mj).
  rewrite Hnval. iSplit; last first.
  { iDestruct ("Hwp" $! _) as "(_&$)". }
  iIntros (q σ1 g1 D κ κs nt) "Hσ Hg HNC".
  iSplit. { iDestruct ("Hwp" $! mj) as "(Hwp&_)". iDestruct ("Hwp" with "[$] [$] [$]") as "[$ _]". }
  iIntros.
  iApply (physical_step_atomic E (⊤ ∖ D)).
  iMod (fupd_mask_subseteq E) as "Hclo"; [done..|].
  iApply (lc_fupd2_add_laterN with "[$]"). iNext. iNext. iModIntro.
  iMod ("Hval" with "[$] [$]") as (?) ">Hstep".
  iDestruct "Hstep" as (?) "(%Heq&Hg&HNC&Hstep)".
  iDestruct ("Hwp" $! mj') as "(Hwp&_)".
  iDestruct ("Hwp" with "[$] [$] [$] [//]") as "H".
  iApply (logical_step_apply with "Hstep").
  iApply (physical_step_atomic E' (⊤∖D')). iMod "Hclo" as "_".
  iModIntro.
  iApply (physical_step_tr_use with "[$]").
  iApply (physical_step_wand with "H").
  iIntros "(Hσ & Hg & Hwpc & Hfork & HNC) H⧗ H£ !>".
  iMod (fupd_mask_subseteq E) as "Hclo"; [done..|].
  iModIntro. iIntros "Hnval".
  iMod (fupd2_mask_subseteq ∅ ∅) as "Hclo'"; [set_solver..|].
  iModIntro. iMod "Hclo'" as "_".
  iMod ("Hnval" with "[$] [$]") as "(Hg&HP&HNC)". iModIntro.
  iMod "Hclo" as "_". iModIntro. iFrame.
  iSplitR "Hfork".
  - iApply (wpc0_mj_le'); first done.
    iApply (wpc0_strong_mono with "Hwpc"); auto. iSplit; last eauto.
    iIntros (?) "HΦ". iModIntro. iApply "HΦ". iApply "HP".
    assert (2 ≤ f 2).
    { pose proof (f_exp 2); lia. }
    iDestruct (lc_weaken with "[$]") as "$"; first done.
    by iDestruct (tr_weaken with "[$]") as "$".
  - iApply (big_sepL_mono with "[$]").
    iIntros (???) "Hwpc".
    by iApply (wpc0_mj_le').
Qed.

End modality.
