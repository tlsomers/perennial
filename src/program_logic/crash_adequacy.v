From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From Perennial.base_logic.lib Require Import wsat.
From Perennial.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export step_fupd_extra crash_lang crash_weakestpre.
Import uPred.
Import language.

Set Default Proof Using "Type".

Section crash_adequacy.
Context `{!irisGS Λ Σ, generationGS Λ Σ}.
Implicit Types s : stuckness.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

Context (mj: fracR).
(* The IH of the theorems here requires working with some fixed choice of mj in the wpc0 form,
   instead of wpc. So, we introduce here a notation to insert the mj explicitly to porting these proofs easier *)
Local Notation "'WPC' e @ E1 {{ Φ } } {{ Φc } }" := (wpc0 NotStuck mj E1 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Local Notation "'WPC' e @ s ;  E1 {{ Φ } } {{ Φc } }" := (wpc0 s mj E1 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Local Notation "'WPC' e @ s ;  E1 {{ Φ } } {{ Φc } }" := (wpc0 s mj E1 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : stdpp_scope.

Notation wptp s t := ([∗ list] ef ∈ t, WPC ef @ s; ⊤ {{ fork_post }} {{ True }})%I.

Lemma wpc_step s e1 σ1 g1 D κ κs e2 σ2 g2 efs m Φ Φc :
  prim_step e1 σ1 g1 κ e2 σ2 g2 efs →
  state_interp σ1 m -∗
  global_state_interp g1 mj D (κ ++ κs) -∗
  WPC e1 @ s; ⊤ {{ Φ }} {{ Φc }} -∗ NC 1 -∗
  |={⊤|⊤}⧗=>
  state_interp σ2 (length efs + m) ∗
  global_state_interp g2 mj D κs ∗
  WPC e2 @ s; ⊤ {{ Φ }} {{ Φc }} ∗
  wptp s efs ∗
  NC 1.
Proof.
  rewrite {1}wpc0_unfold /wpc_pre. iIntros (?) "Hσ Hg H HNC".
  rewrite (val_stuck e1 σ1 g1 κ e2 σ2 g2 efs) //.
  iDestruct "H" as "(H&_)".
  iDestruct ("H" $! _ σ1 with "Hσ Hg HNC [//]") as "H".
  iApply (physical_step2_atomic2 ⊤ (⊤∖D)).
  iMod (fupd2_mask_subseteq ⊤ (⊤∖D)) as "Hclo"; try set_solver+.
  iModIntro. iApply (physical_step2_wand_later with "H"); [done..|].
  iIntros "!> (?&?&?&?)". iMod "Hclo".
  destruct (to_val e2); eauto; by iFrame.
Qed.

Lemma wptp_step s e1 t1 t2 κ κs σ1 g1 D σ2 g2 Φ Φc :
  step (e1 :: t1,(σ1,g1)) κ (t2, (σ2,g2)) →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 mj D (κ ++ κs) -∗
  WPC e1 @ s; ⊤ {{ Φ }} {{ Φc }}-∗ wptp s t1 -∗ NC 1 -∗
  ∃ e2 t2', ⌜t2 = e2 :: t2'⌝ ∗
  |={⊤|⊤}⧗=>
  state_interp σ2 (pred (length t2)) ∗
  global_state_interp g2 mj D κs ∗
  WPC e2 @ s; ⊤ {{ Φ }} {{ Φc}} ∗ wptp s t2' ∗ NC 1.
Proof.
  iIntros (Hstep) "Hσ Hg He Ht HNC".
  destruct Hstep as [e1' σ1' g1' e2' σ2' g2' efs [|? t1'] t2' ?? Hstep]; simplify_eq/=.
  - iExists e2', (t2' ++ efs). iSplitR; first by eauto.
    iDestruct (wpc_step with "Hσ Hg He HNC") as "H"; first done.
    iApply (physical_step2_wand_later with "H"); [done..|].
    iIntros "!> (Hσ & Hg & He2 & Hefs)".
    rewrite Nat.add_comm length_app. by iFrame.
  - iExists e, (t1' ++ e2' :: t2' ++ efs); iSplitR; first eauto.
    iDestruct "Ht" as "(Ht1 & He1 & Ht2)".
    iDestruct (wpc_step with "Hσ Hg He1 HNC") as "H"; first done.
    iApply (physical_step2_wand_later with "H"); [done..|].
    iIntros "!> (Hσ & Hg & He2 & Hefs)".
    rewrite !length_app /= !length_app.
    replace (length t1' + S (length t2' + length efs))
      with (length efs + (length t1' + S (length t2'))) by lia. by iFrame.
Qed.

Lemma wptp_steps s n e1 t1 κs κs' t2 σ1 g1 D σ2 g2 Φ Φc :
  nsteps n (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 mj D (κs ++ κs') -∗
  WPC e1 @ s; ⊤ {{ Φ }} {{ Φc }} -∗ wptp s t1 -∗ NC 1 -∗
  (||={⊤|⊤, ⊤|∅}=> |={⊤}⧗=>^n ||={⊤|∅, ⊤|⊤}=> ∃ e2 t2',
    ⌜t2 = e2 :: t2'⌝ ∗
    state_interp σ2 (pred (length t2)) ∗
    global_state_interp g2 mj D κs' ∗
    WPC e2 @ s; ⊤ {{ Φ }} {{ Φc }} ∗ wptp s t2' ∗
    NC 1).
Proof.
  revert e1 t1 κs κs' t2 σ1 g1 σ2 g2;
  induction n as [|n IH]=> e1 t1 κs κs' t2 σ1 g1 σ2 g2.
  { inversion_clear 1; iIntros "?????".
    iApply (fupd2_mask_intro_subseteq); [set_solver..|].
    iExists e1, t1; iFrame; eauto 10. }
  iIntros (Hsteps) "Hσ Hg He Ht HNC". inversion_clear Hsteps as [|?? [t1' [σ1' g1']]].
  iApply physical_stepN_physical_step2. rewrite -(assoc_L (++)).
  iDestruct (wptp_step with "Hσ Hg He Ht HNC") as (e1' t1'' ?) "H"; first eauto; simplify_eq.
  iApply (physical_step2_wand_later with "H"); [done..|].
  iIntros "!> (Hσ & Hg & He & Ht & HNC)".
  by iApply (IH with "Hσ Hg He Ht HNC").
Qed.

Lemma wpc_safe κs m e σ g D Φ Φc q :
  state_interp σ m -∗
  global_state_interp g mj D κs -∗
  WPC e @ ⊤ {{ Φ }} {{ Φc }} -∗ NC q -∗
  ||={⊤|⊤, ∅|∅}=>
  ⌜is_Some (to_val e) ∨ reducible e σ g⌝.
Proof.
  rewrite wpc0_unfold /wpc_pre. iIntros "Hσ Hg H". iDestruct "H" as "(H&_)".
  destruct (to_val e) as [v|] eqn:?.
  { iIntros "_". iApply fupd2_mask_intro; [done..|].
    iIntros "_".  auto. }
  iIntros "HNC".
  iMod (fupd2_mask_subseteq ⊤ (⊤ ∖ D)) as "Hclo"; try set_solver+.
  iDestruct ("H" $! _ _ _ _ _ [] with "[$] [Hg] [$]") as "[H _]".
  - by rewrite app_nil_r.
  - iMod "H" as "%". iPureIntro. by right.
Qed.

Local Lemma wptp0_strong_adequacy Φ Φc κs' s n e1 t1 κs t2 σ1 g1 D σ2 g2 :
  nsteps n (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 mj D (κs ++ κs') -∗
  WPC e1 @ s; ⊤ {{ Φ }} {{ Φc }} -∗
  wptp s t1 -∗
  NC 1 -∗
  ||={⊤|⊤, ⊤|∅}=> |={⊤}⧗=>^n ||={⊤|∅, ⊤|⊤}=> (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    state_interp σ2 (length t2') ∗
    global_state_interp g2 mj D κs' ∗
    from_option Φ True (to_val e2) ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v) ∗
    NC 1).
Proof.
  iIntros (Hstep) "Hσ Hg He Ht HNC".
  iDestruct (wptp_steps with "Hσ Hg He Ht HNC") as "Hwp"; first done.
  iApply (physical_stepN_wand with "Hwp").
  iMod 1 as (e2' t2' ?) "(Hσ & Hg & Hwp & Ht & HNC)"; simplify_eq/=.
  iExists _, _. iSplitL ""; first done. iFrame "Hσ".
  iMod (fupd2_mask_subseteq ⊤ (⊤ ∖ D)) as "Hclo"; try set_solver+.
  iMod (wpc0_value_inv_option with "Hwp Hg HNC") as "($&Hg&HNC)".
  clear Hstep. iMod "Hclo" as "_". iInduction t2' as [|e t2'] "IH"; csimpl; first by iFrame.
  iDestruct "Ht" as "[Hv Ht]".
  destruct (to_val e) as [v|] eqn:He.
  + apply of_to_val in He as <-.
    iMod (fupd2_mask_subseteq ⊤ (⊤ ∖ D)) as "Hclo'"; try set_solver+.
    iMod (wpc0_value_inv' with "Hv Hg HNC") as "($&?&?)".
    iMod "Hclo'" as "_".
    by iApply ("IH" with "[$] [$] [$]").
  + by iApply ("IH" with "[$] [$]").
Qed.

Local Lemma wptp0_progress Φ Φc κs' n e1 t1 κs t2 σ1 g1 D σ2 g2 e2 :
  nsteps n (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) →
  e2 ∈ t2 →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 mj D (κs ++ κs') -∗
  WPC e1 @ NotStuck; ⊤ {{ Φ }} {{ Φc }} -∗
  wptp NotStuck t1 -∗
  NC 1 -∗
  ||={⊤|⊤, ⊤|∅}=> |={⊤}⧗=>^n ||={⊤|∅, ∅|∅}=>
   ⌜ not_stuck e2 σ2 g2 ⌝.
Proof.
  iIntros (Hstep Hel) "Hσ Hg He Ht HNC".
  iDestruct (wptp_steps with "Hσ Hg He Ht HNC") as "Hwp"; first done.
  iApply (physical_stepN_wand with "Hwp").
  iMod 1 as (e2' t2' ?) "(Hσ & Hg & Hwp & Ht & HNC)"; simplify_eq/=.
  apply elem_of_cons in Hel as [<-|(t1''&t2''&->)%elem_of_list_split].
  - iPoseProof (wpc_safe with "Hσ Hg Hwp HNC") as "H".
    iMod "H". eauto.
  - iDestruct "Ht" as "(_ & He' & _)".
    iPoseProof (wpc_safe with "Hσ Hg He' HNC") as "H".
    by iMod "H".
Qed.

Local Lemma wptp0_strong_crash_adequacy Φ Φc κs' s n e1 t1 κs t2 σ1 g1 D σ2 g2 :
  nsteps n (e1 :: t1, (σ1, g1)) κs (t2, (σ2, g2)) →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 mj D (κs ++ κs') -∗
  WPC e1 @ s; ⊤ {{ Φ }} {{ Φc }} -∗
  wptp s t1 -∗
  NC 1 -∗
  ||={⊤|⊤, ⊤|∅}=> |={⊤}⧗=>^n ||={⊤|∅, ⊤|⊤}=>
  (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    Φc ∗ state_interp σ2 (length t2') ∗ global_state_interp g2 mj D κs' ∗ C).
Proof.
  iIntros (Hstep) "Hσ Hg He Ht HNC".
  iMod (wptp_steps with "Hσ Hg He Ht HNC") as "Hwp"; first done.
  iApply (physical_stepN_wand with "[$]"). iModIntro.
  iMod 1 as (e2' t2' ?) "(Hσ & Hg & Hwp & Ht & HNC)"; simplify_eq/=.
  iMod (fupd2_mask_subseteq ⊤ (⊤ ∖ D)) as "Hclo"; try set_solver+.
  iMod (NC_upd_C with "HNC") as "#HC".
  iPoseProof (wpc0_crash with "[$] Hg [$]") as ">[$$]".
  iMod "Hclo". iFrame "#∗".
  iModIntro. by iExists _.
Qed.
End crash_adequacy.

Section crash_adequacy.
Context `{!irisGS Λ Σ, generationGS Λ Σ}.
Implicit Types s : stuckness.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

(* Now we prove a version where we use normal wpc instead of wpc0. *)

Notation wptp s t := ([∗ list] ef ∈ t, WPC ef @ s; ⊤ {{ fork_post }} {{ True }})%I.

Lemma wptp_strong_adequacy Φ Φc κs' s n e1 t1 κs t2 σ1 g1 mj D σ2 g2 :
  nsteps n (e1 :: t1, (σ1, g1)) κs (t2, (σ2, g2)) →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 mj D (κs ++ κs') -∗
  WPC e1 @ s; ⊤ {{ Φ }} {{ Φc }} -∗
  wptp s t1 -∗
  NC 1 -∗
  ||={⊤|⊤, ⊤|∅}=> |={⊤}⧗=>^n ||={⊤|∅, ⊤|⊤}=> (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    state_interp σ2 (length t2') ∗
    global_state_interp g2 mj D κs' ∗
    from_option Φ True (to_val e2) ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v) ∗
    NC 1).
Proof.
  iIntros (?) "?? Hwpc Hwptp Hnc".
  iApply (wptp0_strong_adequacy mj with "[$] [$] [Hwpc] [Hwptp] [$]"); first eassumption.
  { by iApply wpc0_wpc. }
  { iApply (big_sepL_mono with "Hwptp"). iIntros.
    iApply (wpc0_wpc); eauto.
  }
Qed.

Lemma wptp_progress Φ Φc κs' n e1 t1 κs t2 σ1 g1 mj D σ2 g2 e2 :
  nsteps n (e1 :: t1, (σ1, g1)) κs (t2, (σ2, g2)) →
  e2 ∈ t2 →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 mj D (κs ++ κs') -∗
  WPC e1 @ NotStuck; ⊤ {{ Φ }} {{ Φc }} -∗
  wptp NotStuck t1 -∗
  NC 1 -∗
  ||={⊤|⊤, ⊤|∅}=> |={⊤}⧗=>^n ||={⊤|∅, ∅|∅}=>
  (⌜not_stuck e2 σ2 g2 ⌝).
Proof.
  iIntros (??) "?? Hwpc Hwptp Hnc".
  iApply (wptp0_progress mj with "[$] [$] [Hwpc] [Hwptp] [$]"); first done; first done.
  { by iApply wpc0_wpc. }
  { iApply (big_sepL_mono with "Hwptp"). iIntros.
    iApply (wpc0_wpc); eauto.
  }
Qed.

Lemma wptp_strong_crash_adequacy Φ Φc κs' s n e1 t1 κs t2 σ1 g1 mj D σ2 g2 :
  nsteps n (e1 :: t1, (σ1, g1)) κs (t2, (σ2, g2)) →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 mj D (κs ++ κs') -∗
  WPC e1 @ s; ⊤ {{ Φ }} {{ Φc }} -∗
  wptp s t1 -∗
  NC 1 -∗
  ||={⊤|⊤, ⊤|∅}=> |={⊤}⧗=>^n ||={⊤|∅, ⊤|⊤}=>
  (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    Φc ∗ state_interp σ2 (length t2') ∗ global_state_interp g2 mj D κs' ∗ C).
Proof.
  iIntros (?) "?? Hwpc Hwptp Hnc".
  iApply (wptp0_strong_crash_adequacy mj with "[$] [$] [Hwpc] [Hwptp] [$]"); first eassumption.
  { by iApply wpc0_wpc. }
  { iApply (big_sepL_mono with "Hwptp"). iIntros.
    iApply (wpc0_wpc); eauto.
  }
Qed.

End crash_adequacy.
