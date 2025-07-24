From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From Perennial.Helpers Require Import ipm.
From Perennial.base_logic.lib Require Import wsat.
From Perennial.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export crash_lang recovery_weakestpre dist_weakestpre.
From Perennial.program_logic Require Import crash_adequacy.
Import uPred.

Set Default Proof Using "Type".

Section distributed_adequacy.
Context `{!irisGS Λ Σ}.
Context (CS : crash_semantics Λ).

Context (mj: fracR).
(* The IH of the theorems here requires working with some fixed choice of mj in the wpc0 form,
   instead of wpc. So, we introduce here a notation to insert the mj explicitly to porting these proofs easier *)
Local Notation "'WPC' e @ E1 {{ Φ } } {{ Φc } }" := (wpc0 NotStuck mj E1 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Local Notation "'WPC' e @ s ; E1 {{ Φ } } {{ Φc } }" := (wpc0 s mj E1 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : bi_scope.
Local Notation "'WPC' e @ s ; E1 {{ Φ } } {{ Φc } }" := (wpc0 s mj E1 e%E Φ Φc)
  (at level 20, e, Φ, Φc at level 200, only parsing) : stdpp_scope.

Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φinv : generationGS Λ Σ → iProp Σ.
Implicit Types Φc : generationGS Λ Σ → val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Definition wptp (gen : generationGS Λ Σ) s tpool :=
  ([∗ list] ef ∈ tpool, WPC ef @ s; ⊤ {{ fork_post }} {{ True }})%I.

Definition wpnode (gen : generationGS Λ Σ) (dn: dist_node) :=
  (match tpool dn with
  | [] => False%I
  | e :: tp =>
    ∃ Φ Φinv Φr,
    wpr0 CS NotStuck mj gen ⊤ e (boot dn) Φ Φinv Φr (* to be used after a reboot *) ∗
    wptp gen NotStuck tp
  end)%I.

Definition stwpnode (gen : generationGS Λ Σ) (dn: dist_node) : iProp Σ :=
  (state_interp (local_state dn) (pred (length (tpool dn))) ∗
   NC 1) ∗
  wpnode gen dn.

Definition stwpnodes (dns: list dist_node) : iProp Σ :=
  [∗ list] dn ∈ dns, ∃ gen, stwpnode gen dn.

Lemma stwpnode_step gen eb t1 σ1 g1 D t2 σ2 g2 κ κs:
  step (t1, (σ1,g1)) κ (t2, (σ2,g2)) →
  global_state_interp g1 mj D (κ ++ κs) -∗
  stwpnode gen {| boot := eb; tpool := t1; local_state := σ1 |} -∗
  |={⊤|⊤}⧗=>
  global_state_interp g2 mj D κs ∗
  stwpnode gen {| boot := eb; tpool := t2; local_state := σ2 |}.
Proof.
  iIntros (Hstep) "Hg Hnode".
  iDestruct "Hnode" as "((Hσ&HNC)&Hwptp)".
  destruct t1; first done. simpl.
  iDestruct "Hwptp" as (Φ Φinv Φr) "(Hwpr&Hwptp)". simpl.
  iPoseProof (crash_adequacy.wptp_step with "[$Hσ] [Hg] [Hwpr] [Hwptp] [HNC]") as "H"; eauto.
  { rewrite wpr0_unfold/wpr0_pre. eauto. }
  iDestruct "H" as (e2 t2' ->) "H".
  iApply (physical_step_wand with "H"). iIntros "(Hσ&Hg&Hwpr&Hwptp&HNC)".
  iFrame.
  simpl. iExists Φ, Φinv, Φr.
  rewrite wpr0_unfold/wpr0_pre. iFrame.
Qed.

Lemma stwpnode_crash gen eb t1 σ1 g σ2 κs D:
  crash_prim_step CS σ1 σ2 →
  global_state_interp g mj D κs -∗
  stwpnode gen {| boot := eb; tpool := t1; local_state := σ1 |} -∗
  |={⊤|⊤}⧗=> ∃ gen',
  global_state_interp g mj D κs ∗
  stwpnode gen' {| boot := eb; tpool := [eb]; local_state := σ2 |}.
Proof.
  iIntros (Hstep) "Hg Hnode".
  iDestruct "Hnode" as "((Hσ&HNC)&Hwptp)".
  destruct t1; first done. simpl.
  iDestruct "Hwptp" as (Φ Φinv Φr) "(Hwpr&Hwptp)".
  iMod (NC_upd_C with "HNC") as "#HC".
  rewrite wpr0_unfold/wpr0_pre.
  iApply physical_step_fupd_l.
  iMod (@fupd2_mask_subseteq _ _ ⊤ ⊤ ⊤ (⊤ ∖ D)) as "Hclo"; try set_solver+.
  iMod (wpc0_crash with "Hwpr [Hg] []") as "H".
  { eauto. }
  { iFrame "#". }
  iDestruct "H" as "(Hg&H)".
  iDestruct ("H" with "[//] [$] [Hg]") as "H".
  { eauto. }
  iMod "Hclo". iModIntro.
  iApply (physical_step_subseteq ⊤ D); eauto.
  iApply (physical_step_wand with "H").
  iDestruct 1 as (HG') "(HNC&Hσ&Hg&(_&Hwpr))".
  iClear "HC".
  iExists HG'.
  iFrame. rewrite /wptp. rewrite big_sepL_nil. eauto.
Qed.

Lemma stwpnodes_step dns1 g1 D dns2 g2 κ κs :
  dist_step (CS := CS) (dns1, g1) κ (dns2, g2) →
  global_state_interp g1 mj D (κ ++ κs) -∗
  stwpnodes dns1 -∗
  |={⊤|⊤}⧗=>
  global_state_interp g2 mj D κs ∗
  stwpnodes dns2.
Proof.
  iIntros (Hstep) "Hg Hnodes".
  inversion Hstep as [ρ1 κs' ρ2 m eb t1 σ1 t2 σ2 Hlookup1 Hlookup2 Hprim |
                      ρ1 ρ2 m eb σ1 σ2 tp Hlookup1 Heq1 Heq2 Hcrash].
  - subst. rewrite /stwpnodes.
    iDestruct (big_sepL_insert_acc with "Hnodes") as "(Hdn&Hnodes)"; first eassumption.
    iDestruct "Hdn" as (ct) "Hdn".
    iDestruct (stwpnode_step with "[$] [$]") as "H"; first eassumption.
    iApply (physical_step_wand with "H").
    iIntros "($&Hnode)".
    simpl in Hlookup2. rewrite Hlookup2.
    iApply "Hnodes". iExists _. eauto.
  - subst. rewrite /stwpnodes.
    iDestruct (big_sepL_insert_acc with "Hnodes") as "(Hdn&Hnodes)"; first eassumption.
    iDestruct "Hdn" as (ct) "Hdn".
    iDestruct (stwpnode_crash with "[$] [$]") as "H"; first eassumption.
    iApply (physical_step_wand with "H").
    iDestruct 1 as (ct') "(Hg&Hnode)".
    simpl in Heq2. rewrite Heq2. iFrame.
    simpl in Heq1. rewrite Heq1.
    iApply "Hnodes". iExists _. eauto.
Qed.

Lemma stwpnodes_steps n dns1 g1 D dns2 g2 κs κs' :
  dist_nsteps (CS := CS) n (dns1, g1) κs (dns2, g2) →
  global_state_interp g1 mj D (κs ++ κs') -∗
  stwpnodes dns1 -∗
  |={⊤|⊤}⧗=>^n ||={⊤|⊤, ⊤|⊤}=>
  global_state_interp g2 mj D κs' ∗
  stwpnodes dns2.
Proof.
  revert dns1 dns2 κs κs' g1 g2.
  induction n as [|n IH]=> dns1 dns2 κs κs' g1 g2.
  { inversion_clear 1. simpl. iIntros "$ $ //". }
  simpl.
  iIntros (Hsteps) "Hσ He". inversion_clear Hsteps as [|?? [t1' σ1']].
  rewrite -(assoc_L (++)).
  iDestruct (stwpnodes_step with "Hσ He") as "H"; first eauto; simplify_eq.
  iApply (physical_step_wand with "H").
  iIntros "(Hσ & He)".
  iDestruct (IH with "Hσ He") as "IH"; done.
Qed.

Lemma stwpnodes_strong_adequacy n dns1 g1 D dns2 g2 κs κs' :
  dist_nsteps (CS := CS) n (dns1, g1) κs (dns2, g2) →
  global_state_interp g1 mj D (κs ++ κs') -∗
  (|={⊤}=> stwpnodes dns1) -∗
  ||={⊤|⊤, ⊤|⊤}=> |={⊤|⊤}⧗=>^n ||={⊤|⊤, ⊤|⊤}=>
  global_state_interp g2 mj D κs' ∗
  stwpnodes dns2.
Proof.
  iIntros (Hstep) "Hg >Ht".
  by iDestruct (stwpnodes_steps with "Hg Ht") as "Hgt".
Qed.

Lemma stwpnodes_progress n dns1 g1 D dns2 g2 κs κs' dn e :
  dist_nsteps (CS := CS) n (dns1, g1) κs (dns2, g2) →
  dn ∈ dns2 → e ∈ tpool dn →
  global_state_interp g1 mj D (κs ++ κs') -∗
  (|={⊤}=> stwpnodes dns1) -∗
  (||={⊤|⊤, ⊤|⊤}=> |={⊤|⊤}⧗=>^n ||={⊤|⊤, ∅|∅}=>
      ⌜ not_stuck e (local_state dn) g2 ⌝).
Proof.
  iIntros (Hstep Hin1 Hin2) "Hg >Ht".
  iDestruct (stwpnodes_steps with "Hg Ht") as "Hgt"; first done.
  iModIntro. iApply (physical_stepN_wand with "Hgt").
  iMod 1 as "(Hg & Ht)".
  rewrite /stwpnodes.
  eapply list_elem_of_lookup_1 in Hin1 as (i&Hlookup1).
  iDestruct (big_sepL_lookup with "Ht") as "Hdn"; first eassumption.
  iDestruct "Hdn" as (ct) "Hnode".
  rewrite /stwpnode.
  iDestruct "Hnode" as "((Hσ&HNC)&Hwptp)".
  rewrite /wpnode. destruct (tpool dn) as [| hd tp]; first done.
  iDestruct "Hwptp" as (???) "(Hwpr&Ht)".
  apply elem_of_cons in Hin2 as [<-|(t1''&t2''&->)%list_elem_of_split].
  - rewrite wpr0_unfold/wpr0_pre.
    iPoseProof (wpc_safe with "Hσ [Hg] Hwpr") as "H".
    { eauto. }
    iApply ("H" with "HNC").
  - iDestruct "Ht" as "(_ & He' & _)".
    iPoseProof (wpc_safe with "Hσ [Hg] He'") as "H".
    { eauto. }
    iApply ("H" with "HNC").
Qed.

End distributed_adequacy.

Theorem wpd_strong_adequacy Σ Λ CS `{Hinvpre: !invGpreS Σ} `{Htrpre: !trGpreS Σ} `{Htrgen : !tr_generation} `{Hcrashpre : !crashGpreS Σ}
    (ebσs : list node_init_cfg) g1 n κs dns2 g2 φ ntr :
  (∀ `(Hinv : !invGS Σ) `(Htr : !trGS Σ),
     ⊢ ⧗ ntr -∗ £ ntr ={⊤}=∗ ∃
        (global_stateI : global_state Λ → fracR → coPset → list (observation Λ) → iProp Σ)
        (fork_post : val Λ → iProp Σ),
       let HI := IrisGS Λ Σ Hinv Htr Htrgen (global_stateI) (fork_post) in
       global_stateI g1 1%Qp ∅ κs  ∗
       wpd CS ⊤ ebσs ∗
       (⌜ ∀ dn, dn ∈ dns2 → not_stuck_node dn g2 ⌝ -∗
         global_stateI g2 1%Qp ∅ [] -∗
         (* Under these assumptions, and while opening all invariants, we
         can conclude [φ] in the logic. After opening all required invariants,
         one can use [fupd_mask_subseteq] to introduce the fancy update. *)
         |={⊤,∅}=> ⌜ φ ⌝ )) →
  dist_nsteps (CS := CS) n (starting_dist_cfg ebσs g1) κs (dns2, g2) →
  (* Then we can conclude [φ] at the meta-level. *)
  φ.
Proof.
  intros Hwp Hsteps.
  eapply pure_soundness.
  apply (physical_stepN_soundness _ ntr n).
  iIntros (Hinv Htr) "[Htr Hlc]".
  iMod (Hwp _ _ with "Htr Hlc") as (global_stateI fork_post) "(Hg & Hwp & Hφ)".
  set (HI := IrisGS Λ Σ Hinv Htr _ (global_stateI) (fork_post)).
  iMod (stwpnodes_strong_adequacy _
               1%Qp n _ _ _ _ _ _ []
    with "[Hg] [Hwp]") as "H"; first done.
  { rewrite app_nil_r /=. iExact "Hg". }
  { rewrite /stwpnodes/wpd.
    iApply big_sepL_fmap.
    iApply big_sepL_fupd.
    iApply (big_sepL_impl with "Hwp").
    iIntros "!#" (i ρ Hlookup) "H".
    iMod NC_alloc as (Hc) "HNC".
    iMod ("H" $! Hc) as (stateI Φ Φrx Φinv) "(Hσ&Hwp)".
    set (HG := GenerationGS Λ Σ Hc stateI). iExists HG.
    rewrite /stwpnode.
    rewrite /=. iFrame "HNC Hσ".
    rewrite /wpnode/=.
    iModIntro. iExists Φ, Φinv, Φrx.
    rewrite /wptp big_sepL_nil right_id.
    by iApply wpr0_wpr.
  }
  iModIntro.
  iApply (physical_stepN_wand with "H").
  iIntros ">(Hg&_)".
  iMod (fupd2_mask_subseteq ⊤ ∅) as "Hclo"; try set_solver+.
  iApply (fupd_fupd2).
  iApply ("Hφ" with "[] [$]").
  (* progress. we run the entire adequacy proof again for this.
   we could probably factor this better... *)
  iPureIntro.
  clear- Hwp Hsteps Hinvpre Htrpre Hcrashpre.
  intros dn Hin e Hin'.
  eapply pure_soundness.
  apply (physical_stepN_soundness _ ntr n).
  iIntros (Hinv Htr) "[Htr Hlc]".
  iMod (Hwp _ _ with "Htr Hlc") as (global_stateI fork_post) "(Hg & Hwp & Hφ)".
  set (HI := IrisGS Λ Σ Hinv Htr _ (global_stateI) (fork_post)).
  iMod (stwpnodes_progress _ 1%Qp n _ _ _ _ _ _ []
    with "[Hg] [Hwp]") as "H"; try done.
  { rewrite app_nil_r /=. iExact "Hg". }
  { rewrite /stwpnodes/wpd.
    iApply big_sepL_fmap.
    iApply big_sepL_fupd.
    iApply (big_sepL_impl with "Hwp").
    iIntros "!#" (i ρ Hlookup) "H".
    iMod NC_alloc as (Hc) "HNC".
    iMod ("H" $! Hc) as (stateI Φ Φrx Φinv) "(Hσ&Hwp)".
    set (HG := GenerationGS Λ Σ Hc stateI). iExists HG.
    rewrite /stwpnode.
    rewrite /=. iFrame "HNC Hσ".
    rewrite /wpnode/=.
    iModIntro. iExists Φ, Φinv, Φrx.
    rewrite /wptp big_sepL_nil right_id.
    by iApply wpr0_wpr.
  }
Qed.

Record dist_adequate {Λ CS} (ρs: list (@node_init_cfg Λ)) (g : global_state Λ)
    (φinv: global_state Λ → Prop)  := {
  dist_adequate_not_stuck dns' g' dn :
   rtc (erased_dist_step (CS := CS)) (starting_dist_cfg ρs g) (dns', g') →
   dn ∈ dns' → not_stuck_node dn g';
  dist_adequate_inv dns' g' :
   rtc (erased_dist_step (CS := CS)) (starting_dist_cfg ρs g) (dns', g') →
   φinv g'
}.

Lemma dist_adequate_alt {Λ CS} ebσ g1 φinv :
  dist_adequate (Λ := Λ) (CS := CS) ebσ g1 φinv ↔ ∀ dns2 g2,
    rtc (erased_dist_step (CS := CS)) (starting_dist_cfg ebσ g1) (dns2, g2) →
      (∀ dn, dn ∈ dns2 → not_stuck_node dn g2) ∧
      (φinv g2).
Proof.
  split.
  - intros [] ???; naive_solver.
  - constructor; naive_solver.
Qed.

Corollary wpd_dist_adequacy_inv Σ Λ CS `{!invGpreS Σ} `{!trGpreS Σ} `{!tr_generation} `{!crashGpreS Σ}
          ebσs g φinv ntr:
  (∀ `(Hinv : !invGS Σ) `(Htr : !trGS Σ) κs,
     ⊢ ⧗ ntr -∗ £ ntr ={⊤}=∗ ∃
       (global_stateI : global_state Λ → fracR → coPset → list (observation Λ) → iProp Σ)
       (fork_post : val Λ → iProp Σ),
       let HI := IrisGS Λ Σ Hinv Htr _ (global_stateI) (fork_post) in
       global_stateI g 1%Qp ∅ κs  ∗
       wpd CS ⊤ ebσs ∗
       (∀ g κs, global_stateI g 1%Qp ∅ κs -∗ |={⊤, ∅}=> ⌜ φinv g ⌝)) →
  dist_adequate (CS := CS) ebσs g (λ g, φinv g).
Proof.
  intros Hwp.
  apply dist_adequate_alt.
  intros dns2 g2 Hsteps.
  apply erased_dist_steps_nsteps in Hsteps as [n [κs Hsteps]].
  eapply (wpd_strong_adequacy Σ _ _); [| by eauto ] => ? ?.
  iIntros "Htr Hlc".
  iMod (Hwp with "Htr Hlc") as (global_stateI fork_post) "(Hg&Hwp&Hφ)".
  iExists global_stateI, fork_post.
  iFrame. iIntros "!> %Hns Hg". iMod ("Hφ" with "[$]") as %Hφ. iPureIntro; eauto.
Qed.
