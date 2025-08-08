From iris.prelude Require Import options.

From iris.algebra Require Import stepindex_finite.

From iris.base_logic.lib Require Import iprop own later_credits time_receipts.
From iris.proofmode Require Import base environments classes classes_make
                                   modality_instances tactics.
From Perennial.base_logic Require Export fancy_updates2.
From Perennial.program_logic Require Export step_fupd_extra.


From iris.algebra.lib Require Export tr_view.
Import uPred.


(* ======== Simple tactic to do decisions with updates. ======== *)

Section fupd_decide.

  Context `{!invGS Σ}.

  Local Lemma update_decide_pure {E D} φ (P : iProp Σ) :
    Decision φ →
    (||={E|D, ∅|∅}=> ⌜φ⌝) ∧ (||={E|D, E|D}=> P) -∗ ||={E|D,E|D}=> ⌜φ⌝ ∗ P.
  Proof.
    iIntros (?).
    destruct H.
    - by iIntros "[_ >$]".
    - iIntros "[>%H' _] //".
  Qed.

  Lemma tac_fupd_decision {E D} φ (Δ : envs (iProp Σ)) Q :
    Decision φ →
    envs_entails Δ (||={E|D, ∅|∅}=> ⌜φ⌝) →
    (φ → envs_entails Δ (||={E|D, E|D}=> Q)) →
    envs_entails Δ (||={E|D, E|D}=> Q).
  Proof.
    rewrite envs_entails_unseal.
    intros Hdecision Hupdφ Hnext.
    iIntros "Henvs".
    iMod (update_decide_pure φ with "[Henvs]") as "[%Hφ Henvs]".
    - iSplit.
      + by iApply Hupdφ.
      + iModIntro. iExact "Henvs". 
    - by iApply Hnext.
  Qed.
End fupd_decide.

Tactic Notation "iModDecide" open_constr(φ) "gives" ident(H) :=
  apply (tac_fupd_decision φ _ _); [
    tc_solve |
    | intro H
  ].

Class tr_generation := TrGeneration {
  f : nat → nat;
  f_subadditive x y : f x + f y ≤ f (x + y);
}.

Program Definition tr_generation_nolc : tr_generation := {|
  f x := 0;
|}.
Final Obligation. intros; simpl; lia. Qed.

Section physical_step.

  Context `{!trGS Σ} `{!invGS Σ} `{!tr_generation}.

  Lemma f_mono x y :
    x ≤ y → f x ≤ f y.
  Proof.
    intros.
    replace y with (x + (y - x)) by lia.
    etrans; [|apply f_subadditive]; lia.
  Qed.
  
  Lemma f_zero :
    f 0 = 0.
  Proof.
    destruct (f 0) eqn:Heq; [done|].
    pose proof (f_subadditive 0 0) as Hsub; simpl in *; lia.
  Qed.

  (* Alternative formulation of `f_subadditive` which is nicer to apply. *)
  Local Lemma f_subadditive' x y z :
    x + y ≤ z → f x + f y ≤ f z.
  Proof.
    intros Heq.
    etrans; [apply f_subadditive|].
    apply f_mono; lia.
  Qed.

  (** A modality which represents a single physical step taken. Each physical step
      has additional logical steps which can be used to eliminate more laters
      (specifically (S (f nlc)) such steps). The number of additional logical steps is
      determined by time receipts, which are also updated by this modality.

      Remark: The mask changing updates are included specifically for the
      `physical_step_fupdN` rule to support the wp_step_fupdN_strong rule,
      which uses a conjunction at the WP-level rather than the physical step level.

      Note: The shape of this step describes individually the behaviors of later credits,
      spatial time receipts and persistent time receipts, which simplifies the layering lemmas. 
  *)
  Definition physical_step_def E D P : iProp Σ :=
    ||={E|D, ∅|∅}=> ∀ nlc ntr ntrp,
      tr_supply nlc -∗ (* Supply for time receipts *)
      ⧗ ntr -∗ (* Used time receipts by higher layers. *)
      ⧖ ntrp -∗ (* Persistent time receipt to increase. *)
      £ (f $ S $ nlc - ntr) -∗ (* Remaining later credits for the step. *)
      ||▷=>^(S $ f (nlc - ntr))
          tr_supply (nlc + f (S nlc) + f (S nlc)) ∗ (* Generation of time receipts. *)
          ⧗ (f ntr) ∗ (* Time receipts and later credits for higher layers. *)
          ⧖ (f (S ntrp)) ∗ (* Incremented persistent time receipt. *)
          (||={∅|∅, E|D}=> P). (* Result. *)
  
  Local Definition physical_step_aux : seal ( @physical_step_def). Proof. by eexists. Qed.
  Definition physical_step := physical_step_aux.(unseal).
  Local Definition physical_step_unseal :
    @physical_step = @physical_step_def := physical_step_aux.(seal_eq).

  Local Ltac unseal := rewrite
    ?physical_step_unseal /physical_step_def.

  (** The notation uses a ⧗ to symbolize a single step, but otherwise resembles the |={ E }▷=>
      notation used by step_fupd.

      Remark: Think about notation.
  *)
  Notation "|={ E | D }⧗=> P" := (physical_step E D P)
    (at level 99, P at level 200, E at level 50, D at level 50, format "|={ E | D }⧗=>  P") : bi_scope.

  (* The introduction rule for a physical step, derived by taking nlc = ntrp = n and ntr = 0 *)
  Lemma physical_step_step {E D} n P:
    (||={E|D, ∅|∅}=> ⧖ n) ∧ (£ (f (S n)) -∗ ⧗ (f (S n)) -∗ ||={E|D, ∅|∅}=> ||▷=>^(S $ f $ n) ||={∅|∅, E|D}=> P) -∗
    |={E | D}⧗=> P.
  Proof.
    unseal.
    iIntros "H".
    iApply fupd2_mask_intro; [set_solver..|]; iIntros "Hmask" (nlc ntr ntrp) "Hsup H⧗ H⧖ H£".
    iApply step_fupd2N_S_fupd2_l.
    iModDecide (_ ≤ _)%nat gives Hle.
    { iDestruct "H" as "[H _]".
      iMod "Hmask".
      iMod "H". iCombine "H H⧖" as "H⧖".
      iApply fupd_fupd2.
      iMod (tr_persistent_incr with "H⧖ H⧗") as "H".
      iApply (tr_supply_tr_persistent_bound with "[$] H").
    }
    iMod "Hmask" as "_".
    iMod (tr_supply_increase (f (S nlc)) with "[$] [$]") as "(Hsup & H⧖ & H⧗1)".
    iDestruct (lc_weaken (f (S n)) with "[$]") as "H£".
    { apply f_mono; lia. }
    iDestruct (tr_weaken (f (S n) + f ntr) with "H⧗1") as "[H⧗₁ H⧗₂]".
    { apply f_subadditive'; lia. }
    iMod ("H" with "[$] [$]") as "HP". iModIntro.
    iApply (step_fupd2N_wand with "[HP]").
    { iApply (step_fupd2N_le with "HP").
      apply le_n_S, f_mono; lia.
    }
    iIntros "$". iFrame.
    iApply (tr_persistent_weaken with "[$]").
    etrans; [apply (f_mono _ (S nlc))|]; lia.
  Qed.

  Lemma physical_step_wand_later {E D} P Q:
    (|={E | D}⧗=> P) -∗ ▷(P -∗ Q) -∗ |={E | D}⧗=> Q. 
  Proof.
    unseal.
    iIntros ">HP HPQ !>".
    iIntros (nlc ntr ntrp) "Hsup H⧗ H⧖ H£".
    iDestruct ("HP" with "[$] [$] [$] [$]") as "HP".
    rewrite !Nat.iter_succ_r.
    iApply (step_fupd2N_wand with "[$]").
    iIntros ">H". do 2 iModIntro.
    iMod "H" as "($ & $ & $ & HP)".
    by iApply "HPQ".
  Qed.

  Lemma physical_step_wand {E D} P Q:
    (|={E | D}⧗=> P) -∗ (P -∗ Q) -∗ |={E | D}⧗=> Q. 
  Proof.
    iIntros "HP HPQ".
    iApply (physical_step_wand_later with "[$] [$]").
  Qed.

  Lemma physical_step_fupd {E D} P :
    (|={E | D}⧗=> (||={E|D, E|D}=> P)) -∗ |={E | D}⧗=> P.
  Proof.
    unseal.
    iIntros ">HP !>" (nlc ntr ntrp) "Hsup H⧗ H⧖ H£".
    iDestruct ("HP" with "[$] [$] [$] [$]") as "HP".
    iApply step_fupd2N_S_fupd2.
    iApply (step_fupd2N_wand with "[$]").
    iIntros "($ & $ & $ & HP) // !>".
    by iMod "HP".
  Qed.

  Lemma physical_step_fupd_l {E D} P :
    (||={E|D, E|D}=> |={E|D}⧗=> P) -∗ |={E|D}⧗=> P.
  Proof.
    unseal.
    rewrite (fupd2_trans E D). iIntros "$".
  Qed.

  (** Remark: There are a few possible choices for intro here, but the single
      later variant seems the one I needed for total weakest precondition. *)
  Lemma physical_step_intro {E D} P :
    ▷ P ⊢ |={E | D}⧗=> P.
  Proof.
    iIntros "HP".
    iApply physical_step_step; iSplit.
    - iMod tr_persistent_zero as "$".
      iMod (fupd2_mask_subseteq ∅ ∅); [set_solver..|done].
    - iIntros "? ? //".
      iApply fupd2_mask_intro; [set_solver..|].
      iIntros "Hclose".
      iApply (step_fupd2N_intro). 
      iNext. iNext. by iMod "Hclose".       
  Qed.

  (* The rule for using spatial time receipts. *)
  Lemma physical_step_tr_use_strong {E D} n P :
    ⧗ n -∗ (|={E | D}⧗=> (⧗ (f n) -∗ £ (f n) -∗ ||={E|D, ∅|∅}=> ||▷=>^(f n) ||={∅|∅, E|D}=> P)) -∗ |={E | D}⧗=> P.
  Proof.
    unseal.
    iIntros "H⧗ >Hupd !>" (nlc ntr ntrp) "Hsup H⧗' H⧖ H£".
    iCombine "H⧗ H⧗'" as "H⧗".
    iDestruct (tr_supply_tr_bound with "[$] [$]") as %?.
    iDestruct (lc_weaken (f (S (nlc - (n + ntr))) + f n) with "[$]") as "[? ?]".
    { etrans; [apply f_subadditive|apply f_mono]; lia. }
    iDestruct ("Hupd" with "[$] [$] [$] [$]") as "Hupd".
    iApply (step_fupd2N_le (S (f (nlc - (n + ntr))) + f n)).
    { simpl. apply le_n_S; etrans; [apply f_subadditive|apply f_mono]; lia. }
    rewrite Nat.iter_add.
    iApply (step_fupd2N_S_fupd2).
    iApply (step_fupd2N_wand with "[$]").
    iIntros "(? & H⧗ & H⧖ & >HP)".
    iDestruct (tr_weaken (f n + f ntr) with "H⧗") as "[H⧗₁ H⧗']".
    { apply f_subadditive'; lia. }
    iApply (step_fupd2N_wand with "(HP [$] [$])").
    iIntros "$". iFrame.
  Qed.

  Lemma physical_step_tr_use {E D} n P :
    ⧗ n -∗ (|={E | D}⧗=> (⧗ (f n) -∗ £ (f n) -∗ ||={E|D, E|D}=> P)) -∗ |={E | D}⧗=> P.
  Proof.
    iIntros "H H'".
    iApply (physical_step_tr_use_strong with "[$] [H']").
    iApply (physical_step_wand with "[$]").
    iIntros "H ? ?".
    iMod (fupd2_mask_subseteq ∅ ∅) as "Hcl"; [set_solver..|].
    iModIntro. iApply (step_fupd2N_intro). iNext. iMod "Hcl".
    iApply ("H" with "[$] [$]").
  Qed.

  Local Lemma step_fupdN_sep n (P Q : iProp Σ):
    (||▷=>^n P) -∗ (||▷=>^ n Q) -∗ ||▷=>^n P ∗ Q.
  Proof.
    iIntros "HP HQ".
    iInduction n as [|n] "IH"; first by iFrame.
    simpl. iMod "HP". iMod "HQ". do 2 iModIntro. iMod "HP". iMod "HQ". iModIntro.
    iApply ("IH" with "[$] [$]").
  Qed.

  Local Lemma step_fupd_swap n (P : iProp Σ) :
    (||▷=>^n ||={∅|∅, ∅|∅}=> P) ⊢ ||={∅|∅, ∅|∅}=> ||▷=>^n P.
  Proof.
    iIntros "H". destruct n; [by simpl|].
    iApply step_fupd2N_S_fupd2. by iModIntro.
  Qed.

  (* Physical steps are atomic. *)
  Lemma physical_step_atomic {E₁ D₁} E₂ D₂ (P : iProp Σ) :
    (||={E₁|D₁, E₂|D₂}=> |={E₂ | D₂}⧗=> ||={E₂|D₂, E₁|D₁}=> P) ⊢ |={E₁ | D₁}⧗=> P.
  Proof.
    unseal.
    iIntros ">>H !>" (nlc ntr ntrp) "? ? ? ?".
    iApply (step_fupd2N_wand with "[-]").
    { iApply ("H" with "[$] [$] [$] [$]"). }
    iIntros "($ & $ & $ & >>$) //".
  Qed.

  Lemma physical_step_atomic_inv_subseteq {E₁ D₁} E₂ D₂ (P : iProp Σ) :
    E₂ ⊆ E₁ → D₂ ⊆ D₁ →
    (|={E₁ | D₁}⧗=> P) -∗ (||={E₁|D₁, E₂|D₂}=> |={E₂ | D₂}⧗=> ||={E₂|D₂, E₁|D₁}=> P).
  Proof.
    iIntros (Hse Hse') "H".
    iApply fupd2_mask_intro; [done..|].
    iIntros "Hback". iApply (physical_step_atomic E₁).
    iMod "Hback" as "_". iModIntro.
    iApply (physical_step_wand with "[$]"). iIntros "$".
    by iApply (fupd2_mask_intro_subseteq).
  Qed.

  Lemma physical_step_subseteq {E₁ D₁} E₂ D₂ (P : iProp Σ) :
    E₂ ⊆ E₁ → D₂ ⊆ D₁ →
    (|={E₂ | D₂}⧗=> P) -∗ |={E₁ | D₁}⧗=> P.
  Proof.
    iIntros (Hle Hle2) "H".
    iApply (physical_step_atomic E₂ D₂).
    iMod (fupd2_mask_subseteq E₂ D₂) as "Hclose"; [done..|].
    iModIntro. iApply (physical_step_wand with "[$]").
    by iIntros "$".
  Qed.

  (** The fupdN rule for physical steps. This uses a conjunction to allow additional
      spatial time receipts ⧗ to be used to find the lower bound, but not irreversably
      converted into persistent time receipts.
  *)
  Lemma physical_step_fupdN_strong {E₁ D₁} E₂ D₂ n (P Q R : iProp Σ) :
    (||={E₁|D₁, ∅|∅}=> ⧖ n) ∧ (
      ||={E₁|D₁, E₂|D₂}=>
        (||▷=>^(S $ f n) P -∗ ||={E₂|D₂, E₁|D₁}=> Q) ∗
        (|={E₂ | D₂}⧗=> P ∗ (Q -∗ ||={E₁|D₁, E₁|D₁}=> R))) -∗
    |={E₁ | D₁}⧗=> R.
  Proof.
    unseal.
    iIntros "H".
    iApply (fupd2_mask_intro); [set_solver..|].
    iIntros "Hclose" (nlc ntr ntrp) "Hsup H⧗ H⧖ H£".
    iApply step_fupd2N_S_fupd2_l.
    iModDecide (_ ≤ _)%nat gives Hle'.
    { iMod "Hclose" as "_".
      iDestruct "H" as "[>H _]".
      iApply fupd_fupd2.
      iMod (tr_persistent_incr with "H H⧗") as "H".
      iApply (tr_supply_tr_persistent_bound with "[$] H").
    }
    iMod "Hclose" as "_".
    iDestruct "H" as "[_ >(HP & >HQ)]".
    iDestruct ("HQ" with "[$] [$] [$] [$]") as "HR".
    iModIntro.
    iDestruct (step_fupdN_sep with "[HP] [$]") as "H".
    { iApply (step_fupd2N_le with "[$]").
      apply le_n_S, f_mono; lia.
    }
    iApply step_fupd2N_S_fupd2.
    iApply (step_fupd2N_wand with "[$]").
    iIntros "(HPQ & $ & $ & $ & HPQR) // !>".
    iApply (fupd2_trans _ _ E₂ D₂). iMod "HPQR" as "[HP HQR]".
    iModIntro. iMod ("HPQ" with "HP"). by iApply "HQR".
  Qed.

  (** The fupdN rule for physical steps. This uses a conjunction to allow additional
      spatial time receipts ⧗ to be used to find the lower bound, but not irreversably
      converted into persistent time receipts.
  *)
  Lemma physical_step_fupdN {E₁ D₁} E₂ D₂ n (P Q : iProp Σ) :
    (||={E₁|D₁, ∅|∅}=> ⧖ n) ∧
      ((||={E₁|D₁, E₂|D₂}=> ||▷=>^(S $ f n) ||={E₂|D₂, E₁|D₁}=> P) ∗
        |={E₂ | D₂}⧗=> (P -∗ ||={E₁|D₁, E₁|D₁}=> Q)) -∗
    |={E₁ | D₁}⧗=> Q.
  Proof.
    iIntros "H".
    iApply (physical_step_fupdN_strong E₂ D₂ n True); iSplit.
    - iDestruct "H" as "[$ _]".
    - iDestruct "H" as "[_ [>Hupd H]]". iModIntro.
      iSplitL "Hupd".
      + iApply (step_fupd2N_wand with "[$]").
        iIntros "$ //".
      + iApply (physical_step_wand with "[$]").
        iIntros "$".
  Qed.

  (* Increase the persistent time receipt by 1 *)
  Lemma physical_step_incr {E D} n (P : iProp Σ) :
    ⧖ n -∗ (|={E | D}⧗=> (⧖ (f (S n)) -∗ ||={E|D, E|D}=> P)) -∗ |={E | D}⧗=> P.
  Proof.
    unseal.
    iIntros "H⧖ >HP !>" (nlc ntr ntrp) "Hsup H⧗ H⧖' H£".
    iCombine "H⧖ H⧖'" as "H⧖".
    iDestruct ("HP" with "[$] [$] [$] [$]") as "HP".
    iApply (step_fupd2N_wand with "[$]").
    iIntros "($ & $ & #H & HP) //".
    iSplit.
    - iApply (tr_persistent_weaken with "H"); apply f_mono; lia.
    - iMod "HP". iApply "HP".
      iApply (tr_persistent_weaken with "H"); apply f_mono; lia.
  Qed.

  Global Instance physical_step_contractive {E D} : Contractive (physical_step E D).
  Proof.
    unseal.
    intros n P Q HPQ. rewrite /physical_step.
    do 11 f_equiv.
    rewrite !Nat.iter_succ.
    f_equiv. f_contractive. f_equiv.
    generalize (tr_supply (a + f (S a) + f (S a)))%I => R.
    induction (f (a - a0)).
    - by repeat f_equiv.
    - rewrite !Nat.iter_succ.
      by do 3 f_equiv.
  Qed.


  (* Define multiple physical steps for use in soundness and adequacy of WP. *)
  Notation "|={ E | D }⧗=>^ n P" := (Nat.iter n (physical_step E D) P)
    (at level 99, P at level 200, E at level 50, D at level 50, n at level 9, format "|={ E | D }⧗=>^ n  P") : bi_scope.

  Lemma physical_stepN_intro {E D} n P :
    P ⊢ |={E | D}⧗=>^n P.
  Proof.
    iIntros. iInduction n as []; first done.
    iApply physical_step_intro.
    by iApply "IHn".
  Qed.

  Lemma physical_stepN_subseteq {E E' D D'} n P :
    E' ⊆ E → D' ⊆ D →
    (|={E | D}⧗=>^n P) ⊢ ||={E|D,E'|D'}=> |={E' | D'}⧗=>^n P.
  Proof.
    iIntros. iInduction n as [|n].
    - simpl. iMod (fupd2_mask_subseteq E' D') as "H"; try done.
    - simpl. iMod (fupd2_mask_subseteq E' D') as "H"; try done.
      iModIntro. iApply (physical_step_atomic E D).
      iMod "H". iApply (physical_step_wand with "[$]").
      by iModIntro.
  Qed.
 

  Lemma physical_stepN_wand {E D} n P Q :
    (|={E | D}⧗=>^n P) -∗ (P -∗ Q) -∗ |={E | D}⧗=>^n Q.
  Proof.
    iIntros "HP HPQ". iInduction n as [].
    - by iApply "HPQ".
    - simpl. iApply (physical_step_wand with "HP").
      iIntros "HP".
      iApply ("IHn" with "[$] [$]"). 
  Qed.

  Lemma physical_stepN_le {E D} {n} m P :
    n ≤ m →
    (|={E | D}⧗=>^n P)%I -∗
    |={E | D}⧗=>^m P.
  Proof.
    intros. replace m with ((m - n) + n) by lia.
    rewrite Nat.iter_add.
    iIntros. by iApply physical_stepN_intro.
  Qed.

  Lemma physical_stepN_S_fupd {E D} n P :
    (|={E | D}⧗=>^(S n) (||={E|D, E|D}=> P))%I ⊢ |={E | D}⧗=>^(S n) P.
  Proof.
    iIntros. rewrite !Nat.iter_succ_r.
    iApply (physical_stepN_wand with "[$]").
    iApply (physical_step_fupd).
  Qed.

  Global Instance elim_modal_upd_physical_step p E1a E1b P Q :
    ElimModal True p false (|==> P) P (|={E1a|E1b}⧗=> Q) (|={E1a|E1b}⧗=> Q).
  Proof.
    rewrite /ElimModal intuitionistically_if_elim /=.
    iIntros (_) "[HP HPQ]". iApply physical_step_fupd_l.
    iMod "HP". by iApply "HPQ".
  Qed.

  Global Instance elim_modal_fupd2_physical_step p E1a E1b P Q :
    ElimModal True p false (||={E1a|E1b,E1a|E1b}=> P) P (|={E1a|E1b}⧗=> Q) (|={E1a|E1b}⧗=> Q).
  Proof.
    rewrite /ElimModal intuitionistically_if_elim
      fupd2_frame_r wand_elim_r.
    intro. iApply physical_step_fupd_l.
  Qed.

  Global Instance elim_modal_fupd2_physical_step_weak p E1a E1b E2a E2b P Q :
    ElimModal True p false (||={E1a|E1b,E2a|E2b}=> P) P (|={E1a|E1b}⧗=> Q) (|={E2a|E2b}⧗=> ||={E2a|E2b,E1a|E1b}=> Q) | 100.
  Proof.
    rewrite /ElimModal intuitionistically_if_elim
      fupd2_frame_r wand_elim_r.
    iIntros (_) "H". by iApply physical_step_atomic.
  Qed.

  Global Instance elim_modal_fupd_physical_step p E1a E1b P Q :
    ElimModal True p false (|={E1a,E1a}=> P) P (|={E1a|E1b}⧗=> Q) (|={E1a|E1b}⧗=> Q).
  Proof.
    rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r.
    iIntros (?) "H". iApply physical_step_fupd_l. by iApply fupd_fupd2.
  Qed.

  Global Instance elim_modal_fupd_physical_step_weak p E1a E1b E2a P Q :
    ElimModal True p false (|={E1a,E2a}=> P) P (|={E1a|E1b}⧗=> Q) (|={E2a|E1b}⧗=> ||={E2a|E1b,E1a|E1b}=> Q) | 100.
  Proof.
    rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r.
    iIntros (_) "H". iApply physical_step_atomic. by iApply fupd_fupd2.
  Qed.

  Global Instance is_except_zero_physical_step E1 E2 P :
    IsExcept0 (|={E1|E2}⧗=> P).
  Proof. unseal. apply _. Qed.

  Lemma physical_stepN_fupd_swap {E D} n P :
    (||={E|D,E|D}=> |={E|D}⧗=>^n P) ⊣⊢ |={E|D}⧗=>^n ||={E|D,E|D}=> P.
  Proof.
    destruct n; first done.
    iSplit.
    - iIntros ">H".
      iApply (physical_stepN_wand with "[$]"). iIntros "$ //".
    - iIntros. by iApply (physical_stepN_S_fupd).
  Qed.

  Global Instance elim_modal_conj (P P' Q₁ Q₂ Q₁' Q₂' : iProp Σ) :
    ElimModal True false false P P' Q₁ Q₁' →
    ElimModal True false false P P' Q₂ Q₂' →
    ElimModal True false false P P' (Q₁ ∧ Q₂) (Q₁' ∧ Q₂')%I.
  Proof.
    rewrite /ElimModal //=.
    iIntros (H1 H2 Hle) "[H HR]".
    iSplit.
    - iApply H1; first done.
      iFrame. iIntros. iDestruct ("HR" with "[$]") as "[$ _]".
    - iApply H2; first done.
      iFrame. iIntros. iDestruct ("HR" with "[$]") as "[_ $]".
  Qed.

End physical_step.

(* Redefine the notations outside of the section. *)
Notation "|={ E | D }⧗=> P" := (physical_step E D P)
  (at level 99, P at level 200, E at level 50, D at level 50, format "|={ E | D }⧗=>  P") : bi_scope.
Notation "|={ E | D }⧗=>^ n P" := (Nat.iter n (physical_step E D) P)
  (at level 99, P at level 200, E at level 50, D at level 50, n at level 9, format "|={ E | D }⧗=>^ n  P") : bi_scope.

Section soundness.

  Context `{!tr_generation}.

  (* The largest possible persistent time receipt after `ns` steps, given `m` time receipts before the first step. *)
  Local Definition tr_per_step m ns :=
    Nat.iter ns (λ n, n + f (S n) + f (S n)) m.
  
  (* The number of later credits necessary to take `k` steps, given `m` time receipts before the first step.
     As we need to know the number of later credits before invoking `physical_stepN_soundness` below,
     we give this as a definition, rather than a local definition.
  *)
  Local Definition lc_up_to_steps m k :=
    sum_list_with (λ ns, f $ S $ tr_per_step m ns) (seq 0 k).

  Local Definition laters_up_to_steps m k :=
    sum_list_with (λ ns, S $ f $ tr_per_step m ns) (seq 0 k).

  Local Lemma physical_step_soundness `{!invGS Σ} `{!trGS Σ} {E D} m P :
    tr_supply m -∗ £ (f $ S $ m) -∗ (|={E|D}⧗=> P) -∗ ||={E|D, ∅|∅}=> ||▷=>^(S $ f $ m) tr_supply (m + f (S m) + f (S m)) ∗ ||={∅|∅, E|D}=>P.
  Proof.
    iIntros "? ? HP".
    iApply step_fupd2N_S_fupd2_l.
    iMod tr_zero as "?". iMod tr_persistent_zero as "?".
    rewrite ?physical_step_unseal /physical_step_def.
    iDestruct ("HP" with "[$] [$] [$]") as "HP".
    rewrite Nat.sub_0_r.
    iMod ("HP" with "[$]") as "HP". do 2 iModIntro. iApply (step_fupd2N_wand with "HP").
    iIntros "($ & _ & _ & $)".
  Qed.

  Local Lemma physical_stepN_soundness_local `{!invGS Σ} `{!trGS Σ} {E D} m k P :
    tr_supply m -∗
    £ (lc_up_to_steps m k) -∗
    (|={E|D}⧗=>^k P) -∗
    ||={E|D, ∅|∅}=> ||▷=>^(laters_up_to_steps m k)
        tr_supply (tr_per_step m k) ∗ (||={∅|∅, E|D}=> P).
  Proof.
    iIntros "? H£ HP".
    iInduction k as [] forall (m P).
    { iFrame. iApply fupd2_mask_intro_subseteq; [set_solver..|done]. }
    rewrite Nat.iter_succ_r.
    rewrite /lc_up_to_steps /laters_up_to_steps !seq_S !sum_list_with_app !Nat.iter_add /= Nat.add_0_r.
    iDestruct "H£" as "[H£ H£']".
    iDestruct ("IHk" with "[$] [$] [$]") as ">HP".
    iApply (step_fupd2N_wand with "[$]").
    iIntros "!> [Hsup HP]".
    iApply step_fupd2N_S_fupd2_l. iMod "HP".
    iApply (physical_step_soundness with "[$] [$] [$]").
  Qed.


  Lemma physical_stepN_soundness `{!invGpreS Σ} `{!trGpreS Σ} (P : iProp Σ) `{!Plain P} n k :
    (∀ {Hinv : invGS Σ} {Htr: trGS Σ}, ⧗ n ∗ £ n ⊢ ||={⊤|⊤, ⊤|⊤}=> |={⊤|⊤}⧗=>^k ||={⊤|⊤, ∅|∅}=> P) → ⊢ P.
  Proof.
    intros HP.
    eapply (step_fupd2N_soundness _ _ _).
    iIntros (Hinv) "[H£ ?]".
    iMod (tr_supply_alloc n) as "(%Htr & Hsup & H⧗)".
    iDestruct (HP with "[$]") as ">HP".
    iDestruct (physical_stepN_soundness_local with "[$] [$] [$]") as ">HP'".
    iApply step_fupd_swap. iApply (step_fupd2N_wand with "[$]").
    iIntros "[_ >>$] //".
  Qed.
End soundness.

Section logical_step.

  Context `{!trGS Σ} `{!invGS Σ} `{!tr_generation}.

  (* A minimal reimplementation of logical step for Perennial's fupd2.
     Limited to the non-mask changing version for simplicity.
  *)

  Definition logical_step_def E D P : iProp Σ :=
    ∀ Q, (|={E|D}⧗=> Q) -∗ (|={E|D}⧗=> Q ∗ P).
  Local Definition logical_step_aux : seal ( @logical_step_def). Proof. by eexists. Qed.
  Definition logical_step := logical_step_aux.(unseal).
  Local Definition logical_step_unseal :
    @logical_step = @logical_step_def := logical_step_aux.(seal_eq).

  Local Ltac unseal := rewrite
    ?logical_step_unseal /logical_step_def.
  Local Ltac seal := fold logical_step_def; rewrite <-?logical_step_unseal.
  Notation "|~{ E | D }~> P" := (logical_step E D P) (at level 99, P at level 200, format "'[  ' |~{ E | D }~>  '/' P ']'").

  Lemma step_update_mask_weaken E D E' D' P :
    E ⊆ E' → D ⊆ D' →
    (|~{E|D}~> P) -∗
    (|~{E'|D'}~> P).
  Proof.
    unseal. iIntros (Hle Hdiff) "Hupd %Q HQ".
    iDestruct (physical_step_atomic_inv_subseteq E D with "HQ") as "HQ"; [set_solver..|].
    iApply (physical_step_atomic E D).
    iMod "HQ". iModIntro. iDestruct ("Hupd" with "HQ") as "HQ".
    iApply (physical_step_wand with "[$]").
    iIntros "[H $] //".
  Qed.

  (* TODO: Port back these into_wand instances. *)
  Global Instance elim_modal_logical_step E D E' D' P Q :
    ElimModal (E ⊆ E' ∧ D ⊆ D') false false (|~{E|D}~> P) emp (|={E'|D'}⧗=> Q) (|={E'|D'}⧗=> P -∗ Q).
  Proof.
    rewrite /ElimModal /=.
    iIntros ([??]) "[HP HPQ]".
    iDestruct (step_update_mask_weaken _ _ E' D' with "HP") as "HP"; [done..|].
    unseal. iApply (physical_step_wand with "(HP (HPQ [//]))").
    iIntros "[HPQ HP]". by iApply "HPQ".
  Qed.

  Global Instance elim_modal_logical_step' E D E' D' P Q :
    ElimModal (E ⊆ E' ∧ D ⊆ D') false false (|~{E|D}~> P) emp (|~{E'|D'}~> Q) (|~{E'|D'}~> P -∗ Q).
  Proof.
    rewrite /ElimModal /=.
    iIntros ([??]) "[HP HPQ]". iEval unseal. iIntros "%R HR".
    iMod ("HPQ" with "[//]") as "_". iMod "HP"  as "_".
    iApply (physical_step_wand with "HR").
    iIntros "$ HP HPQ". by iApply "HPQ".
  Qed.

  Lemma logical_step_wand E D P Q :
    (|~{E|D}~> P) -∗  
    (P -∗ Q) -∗
    |~{E|D}~> Q.
  Proof.
    iIntros "Hstep HPQ". iEval (unseal). iIntros (R) "HR".
    iMod "Hstep" as "_".
    iApply (physical_step_wand with "HR"). iIntros "$ P".
    by iApply "HPQ".
  Qed.

  Lemma logical_step_intro E D P :
    P -∗
    |~{E|D}~> P.
  Proof. unseal.
    iIntros "HP" (R) "HR".
    iApply (physical_step_wand with "HR"). by iIntros "$".
  Qed.

End logical_step.

Global Notation "|~{ E | D }~> P" := (logical_step E D P) (at level 99, P at level 200, format "'[  ' |~{ E | D }~>  '/' P ']'").
