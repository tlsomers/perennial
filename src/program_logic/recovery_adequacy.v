From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From Perennial.Helpers Require Import ipm.
From Perennial.base_logic.lib Require Import wsat.
From Perennial.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export crash_lang recovery_weakestpre.
From Perennial.program_logic Require Import crash_adequacy.
Import uPred.

Set Default Proof Using "Type".
Set Default Goal Selector "!".

Section recovery_adequacy.
Context `{!irisGS Λ Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φinv : generationGS Λ Σ → iProp Σ.
Implicit Types Φr : generationGS Λ Σ → val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Notation wptp s t := ([∗ list] ef ∈ t, WPC ef @ s; ⊤ {{ fork_post }} {{ True }})%I.

Fixpoint step_fupdN_fresh (ns: list nat) (HG0: generationGS Λ Σ)
         (P: generationGS Λ Σ → iProp Σ) {struct ns} :=
  match ns with
  | [] => P HG0
  | (n :: ns) =>
      ||={⊤|⊤, ⊤|∅}=> |={⊤}⧗=>^(S n) ||={⊤|∅, ⊤|⊤}=>
      ∃ HG' : generationGS Λ Σ,
       step_fupdN_fresh ns HG' P
  end%I.

Lemma step_fupdN_fresh_wand (ns: list nat) HG0 Q Q':
  step_fupdN_fresh ns HG0 Q -∗ (∀ HG, Q HG -∗ Q' HG)
  -∗ step_fupdN_fresh ns HG0 Q'.
Proof.
  revert HG0.
  induction ns => ?.
  - iIntros "H Hwand". iApply "Hwand". eauto.
  - iIntros "H Hwand". rewrite /step_fupdN_fresh -/step_fupdN_fresh.
    iApply (physical_stepN_wand with "H").
    iMod 1 as (Hg') "H".
    iExists _. by iApply (IHns with "H").
Qed.

Lemma wptp_recv_strong_normal_adequacy {CS Φ Φinv Φr κs' s HG} n mj D r1 e1 t1 κs t2 σ1 g1 σ2 g2 :
  nrsteps (CS := CS) r1 [n] (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) Normal →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 mj D (κs ++ κs') -∗
  wpr CS s HG ⊤ e1 r1 Φ Φinv Φr -∗
  wptp s t1 -∗ NC 1-∗ (
    ||={⊤|⊤, ⊤|∅}=> |={⊤}⧗=>^n ||={⊤|∅, ⊤|⊤}=>
    ∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    state_interp σ2 (length t2') ∗
    global_state_interp g2 mj D κs' ∗
    from_option Φ True (to_val e2) ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v) ∗
    NC 1).
Proof.
  iIntros (Hstep) "Hσ Hg He Ht HNC".
  inversion Hstep. subst.
  iPoseProof (wptp_strong_adequacy with "Hσ Hg [He] Ht") as "H".
  { eauto. }
  {rewrite wpr_unfold /wpr_pre. iApply "He". }
  iSpecialize ("H" with "[$]").
  rewrite /step_fupdN_fresh.
  iApply (physical_stepN_wand with "H").
  iIntros "$".
Qed.

Lemma wptp_recv_normal_progress {CS Φ Φinv Φr κs' HG} n ns mj D r1 e1 t1 κs t2 σ1 g1 σ2 g2 e2 :
  nrsteps (CS := CS) r1 (ns ++ [n]) (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) Normal →
  e2 ∈ t2 →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 mj D (κs ++ κs') -∗
  wpr CS NotStuck HG ⊤ e1 r1 Φ Φinv Φr -∗
  wptp NotStuck t1 -∗ NC 1-∗ step_fupdN_fresh ns HG (λ HG',
    ⌜ HG' = HG ⌝ ∗
    ||={⊤|⊤, ⊤|∅}=> |={⊤}⧗=>^n ||={⊤|∅, ∅|∅}=>
        ⌜ not_stuck e2 σ2 g2 ⌝ ).
Proof.
  iIntros (Hstep Hel) "Hσ Hg He Ht HNC".
  inversion Hstep. subst.
  iPoseProof (wptp_progress with "Hσ Hg [He] Ht") as "H".
  { eauto. } { done. }
  {rewrite wpr_unfold /wpr_pre. iApply "He". }
  iSpecialize ("H" with "[$]").
  assert (ns = []) as ->;
    first by (eapply nrsteps_normal_empty_prefix; eauto).
  inversion H. subst.
  rewrite /step_fupdN_fresh.
  iSplitL ""; by eauto.
Qed.

Fixpoint sum_crash_steps ns :=
  match ns with
  | [] => 0
  | n :: ns => (S n) + (sum_crash_steps ns)
  end.

Lemma wptp_recv_strong_crash_adequacy {CS Φ Φinv Φinv' Φr κs' s HG} mj D ns n r1 e1 t1 κs t2 σ1 g1 σ2 g2 :
  nrsteps (CS := CS) r1 (ns ++ [n]) (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) Crashed →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 mj D (κs ++ κs') -∗
  wpr CS s HG ⊤ e1 r1 Φ Φinv Φr -∗
  □ (∀ HG', Φinv HG' -∗ □ Φinv' HG') -∗
  wptp s t1 -∗ NC 1-∗ step_fupdN_fresh ns HG (λ HG',
    (||={⊤|⊤, ⊤|∅}=> |={⊤}⧗=>^n ||={⊤|∅, ⊤|⊤}=> (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    state_interp σ2 (length t2') ∗
    global_state_interp g2 mj D κs' ∗
    from_option (Φr HG') True (to_val e2) ∗
    □ Φinv' HG' ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v) ∗
    NC 1))).
Proof.
  revert HG e1 t1 κs κs' t2 σ1 g1 σ2 Φ.
  induction ns as [|n' ns' IH] => HG e1 t1 κs κs' t2 σ1 g1 σ2 Φ.
  { rewrite app_nil_l.
    inversion 1.
    match goal with
    | [ H : nrsteps _ _ _ _ _ _ |- _ ] => inversion H
    end.
  }
  iIntros (Hsteps) "Hσ Hg He #Hinv Ht HNC".
  inversion_clear Hsteps as [|?? [t1' ?] ????? s0].
  rewrite {1}/step_fupdN_fresh -/step_fupdN_fresh.
  destruct ρ2 as (?&[σ2_pre_crash g2_pre_crash]).
  rewrite -assoc wpr_unfold /wpr_pre.
  iMod (@wptp_strong_crash_adequacy with "[$] [$] [$] [$] [$]") as "H"; eauto.
  iModIntro. rewrite Nat.iter_succ_r.
  iApply (physical_stepN_wand with "H").
  rewrite -physical_step_fupd_l -fupd_fupd2_emp.
  iMod 1 as (e2 t2' ?) "(H&Hσ&Hg&HC)".
  iDestruct ("H" with "[//] Hσ Hg") as "H".
  iApply (physical_stepN_physical_step2 0).
  iApply (physical_step2_wand_later with "H"); [set_solver..|].
  iIntros "!> (%HG'&HNC&Hσ&Hg&Hr) /=".
  iApply fupd2_mask_intro_subseteq; [set_solver..|].
  destruct s0.
  - iDestruct "Hr" as "(_&Hr)".
    simpl in *.
    iPoseProof (IH with "[Hσ] [Hg] Hr [] [] HNC") as "$"; eauto.
  - iExists HG'.
    iAssert (□Φinv' HG')%I as "#Hinv'".
    { iDestruct "Hr" as "(Hr&_)".
      iApply "Hinv". eauto.
    }
    iDestruct "Hr" as "(_&Hr)".
    assert (ns' = []) as ->; first by (eapply nrsteps_normal_empty_prefix; eauto).
    iDestruct (wptp_recv_strong_normal_adequacy (HG:=HG') with "[Hσ] [Hg] [Hr] [] HNC") as "H"; eauto.
    simpl.
    iApply (physical_stepN_wand with "H").
    iIntros ">H !>".
    iFrame "# ∗".
Qed.

(* unfortunately this duplicates the large induction above.
There is probably some way to factor this... *)
Lemma wptp_recv_crash_progress {CS Φ Φinv Φinv' Φr κs' HG} mj D ns n r1 e1 t1 κs t2 σ1 g1 σ2 g2 ee2 :
  nrsteps (CS := CS) r1 (ns ++ [n]) (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) Crashed →
  ee2 ∈ t2 →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 mj D (κs ++ κs') -∗
  wpr CS NotStuck HG ⊤ e1 r1 Φ Φinv Φr -∗
  □ (∀ HG', Φinv HG' -∗ □ Φinv' HG') -∗
  wptp NotStuck t1 -∗ NC 1-∗ step_fupdN_fresh ns HG (λ HG',
    (||={⊤|⊤, ⊤|∅}=> |={⊤}⧗=>^n ||={⊤|∅, ∅|∅}=>
    ⌜ not_stuck ee2 σ2 g2 ⌝)).
Proof.
  revert HG e1 t1 κs κs' t2 σ1 g1 σ2 Φ.
  induction ns as [|n' ns' IH] => HG e1 t1 κs κs' t2 σ1 g1 σ2 Φ.
  { rewrite app_nil_l.
    inversion 1.
    match goal with
    | [ H : nrsteps _ _ _ _ _ _ |- _ ] => inversion H
    end.
  }
  iIntros (Hsteps Hel) "Hσ Hg He #Hinv Ht HNC".
  inversion_clear Hsteps as [|?? [t1' ?] ????? s0].
  rewrite {1}/step_fupdN_fresh -/step_fupdN_fresh.
  destruct ρ2 as (?&[σ2_pre_crash g2_pre_crash]).
  rewrite -assoc wpr_unfold /wpr_pre.
  iMod ( @wptp_strong_crash_adequacy with "[$] [$] [$] [$] [$]") as "H"; eauto.
  iModIntro. rewrite Nat.iter_succ_r.
  iApply (physical_stepN_wand with "H").
  rewrite -physical_step_fupd_l -fupd_fupd2_emp.
  iMod 1 as (e2 t2' ?) "(H&Hσ&Hg&HC)".
  iDestruct ("H" with "[//] Hσ Hg") as "H".
  iApply (physical_stepN_physical_step2 0).
  iApply (physical_step2_wand_later with "H"); [set_solver..|].
  iIntros "!> (%HG'&HNC&Hσ&Hg&Hr) /=".
  iApply fupd2_mask_intro_subseteq; [set_solver..|].
  destruct s0.
  - iDestruct "Hr" as "(_&Hr)".
    simpl in *.
    iPoseProof (IH with "[Hσ] [Hg] Hr [] [] HNC") as "H"; eauto.
  - iExists HG'.
    iAssert (□Φinv' HG')%I as "#Hinv'".
    { iDestruct "Hr" as "(Hr&_)".
      iApply "Hinv". eauto.
    }
    iDestruct "Hr" as "(_&Hr)".
    iDestruct (wptp_recv_normal_progress (HG:=HG') with "[Hσ] [Hg] [Hr] [] HNC") as "H"; eauto.
    iApply (step_fupdN_fresh_wand with "H").
    iIntros (HG'') "H".
    by iDestruct "H" as (->) "H".
Qed.

Lemma wptp_recv_strong_adequacy {CS Φ Φinv Φinv' Φr κs' s HG} ns mj D n r1 e1 t1 κs t2 σ1 g1 σ2 g2 stat :
  nrsteps (CS := CS) r1 (ns ++ [n]) (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) stat →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 mj D (κs ++ κs') -∗
  wpr CS s HG ⊤ e1 r1 Φ Φinv Φr -∗
  □ (∀ HG', Φinv HG' -∗ □ Φinv' HG') -∗
  wptp s t1 -∗ NC 1-∗ step_fupdN_fresh ns HG (λ HG',
    (||={⊤|⊤, ⊤|∅}=> |={⊤}⧗=>^n ||={⊤|∅, ⊤|⊤}=> (∃ e2 t2',
    ⌜ t2 = e2 :: t2' ⌝ ∗
    state_interp σ2 (length t2') ∗
    global_state_interp g2 mj D κs' ∗
    (match stat with
     | Normal => ⌜ HG' = HG ⌝ ∗ from_option Φ True (to_val e2)
     | Crashed => from_option (Φr HG') True (to_val e2) ∗ □ Φinv' HG'
     end)  ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v) ∗
    NC 1))).
Proof.
  intros. destruct stat.
  - iIntros. iDestruct (wptp_recv_strong_crash_adequacy with "[$] [$] [$] [$] [$] [$]") as "H"; eauto.
    iApply (step_fupdN_fresh_wand with "H"); first auto.
    iIntros (?) "H".
    iApply (physical_stepN_wand with "H").
    iMod 1 as (???) "(?&H&?&?&?)". iExists _, _.
    repeat (iSplitL ""; try iFrame; eauto).
  - iIntros.
    assert (ns = []) as ->; first by (eapply nrsteps_normal_empty_prefix; eauto).
    iDestruct (wptp_recv_strong_normal_adequacy with "[$] [$] [$] [$] [$]") as "H"; eauto.
    iApply (physical_stepN_wand with "H").
    iMod 1 as (???) "(?&H&?&?&?)". iExists _, _.
    iSplitL ""; first eauto. iFrame. eauto.
Qed.

Lemma wptp_recv_progress {CS Φ Φinv Φinv' Φr κs' HG} ns mj D n r1 e1 t1 κs t2 σ1 g1 σ2 g2 stat e2 :
  nrsteps (CS := CS) r1 (ns ++ [n]) (e1 :: t1, (σ1,g1)) κs (t2, (σ2,g2)) stat →
  e2 ∈ t2 →
  state_interp σ1 (length t1) -∗
  global_state_interp g1 mj D (κs ++ κs') -∗
  wpr CS NotStuck HG ⊤ e1 r1 Φ Φinv Φr -∗
  □ (∀ HG', Φinv HG' -∗ □ Φinv' HG') -∗
  wptp NotStuck t1 -∗ NC 1-∗ step_fupdN_fresh ns HG (λ HG',
    (||={⊤|⊤, ⊤|∅}=> |={⊤}⧗=>^n ||={⊤|∅ , ∅|∅}=> 
    ⌜ not_stuck e2 σ2 g2 ⌝)).
Proof.
  intros. destruct stat.
  - iIntros. iDestruct (wptp_recv_crash_progress with "[$] [$] [$] [$] [$] [$]") as "H"; eauto.
  - iIntros. iDestruct (wptp_recv_normal_progress with "[$] [$] [$] [$] [$]") as "H"; eauto.
    iApply (step_fupdN_fresh_wand with "H"); first auto.
    iIntros (?).
    iDestruct 1 as (->) "H".
    assert (ns = []) as ->; first by (eapply nrsteps_normal_empty_prefix; eauto).
    done.
Qed.

End recovery_adequacy.
(* 
Fixpoint fresh_later_count f g ncurr (ns: list nat) :=
  match ns with
  | [] => 0
  | n :: ns' => S (S (S (crash_adequacy.steps_sum f g ncurr (S n))))
                 + fresh_later_count f g (Nat.iter (S n) g ncurr) ns'
  end.

Lemma fresh_later_count_nil f g ncurr :
  fresh_later_count f g ncurr nil = 0.
Proof. simpl. lia. Qed.
Lemma fresh_later_count_cons f g ncurr n (ns': list nat) :
  fresh_later_count f g ncurr (n::ns') = crash_adequacy.steps_sum f g ncurr (S n) + 3
                 + fresh_later_count f g (Nat.iter (S n) g ncurr) ns'.
Proof. simpl. lia. Qed. *)

Lemma step_fupdN_fresh_rearrange {Λ Σ} `{!irisGS Λ Σ} {HG : generationGS Λ Σ} φ ns k:
  (|={⊤}=> step_fupdN_fresh ns _
                  (λ _, ||={⊤|⊤, ⊤|∅}=> |={⊤}⧗=>^k ||={⊤|∅, ∅|∅}=> ⌜φ⌝)) -∗
    ||={⊤|⊤, ⊤|∅}=> |={⊤}⧗=>^((sum_list $ fmap S $ ns) + k) ||={⊤|∅, ∅|∅}=> ⌜φ⌝.
Proof.
  iIntros "H".
  iInduction ns as [| n' ns] "IH" forall (HG).
  - rewrite /step_fupdN_fresh.
    simpl. by iMod "H".
  - iMod NC_alloc as (Hc') "HNC".
    rewrite /step_fupdN_fresh -/step_fupdN_fresh.
    iMod "H" as ">H". simpl. iModIntro. iEval (rewrite -Nat.add_assoc Nat.iter_add).
    rewrite -!Nat.iter_succ.
    iApply (physical_stepN_S_fupd).
    iApply (physical_stepN_wand with "H").
    rewrite -fupd_fupd2_emp.
    iMod 1 as (HG') "H".
    iApply ("IH" $! HG' with "H").
Qed.

Axiom functional_extensionality: forall {A B} (f g:A->B) , (forall x, f x = g x) -> f = g.

Lemma step_fupdN_fresh_soundness {Λ Σ} `{!invGpreS Σ} `{!trGpreS Σ} `{!crashGpreS Σ} (φ : Prop) ns k n:
  (∀ (Hi: invGS Σ) (Htr : trGS Σ) (Hc: crashGS Σ), ⧗ n ∗ £ n -∗ NC 1 ={⊤}=∗
    ∃ (HI: irisGS Λ Σ) (HG:generationGS Λ Σ) (Hpf1: iris_invGS = Hi) (Hpf2: iris_trGS = Htr) (Hpf4: iris_crashGS = Hc),
      (|={⊤}=> step_fupdN_fresh ns HG (λ _,
        ||={⊤|⊤, ⊤|∅}=> |={⊤}⧗=>^k ||={⊤|∅, ∅|∅}=>
        ⌜φ⌝))%I) →
  φ.
Proof.
  intros Hiter.
  eapply pure_soundness.
  eapply (physical_stepN_soundness _ n (sum_list (S <$> ns) + k)) => Hinv Htr.
  iIntros "H⧗£".
  iMod NC_alloc as (Hc) "HNC".
  iMod (Hiter Hinv Htr Hc with "H⧗£ HNC") as (Hiris Hgen <- <- <-) "H".
  iApply (step_fupdN_fresh_rearrange φ ns k with "H").
Qed.

Record recv_adequate {Λ CS} (s : stuckness) (e1 r1: expr Λ) (σ1 : state Λ) (g1 : global_state Λ)
    (φ φr: val Λ → state Λ → global_state Λ → Prop) (φinv: state Λ → global_state Λ → Prop)  := {
  recv_adequate_result_normal t2 σ2 g2 v2 :
   erased_rsteps (CS := CS) r1 ([e1], (σ1,g1)) (of_val v2 :: t2, (σ2,g2)) Normal →
   φ v2 σ2 g2;
  recv_adequate_result_crashed t2 σ2 g2 v2 :
   erased_rsteps (CS := CS) r1 ([e1], (σ1,g1)) (of_val v2 :: t2, (σ2,g2)) Crashed →
   φr v2 σ2 g2;
  recv_adequate_not_stuck t2 σ2 g2 e2 stat :
   s = NotStuck →
   erased_rsteps (CS := CS) r1 ([e1], (σ1,g1)) (t2, (σ2,g2)) stat →
   e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2 g2);
  recv_adequate_inv t2 σ2 g2 stat :
   erased_rsteps (CS := CS) r1 ([e1], (σ1,g1)) (t2, (σ2,g2)) stat →
   φinv σ2 g2
}.

Lemma recv_adequate_alt {Λ CS} s e1 r1 σ1 g1 (φ φr : val Λ → state Λ → global_state Λ → Prop) φinv :
  recv_adequate (CS := CS) s e1 r1 σ1 g1 φ φr φinv ↔ ∀ t2 σ2 g2 stat,
    erased_rsteps (CS := CS) r1 ([e1], (σ1,g1)) (t2, (σ2,g2)) stat →
      (∀ e2, s = NotStuck → e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2 g2)) ∧
      (∀ v2 t2', t2 = of_val v2 :: t2' →
                 match stat with
                   | Normal => φ v2 σ2 g2
                   | Crashed => φr v2 σ2 g2
                 end) ∧
      (φinv σ2 g2).
Proof.
  split.
  - intros [] ??? []; naive_solver.
  - constructor; naive_solver.
Qed.

Corollary wp_recv_adequacy_inv Σ Λ CS `{!invGpreS Σ} `{!trGpreS Σ} `{!crashGpreS Σ} s e r σ g φ φr φinv ntr:
  (∀ `(Hinv : !invGS Σ) `(Htr : !trGS Σ) `(Hc: !crashGS Σ) κs,
     ⧗ ntr ∗ £ ntr ⊢ |={⊤}=> ∃
         (stateI : state Λ → nat → iProp Σ) (* for the initial generation *)
         (global_stateI : global_state Λ → fracR → coPset → list (observation Λ) → iProp Σ)
         (fork_post : val Λ → iProp Σ)
         Φinv,
        let HI := IrisGS Λ Σ Hinv Htr (global_stateI) (fork_post) in
        let HG := GenerationGS Λ Σ Hc stateI in
       □ (∀ σ nt, stateI σ nt -∗ |NC={⊤, ∅}=> ⌜ φinv σ ⌝) ∗ (* φinv for initial gen. *)
       □ (∀ HG, Φinv Hinv HG -∗ □ ∀ σ nt, state_interp σ nt -∗ |@NC={iris_crashGS, ⊤, ∅}=> ⌜ φinv σ ⌝) ∗ (* φinv for later generations *)
       stateI σ 0 ∗ global_stateI g 1%Qp ∅ κs ∗
       wpr CS s HG ⊤ e r (λ v, ⌜φ v⌝) (Φinv Hinv) (λ _ v, ⌜φr v⌝)) →
  recv_adequate (CS := CS) s e r σ g (λ v _ _, φ v) (λ v _ _, φr v) (λ σ _, φinv σ).
Proof.
  intros Hwp.
  apply recv_adequate_alt.
  intros t2 σ2 g2 stat [n [κs H]]%erased_rsteps_nrsteps.
  (* we apply adequacy twice, for not_stuck and the rest.
     probably we can somehow avoid all this code duplication... *)
  split; last first.
  { destruct (nrsteps_snoc _ _ _ _ _ _ H) as (ns'&n'&->).
  eapply (step_fupdN_fresh_soundness _ ns')
         => Hinv Htr Hc.
  iIntros "H⧗£ HNC".
  iMod (Hwp Hinv Htr Hc κs with "H⧗£") as (stateI global_stateI fork_post Φinv) "(#Hinv1&#Hinv2&Hσ&Hg&H)".
  iModIntro.
  set (HI := IrisGS Λ Σ Hinv Htr (global_stateI) (fork_post)).
  set (HG := GenerationGS Λ Σ Hc stateI).
  iExists HI, HG.
  iDestruct (wptp_recv_strong_adequacy
               (Φinv' := (λ HG, ∀ σ nt, state_interp σ nt -∗ |@NC={iris_crashGS, ⊤, ∅}=> ⌜ φinv σ ⌝)%I)
               (κs' := []) (HG := HG) with "[Hσ] [Hg] [H] [] [] HNC") as "H"; eauto.
  { rewrite app_nil_r. eauto. }
  do 3 iExists eq_refl.
  iModIntro.
  iApply (step_fupdN_fresh_wand with "H").
  iIntros (HG') "H".
  iApply (physical_stepN_wand with "H").
  iMod 1 as (v2 ??) "(Hσ&Hg&Hv&Hfpost&HNC)".
  destruct stat.
  - iDestruct "Hv" as "(Hv&#Hinv)".
    rewrite ?ncfupd_eq /ncfupd_def.
    iMod ("Hinv" with "[$] [$]") as "(%&HNC)".
    iApply fupd2_mask_intro; [done..|]. iIntros.
    iSplit; last done. iIntros (v2' ? Heq). subst. inversion Heq; subst.
    rewrite to_of_val. naive_solver.
  - iDestruct "Hv" as "(->&Hv)".
    rewrite ?ncfupd_eq /ncfupd_def.
    iMod ("Hinv1" with "[$] [$]") as "(Hp&HNC)".
    iApply fupd2_mask_intro; [done..|]. iIntros "_".
    iSplit; last done.
    iIntros (v2' ? Heq). subst. inversion Heq; subst.
    rewrite to_of_val. naive_solver.
  }
  { intros e2 -> He2.
  destruct (nrsteps_snoc _ _ _ _ _ _ H) as (ns'&n'&->).
  eapply (step_fupdN_fresh_soundness _ ns')
         => Hinv Htr Hc.
  iIntros "H⧗£ HNC".
  iMod (Hwp Hinv Htr Hc κs with "H⧗£") as (stateI global_stateI fork_post) "H".
  iDestruct "H" as (Φinv) "(#Hinv1&#Hinv2&Hσ&Hg&H)".
  iModIntro.
  set (HI := IrisGS Λ Σ Hinv Htr (global_stateI) (fork_post)).
  set (HG := GenerationGS Λ Σ Hc stateI).
  iExists HI, HG.
  iDestruct (wptp_recv_progress
               (Φinv' := (λ HG, ∀ σ nt, state_interp σ nt -∗ |@NC={iris_crashGS, ⊤, ∅}=> ⌜ φinv σ ⌝)%I)
               (κs' := []) (HG := HG) with "[Hσ] [Hg] [H] [] [] HNC") as "H"; [eauto..|].
  { rewrite app_nil_r. eauto. }
  do 3 iExists eq_refl. iModIntro.
  iApply (step_fupdN_fresh_wand with "H").
  iIntros (?) "$".
 }
Qed.
