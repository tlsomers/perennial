From iris.algebra Require Import gmap auth agree gset coPset excl csum.
From Perennial.base_logic.lib Require Export fancy_updates.
From stdpp Require Export namespaces.
From Perennial.base_logic.lib Require Import wsat invariants ae_invariants saved_prop.
From Perennial.Helpers Require Import Qextra ipm.
From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Export step_fupd_extra crash_weakestpre ae_invariants_mutable later_res private_invariants staged_invariant_alt.
From iris.prelude Require Import options.

Set Default Proof Using "Type".

#[global]
Existing Instances pri_inv_tok_timeless.

Section def.
Context `{IRISG: !irisGS Λ Σ, !generationGS Λ Σ}.
Context `{!pri_invG IRISG}.
Context `{!later_tokG IRISG}.
Context `{!stagedG Σ}.

Definition staged_value_inuse e E1' E1 mj mj_wp mj_ukeep Φ Φc P :=
  (∃ E2 mj_wp_init mj_ishare mj_ushare γsaved γfinished γstatus γprop γprop',
      ⌜ E1 ⊆ E1' ⌝ ∗
      ⌜ to_val e = None ⌝ ∗
      ⌜ (1 < mj + mj_ukeep)%Qp ⌝ ∗
      ⌜ (mj_ukeep + mj_ushare = /2)%Qp ⌝ ∗
      ⌜ (mj_wp ≤ mj) ⌝%Qp ∗
      ⌜ (mj_wp ≤ / 2 + mj_ishare) ⌝%Qp ∗
      own γsaved (◯ Excl' (γprop, γprop')) ∗
      own γstatus (◯ Excl' (inuse mj_wp mj_ushare)) ∗
      saved_prop_own γprop DfracDiscarded (wpc0 NotStuck mj_wp E1 e
                     (λ v : val Λ, (wpc_crash_modality E1 mj_wp P) ∗ (wpc_crash_modality E1 mj_wp Φc ∧ Φ v))
                     (Φc ∗ P)) ∗
      saved_prop_own γprop' DfracDiscarded Φc ∗
      later_tok ∗
      pri_inv_tok mj_ukeep E2 ∗
      ⌜ /2 < mj ⌝%Qp ∗
      pri_inv E2 (staged_inv_inner E1' E2 mj_wp_init mj_ishare γsaved γfinished γstatus P))%I.

End def.

Section inv.
Context `{IRISG: !irisGS Λ Σ, !generationGS Λ Σ}.
Context `{!pri_invG IRISG}.
Context `{!later_tokG IRISG}.
Context `{!stagedG Σ}.
Implicit Types i : positive.
Implicit Types N : namespace.
Implicit Types P Q R : iProp Σ.

Lemma wpc_staged_inv_aux e E1' mj mj_wp mj_ukeep Φ Φc P :
  staged_value_inuse e E1' ⊤ mj mj_wp mj_ukeep Φ Φc P -∗
  wpc0 NotStuck mj ⊤ e Φ Φc.
Proof using later_tokG0.
  iIntros "Hsv".
  iLöb as "IH" forall (e).
  iDestruct "Hsv" as (E2 ? mj_ishare mj_ushare ????? Hsub)
    "(%Hnval&%Hinvalid&%Heq_mj&%Hle2&%Hinvalid2&Hown&Hownstat&#Hsaved1&#Hsaved2&Htok&Hitok&%Hlt2&#Hinv)".
  iEval (rewrite wpc0_unfold).
  iDestruct (later_tokN_use with "[$]") as "[[[??]_] Hcl]".
  rewrite /wpc_pre. iSplit; last first.
  {
    iIntros (g1 D' κs) "Hg #HC".
    iDestruct (pri_inv_tok_disj with "[$]") as %[Hdisj|Hval]; last first.
    { exfalso. apply Qp.lt_nge in Hinvalid. revert Hval. rewrite frac_valid. eauto. }
    iMod (pri_inv_acc with "[$]") as "(Hinner&Hclo)".
    { set_solver. }
    iEval (rewrite staged_inv_inner_unfold) in "Hinner".
    iDestruct "Hinner" as (γprop_stored ????) "(>Hown'&#Hsaved1'&#Hsaved2'&>Hstatus'&>Hitok_ishare&Hinner)".
    iDestruct (own_valid_2 with "Hown' Hown") as "#H".
    iDestruct "H" as %[Heq%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
    iDestruct (own_valid_2 with "Hstatus' Hownstat") as "#Heq_status".
    iDestruct "Heq_status" as %[Heq_status%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
    inversion Heq; subst.
    iDestruct (saved_prop_agree with "Hsaved1 Hsaved1'") as "Hequiv1".
    iDestruct (saved_prop_agree with "Hsaved2 Hsaved2'") as "Hequiv2".
    iEval (simpl).
    iApply fupd2_trans. iApply (fupd_fupd2 ⊤ ⊤).
    iApply (lc_fupd_add_later with "[$]"). iNext.
    iApply (lc_fupd_add_later with "[$]"). iNext. iModIntro.
    iDestruct "Hinner" as "[(%Hlt''&HPs&Hs)|Hfin]"; last first.
    {
      iDestruct "Hfin" as "(HPR&Hrest)".
      iMod (saved_prop_alloc True%I) as (γprop_remainder') "#Hsaved2''".
      { apply dfrac_valid_discarded. }
      iMod (own_update_2 _ _ _ (● Excl' (γprop_stored, γprop_remainder') ⋅
                                  ◯ Excl' (γprop_stored, γprop_remainder'))
              with "Hown' Hown") as "[Hown' Hown]".
      { by apply auth_update, option_local_update, exclusive_local_update. }
      iMod ("Hclo" with "[-Hg HPR]").
      { iNext. iEval (rewrite staged_inv_inner_unfold). iExists _, _, _, _, _. iFrame "∗ #". }
      iRewrite "Hequiv2". by iFrame.
    }
    iDestruct "Hs" as "(Hitok'&#Hwand)".
    iDestruct (pri_inv_tok_join with "Hitok Hitok'") as "Hitok".
    rewrite Heq_mj.
    iDestruct (pri_inv_tok_join with "Hitok Hitok_ishare") as "Hitok".
    iDestruct (pri_inv_tok_global_le_acc _ _ mj_wp with "[] Hg") as "(Hg_inv&Hg_inv_clo)".
    { iPureIntro; split; naive_solver. }
    iDestruct (pri_inv_tok_le_acc mj_wp with "Hitok") as "(Hitok_wp&Hitok_inv_clo)".
    { naive_solver. }
    iMod (pri_inv_tok_disable_reenable with "[$]") as "(Hg&Hreenable)".
    iRewrite -"Hequiv1" in "HPs".
    iEval (rewrite wpc0_unfold /wpc_pre) in "HPs".
    iDestruct "HPs" as "(_&HPs)".

    rewrite /wpc_crash_modality.
    replace (⊤ ∖ D' ∖ E2) with (⊤ ∖ (E2 ∪ D')) by set_solver.
    (* iDestruct (lc_weaken with "Hlc") as "Hlc". *)
    (* { apply (num_laters_per_step_exp ns'). lia. } *)
    (* iDestruct "Hlc" as "[[Hlc1 Hlc2] Hlc3]". *)
    iSpecialize ("HPs" with "[$] [$]").
    iMod "HPs" as "(Hg&HPr&HP)".
    iMod ("Hreenable" with "[$Hg]") as "(Hitok&Hg)".
    iDestruct ("Hitok_inv_clo" with "[$]") as "Hitok".
    iDestruct (pri_inv_tok_split with "Hitok") as "(Hitok&Hitok_ishare)".
    rewrite -Heq_mj.
    iDestruct (pri_inv_tok_split with "Hitok") as "(Hitok_ukeep&Hitok_ushare)".
    iMod (saved_prop_alloc True%I) as (γprop_remainder') "#Hsaved2''".
    { apply dfrac_valid_discarded. }
    iMod (own_update_2 _ _ _ (● Excl' (γprop_stored, γprop_remainder') ⋅
                                ◯ Excl' (γprop_stored, γprop_remainder'))
            with "Hown' Hown") as "[Hown' Hown]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    iDestruct ("Hg_inv_clo" with "[$]") as "Hg".

    iMod ("Hclo" with "[-HPr Hg]").
    { iNext. iEval (rewrite staged_inv_inner_unfold). iExists _, _, _, _, _. iFrame "∗ #". iRight. iFrame. }
    by iFrame.
  }
  {
    rewrite Hnval.
    iIntros (q σ1 g1 D κ κs nt) "Hσ Hg HNC".
    iDestruct (pri_inv_tok_disj with "[$]") as %[Hdisj|Hval]; last first.
    { exfalso. apply Qp.lt_nge in Hinvalid. revert Hval. rewrite frac_valid. eauto. }
    iMod (pri_inv_acc with "[$]") as "(Hinner&Hclo)".
    { set_solver. }
    iEval (rewrite staged_inv_inner_unfold) in "Hinner".

    iAssert (|={⊤}=> _ ∧ _)%I with "[-]" as ">$".
    iDestruct "Hinner" as (?????) "(>Hown'&#Hsaved1'&#Hsaved2'&>Hstatus'&>Hitok_ishare&Hinner)".
    iDestruct (own_valid_2 with "Hown' Hown") as "#H".
    iDestruct "H" as %[Heq%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
    iDestruct (own_valid_2 with "Hstatus' Hownstat") as "#Heq_status".
    iDestruct "Heq_status" as %[Heq_status%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
    inversion Heq; subst.

    iDestruct (saved_prop_agree with "Hsaved1 Hsaved1'") as "Hequiv1".
    iDestruct (saved_prop_agree with "Hsaved2 Hsaved2'") as "Hequiv2".

    iEval (simpl).
    
    iApply (lc_fupd_add_later with "[$]"); iModIntro.
    iApply (lc_fupd_add_later with "[$]"); iModIntro.

    iDestruct "Hinner" as "[(%Hlt''&HPs&Hs)|Hfin]"; last first.
    {
      iDestruct "Hfin" as "(HPR&HC&Hrest)".
      iDestruct (NC_C with "[$] [$]") as %[].
    }
    iDestruct "Hs" as "(Hitok'&#Hwand)".
    iDestruct (pri_inv_tok_join with "Hitok Hitok'") as "Hitok".
    rewrite Heq_mj.
    iDestruct (pri_inv_tok_join with "Hitok Hitok_ishare") as "Hitok".
    iDestruct (pri_inv_tok_global_le_acc _ _ mj_wp with "[] Hg") as "(Hg_inv&Hg_inv_clo)".
    { iPureIntro; split; naive_solver. }
    iDestruct (pri_inv_tok_le_acc mj_wp with "Hitok") as "(Hitok_wp&Hitok_inv_clo)".
    { naive_solver. }
    iMod (pri_inv_tok_disable_reenable with "[$]") as "(Hg&Hreenable)".
    iRewrite -"Hequiv1" in "HPs".
    iEval (rewrite wpc0_unfold /wpc_pre) in "HPs".
    iDestruct "HPs" as "(Hwp&_)".
    rewrite Hnval.
    replace (⊤ ∖ D ∖ E2) with (⊤ ∖ (E2 ∪ D)) by set_solver.
    iDestruct ("Hwp" with "[$] [$] [$]") as "Hwp".
    iModIntro. iSplit; [by iLeft in "Hwp"|iRight in "Hwp"].
    iIntros (e2 ????).
    iMod "Hcl" as "_".
    iApply (physical_step_wand with "(Hwp [//])").
    iIntros "($&Hg&H&Hefs&HNC) [[Htok _]_]".
    destruct (to_val e2) eqn:Heq_val.
    {
      iEval (rewrite wpc0_unfold /wpc_pre) in "H".
      iDestruct "H" as "(H&_)".
      rewrite Heq_val.
      iMod ("H" with "[$] [$]") as "H".
      iDestruct "H" as "((Hcm&Hv)&Hg&HNC)".
      iMod (saved_prop_alloc (wpc_crash_modality ⊤ mj_wp P)) as (γprop_stored') "#Hsaved1''".
      { apply dfrac_valid_discarded. }
      iMod (saved_prop_alloc True%I) as (γprop_remainder') "#Hsaved2''".
      { apply dfrac_valid_discarded. }
      iMod (own_update_2 _ _ _ (● Excl' (γprop_stored', γprop_remainder') ⋅
                                ◯ Excl' (γprop_stored', γprop_remainder'))
              with "Hown' Hown") as "[Hown' Hown]".
      { by apply auth_update, option_local_update, exclusive_local_update. }
      iMod ("Hreenable" with "[$Hg]") as "(Hitok&Hg)".
      iDestruct ("Hitok_inv_clo" with "[$]") as "Hitok".
      iDestruct (pri_inv_tok_split with "[$Hitok]") as "(Hitok&Hitok_ishare)".
      iEval (rewrite -Heq_mj) in "Hitok".
      iDestruct (pri_inv_tok_split with "[$Hitok]") as "(Hitok_ukeep&Hitok_ushare)".
      iMod ("Hclo" with "[Hown' Hstatus' Hcm Hitok_ishare Hitok_ushare]").
      { iNext.
        iEval (rewrite staged_inv_inner_unfold).
        iExists _, _, _, _, _. iFrame "∗ #".
        iLeft.
        iSplit.
        { iPureIntro. split_and!; auto; try naive_solver. }
        iFrame.
        iModIntro. iIntros "Hwpc".
        assert (E1' = ⊤) as -> by set_solver.
        rewrite /wpc_crash_modality.
        iIntros (???) "Hg HC".
        by iMod ("Hwpc" with "[$] [$]") as "($&$)".
      }
      iDestruct ("Hg_inv_clo" with "Hg") as "Hg".
      iModIntro. iFrame.
      iSplitR "Hefs".
      - iEval (rewrite wpc0_unfold /wpc_pre).
        rewrite Heq_val.
        iSplit.
        * iIntros. iModIntro. iFrame. iDestruct "Hv" as "(_&$)".
        * iDestruct "Hv" as "(H&_)". iIntros.
          iDestruct (pri_inv_tok_global_le_acc _ _ mj_wp with "[] [$]") as "(Hg&Hg_clo)".
          { iPureIntro; naive_solver. }
          iSpecialize ("H" with "[$] [$]").
          iMod "H" as "(Hg&$)".
          iApply "Hg_clo". by iFrame.
      - iApply (big_sepL_mono with "Hefs").
        iIntros. iApply (wpc0_mj_le); last by iFrame.
        split; auto. naive_solver.
    }
    iFrame "HNC".
    iMod (saved_prop_alloc
            (wpc0 NotStuck mj_wp ⊤ e2
              (λ v : val Λ, wpc_crash_modality ⊤ mj_wp P ∗ (wpc_crash_modality ⊤ mj_wp Φc ∧ Φ v))
              (Φc ∗ P))%I) as (γprop_stored') "#Hsaved1''".
    { apply dfrac_valid_discarded. }
    iMod (saved_prop_alloc Φc) as (γprop_remainder') "#Hsaved2''".
    { apply dfrac_valid_discarded. }
    iMod (own_update_2 _ _ _ (● Excl' (γprop_stored', γprop_remainder') ⋅
                              ◯ Excl' (γprop_stored', γprop_remainder'))
            with "Hown' Hown") as "[Hown' Hown]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    iMod (own_update_2 _ _ _ (● Excl' (inuse mj_wp mj_ushare) ⋅ ◯ Excl' (inuse mj_wp mj_ushare))
            with "Hstatus' Hownstat") as "[Hstatus' Hownstat]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    iMod ("Hreenable" with "[$Hg]") as "(Hitok&Hg)".
    iDestruct ("Hitok_inv_clo" with "[$]") as "Hitok".
    iDestruct (pri_inv_tok_split with "[$Hitok]") as "(Hitok&Hitok_ishare)".
    iEval (rewrite -Heq_mj) in "Hitok".
    iDestruct (pri_inv_tok_split with "[$Hitok]") as "(Hitok_ukeep&Hitok_ushare)".
    iMod ("Hclo" with "[Hown' Hstatus' H Hitok_ishare Hitok_ushare]").
    { iNext.
      iEval (rewrite staged_inv_inner_unfold).
      iExists _, _, _, _, _. iFrame "∗ #".
      iLeft.
      iSplit.
      { iPureIntro. split_and!; auto; try naive_solver. }
      iFrame.
      iModIntro. iIntros "Hwpc".
      iEval (rewrite wpc0_unfold) in "Hwpc". iDestruct "Hwpc" as "(_&Hwpc)".
      rewrite /wpc_crash_modality.
      iIntros (???) "Hg HC".
      iSpecialize ("Hwpc" with "[$] [$]").
      by replace E1' with (⊤ : coPset) by set_solver.
    }
    iDestruct ("Hg_inv_clo" with "Hg") as "$".
    iModIntro. iSplitR "Hefs"; last first.
    { iApply (big_sepL_mono with "Hefs").
      iIntros. iApply (wpc0_mj_le); last by iFrame.
      split; auto. naive_solver.
    }
    iApply "IH".
    iExists _, _, mj_ishare, _, _, _, _, _. iExists _. iFrame "∗".
    repeat iSplit; eauto.
  }
Qed.

Lemma wpc_staged_inv_inuse E1 e Φ Φc Qs P :
  to_val e = None →
  staged_value ⊤ Qs P ∗
  ((∀ mj_wp, wpc_crash_modality E1 mj_wp Φc) ∧
   (Qs -∗ ∀ mj_wp, ⌜ (/2 < mj_wp)%Qp ⌝ → WPC e @ E1
                                 {{λ v, wpc_crash_modality ⊤ mj_wp P ∗ (wpc_crash_modality E1 mj_wp Φc ∧ Φ v)}}
                                 {{ Φc ∗ P }}))
  ⊢ WPC e @ E1 {{ Φ }} {{ Φc }}.
Proof using later_tokG0.
  iIntros (Hnval) "(Hstaged&Hwp)".
  iDestruct "Hstaged" as (E2 ??? γprop γprop') "(Hown&Hownstat&#Hsaved1&#Hsaved2&Htok&Hitok&Hinv)".
  iDestruct "Hinv" as (mj_wp_init mj_ishare Hlt) "#Hinv".
  rewrite /staged_inv.
  rewrite wpc_eq /wpc_def. iIntros (mj).

  iLöb as "IH" forall (γprop γprop' Qs) "Hsaved1 Hsaved2".

  (* Base case *)
  iEval (rewrite wpc0_unfold).
  rewrite /wpc_pre. iSplit; last first.
  {
    iDestruct "Hwp" as "(Hwp&_)".
    iIntros (g1 D' κs) "Hg #HC".
    by iSpecialize ("Hwp" $! mj with "[$] [$]").
  }
  rewrite Hnval.
  iIntros (q σ1 g1 D κ κs nt) "Hσ Hg HNC".
  iDestruct (pri_inv_tok_disj_inv_half with "[$]") as %Hdisj.
  iMod (pri_inv_acc with "[$]") as "(Hinner&Hclo)".
  { set_solver. }
  iEval (rewrite staged_inv_inner_unfold) in "Hinner".

  iAssert (|={E1}=> _ ∧ _)%I with "[-]" as ">$".

  iDestruct "Hinner" as (?????) "(>Hown'&#Hsaved1'&#Hsaved2'&>Hstatus'&>Hitok_ishare&Hinner)".
  iDestruct (own_valid_2 with "Hown' Hown") as "#H".
  iDestruct "H" as %[Heq%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  iDestruct (own_valid_2 with "Hstatus' Hownstat") as "#Heq_status".
  iDestruct "Heq_status" as %[Heq_status%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  inversion Heq; subst.
  iDestruct (saved_prop_agree with "Hsaved1 Hsaved1'") as "Hequiv1".
  iDestruct (saved_prop_agree with "Hsaved2 Hsaved2'") as "Hequiv2".
  iDestruct (later_tokN_use with "Htok") as "[[[??]_] Hcl]".

  iApply (lc_fupd_add_later with "[$]"); iModIntro.
  iApply (lc_fupd_add_later with "[$]"); iModIntro.

  iDestruct "Hinner" as "[(HPs&_)|Hfin]"; last first.
  { (* Impossible, since we have NC token. *)
    iDestruct "Hfin" as "(_&HC&_)". iDestruct (NC_C with "[$] [$]") as %[]. }
  iRewrite -"Hequiv1" in "HPs".
  iDestruct "Hwp" as "(_&Hwp)".
  iSpecialize ("Hwp" with "[$]").

  iDestruct (pri_inv_tok_global_valid with "Hg") as %(Hmin&Hvalid).
  destruct (Qp_plus_inv_2_gt_1_split mj) as (mj_ukeep&mj_ushare&Heq_mj&Hinvalid); first auto.
  set (mj_wp := (mj_wp_init `min` mj `min` (/2 + mj_ishare) `min` (/2 + mj_ushare))%Qp).
  assert (/ 2 < mj_wp)%Qp.
  {
    - rewrite /mj_wp. apply Qp_min_glb1_lt; auto.
      * apply Qp_min_glb1_lt; auto.
        ** apply Qp_min_glb1_lt; auto.
        ** apply Qp.lt_add_l.
      * apply Qp.lt_add_l.
  }
  iDestruct (pri_inv_tok_global_le_acc _ _ mj_wp with "[] Hg") as "(Hg_inv&Hg_inv_clo)".
  { iPureIntro; split; auto.
    rewrite /mj_wp.
    etransitivity; first eapply Qp.le_min_l.
    etransitivity; first eapply Qp.le_min_l.
    apply Qp.le_min_r.
  }

  iDestruct (pri_inv_tok_join with "[$Hitok] [$]") as "Hitok".
  iDestruct (pri_inv_tok_le_acc mj_wp with "Hitok") as "(Hitok_wp&Hitok_inv_clo)".
  { rewrite /mj_wp.
    etransitivity; first eapply Qp.le_min_l.
    apply Qp.le_min_r. }


  iMod (pri_inv_tok_disable_reenable with "[$]") as "(Hg&Hreenable)".
  unshelve (iSpecialize ("Hwp" $! mj_wp _ mj_wp)).
  { rewrite //=. }
  iEval (rewrite wpc0_unfold) in "Hwp".
  iDestruct "Hwp" as "(Hwp&_)".
  rewrite Hnval.
  replace (⊤ ∖ D ∖ E2) with (⊤ ∖ (E2 ∪ D)) by set_solver.
  iDestruct ("Hwp" with "[$] [$] [$]") as "Hwp".
  iModIntro. iSplit; [by iLeft in "Hwp"|iRight in "Hwp"].
  iIntros (e2 σ2 g2 efs Hstep).
  iMod "Hcl" as "_".
  iApply (physical_step_wand with "(Hwp [//])").
  iIntros "($&Hg&H&Hefs&HNC) [[Htok _] _]".

  destruct (to_val e2) eqn:Heq_val.
  {
    iEval (rewrite wpc0_unfold /wpc_pre) in "H".
    iDestruct "H" as "(H&_)".
    rewrite Heq_val.
    iMod ("H" with "[$] [$]") as "H".

      iDestruct "H" as "((Hcm&Hv)&Hg&HNC)".
      iMod (saved_prop_alloc (wpc_crash_modality ⊤ mj_wp P)) as (γprop_stored') "#Hsaved1''".
      { apply dfrac_valid_discarded. }
      iMod (saved_prop_alloc True%I) as (γprop_remainder') "#Hsaved2''".
      { apply dfrac_valid_discarded. }
      iMod (own_update_2 _ _ _ (● Excl' (γprop_stored', γprop_remainder') ⋅
                                ◯ Excl' (γprop_stored', γprop_remainder'))
              with "Hown' Hown") as "[Hown' Hown]".
      { by apply auth_update, option_local_update, exclusive_local_update. }
      iMod (own_update_2 _ _ _ (● Excl' (inuse mj_wp mj_ushare) ⋅ ◯ Excl' (inuse mj_wp mj_ushare))
              with "Hstatus' Hownstat") as "[Hstatus' Hownstat]".
      { by apply auth_update, option_local_update, exclusive_local_update. }
      iMod ("Hreenable" with "[$Hg]") as "(Hitok&Hg)".
      iDestruct ("Hitok_inv_clo" with "[$]") as "Hitok".
      iDestruct (pri_inv_tok_split with "[$Hitok]") as "(Hitok&Hitok_ishare)".
      iEval (rewrite -Heq_mj) in "Hitok".
      iDestruct (pri_inv_tok_split with "[$Hitok]") as "(Hitok_ukeep&Hitok_ushare)".
      iMod ("Hclo" with "[Hown' Hstatus' Hcm Hitok_ishare Hitok_ushare]").
      { iNext.
        iEval (rewrite staged_inv_inner_unfold).
        iExists _, _, _, _, _. iFrame "∗ #".
        iLeft.
        iSplit.
        { iPureIntro. split_and!; auto; try naive_solver.
          - etransitivity; first eapply Qp.le_min_r. reflexivity.
          - etransitivity; first eapply Qp.le_min_l.
            etransitivity; first eapply Qp.le_min_l.
            eapply Qp.le_min_l. }
        iFrame.
        iModIntro. iIntros "Hwpc".
        rewrite /wpc_crash_modality.
        iIntros (???) "Hg HC".
        by iMod ("Hwpc" with "[$] [$]") as "[$ $]".
      }
      iDestruct ("Hg_inv_clo" with "Hg") as "Hg".
      iModIntro. iFrame.
      iSplitR "Hefs".
      - iEval (rewrite wpc0_unfold /wpc_pre).
        rewrite Heq_val.
        iSplit.
        * iIntros. iModIntro. iFrame. iDestruct "Hv" as "(_&$)".
        * iDestruct "Hv" as "(H&_)". iIntros.
          iDestruct (pri_inv_tok_global_le_acc _ _ mj_wp with "[] [$]") as "(Hg&Hg_clo)".
          { iPureIntro; split; auto.
            etransitivity; first eapply Qp.le_min_l.
            etransitivity; first eapply Qp.le_min_l.
            eapply Qp.le_min_r. }
          iMod ("H" with "[$] [$]") as "(Hg&$)".
          iApply "Hg_clo". by iFrame.
      - iApply (big_sepL_mono with "Hefs").
        iIntros. iApply (wpc0_mj_le); last by iFrame.
        split; auto.
        etransitivity; first eapply Qp.le_min_l.
        etransitivity; first eapply Qp.le_min_l.
        eapply Qp.le_min_r. }

  iFrame "HNC".
  iMod (saved_prop_alloc
          (wpc0 NotStuck mj_wp ⊤ e2
            (λ v : val Λ, wpc_crash_modality ⊤ mj_wp P ∗ (wpc_crash_modality ⊤ mj_wp Φc ∧ Φ v))
            (Φc ∗ P))%I) as (γprop_stored') "#Hsaved1''".
  { apply dfrac_valid_discarded. }
  iMod (saved_prop_alloc Φc) as (γprop_remainder') "#Hsaved2''".
  { apply dfrac_valid_discarded. }
  iMod (own_update_2 _ _ _ (● Excl' (γprop_stored', γprop_remainder') ⋅
                            ◯ Excl' (γprop_stored', γprop_remainder'))
          with "Hown' Hown") as "[Hown' Hown]".
  { by apply auth_update, option_local_update, exclusive_local_update. }
  iMod (own_update_2 _ _ _ (● Excl' (inuse mj_wp mj_ushare) ⋅ ◯ Excl' (inuse mj_wp mj_ushare))
          with "Hstatus' Hownstat") as "[Hstatus' Hownstat]".
  { by apply auth_update, option_local_update, exclusive_local_update. }
  iMod ("Hreenable" with "[$Hg //]") as "(Hitok&Hg)".
  iDestruct ("Hitok_inv_clo" with "[$]") as "Hitok".
  iDestruct (pri_inv_tok_split with "[$Hitok]") as "(Hitok&Hitok_ishare)".
  iEval (rewrite -Heq_mj) in "Hitok".
  iDestruct (pri_inv_tok_split with "[$Hitok]") as "(Hitok_ukeep&Hitok_ushare)".
  iMod ("Hclo" with "[Hown' Hstatus' H Hitok_ishare Hitok_ushare]").
  { iNext.
    iEval (rewrite staged_inv_inner_unfold).
    iExists _, _, _, _, _. iFrame "∗ #".
    iLeft.
    iSplit.
    { iPureIntro. split_and!; auto.
      - rewrite /mj_wp. apply Qp.le_min_r.
      - rewrite /mj_wp.
        etransitivity; first eapply Qp.le_min_l.
        etransitivity; first eapply Qp.le_min_l.
        eapply Qp.le_min_l.
    }
    iSplitL "H".
    { iApply (wpc0_strong_mono with "H"); auto.
      iSplit; last by (iIntros; iModIntro; iFrame).
      iIntros (?) "($&H)". iModIntro.
      iSplit.
      - iDestruct "H" as "(H&_)". iApply (wpc_crash_modality_strong_wand with "[$]"); auto.
      - iDestruct "H" as "(_&$)".
    }
    iFrame.
    iModIntro. iIntros "Hwpc".
    iEval (rewrite wpc0_unfold) in "Hwpc". iDestruct "Hwpc" as "(_&Hwpc)".
    rewrite /wpc_crash_modality.
    iIntros (???) "Hg HC".
    by iSpecialize ("Hwpc" with "[$] [$]").
  }
  iDestruct ("Hg_inv_clo" with "Hg") as "$".
  iModIntro. iSplitR "Hefs"; last first.
  { iApply (big_sepL_mono with "Hefs").
    iIntros. iApply (wpc0_mj_le); last by iFrame.
    split; auto.
      - rewrite /mj_wp.
        etransitivity; first eapply Qp.le_min_l.
        etransitivity; first eapply Qp.le_min_l.
        eapply Qp.le_min_r.
  }
  iAssert (staged_value_inuse e2 ⊤ ⊤ mj mj_wp mj_ukeep Φ Φc P) with "[-]" as "Hsv".
  {
    iExists _, _, mj_ishare, _, _, _, _, _. iExists _. iFrame "∗".
    repeat iSplit; eauto.
    { iPureIntro. rewrite /mj_wp.
      etransitivity; first eapply Qp.le_min_l.
      etransitivity; first eapply Qp.le_min_l.
      eapply Qp.le_min_r. }
    { iPureIntro. rewrite /mj_wp.
      etransitivity; first eapply Qp.le_min_l.
      eapply Qp.le_min_r. }
  }
  iApply (wpc_staged_inv_aux with "[$]").
Qed.

End inv.
