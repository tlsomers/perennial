From Perennial.base_logic Require Import ghost_map saved_prop mono_nat.
From Perennial.program_proof Require std_proof.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.txn Require Import txn_repr.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_getTimestamp (sid : u64) γ :
    uint.Z sid < zN_TXN_SITES →
    ⊢ have_gentid γ -∗
    {{{ own_sid γ sid }}}
    <<< ∀∀ (ts : nat), own_largest_ts γ ts >>>
      getTimestamp #sid @ ↑tsNS
    <<< ∃∃ (ts' : nat), own_largest_ts γ ts' ∗ ⌜(ts < ts')%nat⌝ >>>
    {{{ (tid : u64), RET #tid; ⌜uint.nat tid = ts'⌝ ∗ own_sid γ sid }}}.
  Proof.
  iIntros "%Hsid #Hinv !>" (Φ) "Hsid HAU".
    wp_rec.
    rewrite /trusted_time.GetTime.
    wp_pure_credit "LC".

    (*@ func getTimestamp(sid uint64) uint64 {                                  @*)
    (*@     ts := trusted_time.GetTime()                                        @*)
    wp_apply (wp_GetTSC).
    iInv "Hinv" as "Hgentid" "Hclose".
    iMod (lc_fupd_elim_later with "LC Hgentid") as (clock) "Hgentid".
    iMod (gentid_reserve with "Hgentid Hsid HAU") as "[Hclock Hcont]".
    iApply ncfupd_mask_intro.
    { solve_ndisj. }
    iIntros "Hclose2".
    iExists _. iFrame "Hclock".
    iIntros (clock2) "[%Hclock Hclock2]".
    iMod "Hclose2" as "_".
    set inbounds := bool_decide (uint.Z clock2 + 64 < 2^64).
    set clock2_boundsafe := if inbounds then clock2 else 0.
    opose proof (u64_round_up_spec clock2_boundsafe (W64 64) _ _) as H.
    { subst clock2_boundsafe inbounds. case_bool_decide; word. }
    { word. }
    move:H.
    set rounded_ts := u64_round_up clock2_boundsafe (W64 64).
    intros (Hmod & Hbound1 & Hbound2).
    set reserved_ts := word.add rounded_ts sid.
    assert ((uint.Z rounded_ts + uint.Z sid) `mod` 64 = uint.Z sid) as Hsidmod.
    { rewrite Z.add_mod. 2:lia.
      rewrite Hmod. rewrite [uint.Z sid `mod` _]Z.mod_small. 2:split;[word|done].
      rewrite Z.mod_small. 1:lia. split;[word|done]. }
    assert (uint.Z (sid_of reserved_ts) = uint.Z sid) as Hsid_of.
    { rewrite /sid_of /reserved_ts.
      rewrite word.unsigned_modu. 2:done.
      rewrite word.unsigned_add. rewrite (wrap_small (_+_)). 2:word.
      rewrite wrap_small. 1:done.
      split.
      - apply Z_mod_nonneg_nonneg. all:try word. all:done.
      - trans (uint.Z zN_TXN_SITES). 2:done. apply Z.mod_pos_bound. done.
    }
    iMod ("Hcont" $! reserved_ts with "[]") as "[Hreserved Hgentid]".
    { iPureIntro. rewrite /sid_of /reserved_ts. apply word.unsigned_inj. done. }
    iMod ("Hclose" with "[Hgentid]") as "_".
    { eauto. }
    iIntros "!> _".

    (*@     n := params.N_TXN_SITES                                             @*)
    wp_pures.

    (*@     tid := std.SumAssumeNoOverflow(ts, n) / n * n + sid                 @*)

    wp_pures.
    wp_apply std_proof.wp_SumAssumeNoOverflow. iIntros (Hoverflow).
    assert (inbounds = true) as ->.
    { subst inbounds. rewrite bool_decide_true; first done. word. }
    subst clock2_boundsafe.
    rewrite u64_Z_through_nat in Hclock.
    rewrite bool_decide_true.
    2:{ subst reserved_ts. word. }
    iDestruct "Hreserved" as (γr) "Hreserved".
    wp_pures.

    set tid := (word.add _ _).
    assert (tid = reserved_ts) as -> by done.
    (*@                                                                         @*)
    (*@                                                                         @*)
    (*@     for trusted_time.GetTime() <= tid {                                 @*)
    (*@     }                                                                   @*)

    set P := λ (b : bool), (if b then True else tsc_lb (uint.nat reserved_ts))%I.
    wp_apply (wp_forBreak_cond P with "[] []").
    { clear Φ. iIntros "!> %Φ _ HΦ".
      wp_apply (wp_GetTSC).
      iMod tsc_lb_0 as "Htsc".
      iApply ncfupd_mask_intro.
      { solve_ndisj. }
      iIntros "Hclose".
      iExists _. iFrame "Htsc".
      iIntros (new_time) "[%Htime Htsc]". iMod "Hclose" as "_".
      iIntros "!> _". wp_pures.
      case_bool_decide; wp_pures; iApply "HΦ"; unfold P.
      - done.
      - iApply tsc_lb_weaken; last done. lia.
    }
    { unfold P. auto. }
    iIntros "Htsc". unfold P. clear P.

    wp_pure_credit "LC1". wp_pure_credit "LC2".
    iInv "Hinv" as "Hgentid" "Hclose".
    iMod (lc_fupd_elim_later with "LC1 Hgentid") as (clock3) "Hgentid".
    iMod (gentid_completed with "LC2 Hgentid Hreserved Htsc") as (clock4) "(Hgentid & HΦ)".
    iMod ("Hclose" with "[Hgentid]") as "_".
    { eauto. }
    iModIntro.

      (*@                                                                         @*)
      (*@     return tid                                                          @*)
      (*@ }                                                                       @*)

    iApply "HΦ".
  Qed.

  Theorem wp_Txn__begin (txn : loc) γ :
    ⊢ {{{ own_txn_uninit txn γ }}}
      <<< ∀∀ (ts : nat), own_largest_ts γ ts >>>
        Txn__begin #txn @ ↑tsNS
      <<< ∃∃ (ts' : nat), own_largest_ts γ ts' ∗ ⌜(ts < ts')%nat⌝ >>>
      {{{ RET #(); own_txn_init txn ts' γ }}}.
  Proof.
    iIntros (Φ) "!> Htxn HAU".
    wp_rec.

    (*@ func (txn *Txn) begin() {                                               @*)
    (*@     txn.ts = getTimestamp(txn.sid)                                      @*)
    (*@                                                                         @*)
    do 2 iNamed "Htxn". iNamed "Hsid".
    wp_loadField.
    wp_apply (wp_getTimestamp with "[] Hsid_own").
    { auto. }
    { admit. }
    iNamed "Hts".

    iMod "HAU" as (ts) "[Hts HAU]".
    iFrame "Hts".
    iIntros "!>" (ts') "[Hts %Hts]".
    iMod ("HAU" with "[$Hts]") as "HΦ"; first done.
    iModIntro.
    iIntros (tidW) "(%Htidw&Hown)".
    wp_storeField.
    iApply "HΦ".
    iAssert (own_txn_ts txn ts')%I with "[$HtsW]" as "Hts"; first done.
    iFrame "∗ #".
    iPureIntro.
    rewrite /valid_ts. word.
  Admitted.

End program.
