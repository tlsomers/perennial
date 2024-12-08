From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.goose_lang.trusted.github_com.mit_pdos.tulip Require Import trusted_proph.

Section proph.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Lemma wp_ResolveRead p (tid : u64) (key : string) (ts : nat) :
    ⊢
    {{{ ⌜uint.nat tid = ts⌝ }}}
    <<< ∀∀ acs, own_txn_proph p acs >>>
      ResolveRead #p #tid #(LitString key) @ ∅
    <<< ∃ acs', ⌜acs = ActRead ts key :: acs'⌝ ∗ own_txn_proph p acs' >>>
    {{{ RET #(); True }}}.
  Proof.
    iIntros "!> %Φ %Hts AU". wp_rec. wp_pures.
    replace (⊤ ∖ ∅) with (⊤ : coPset) by set_solver.
    iMod "AU" as (acs) "[(%pvs & %Hpvs & Hp) Hclose]".
    wp_apply (wp_resolve_proph with "Hp").
    iIntros (pvs') "[-> Hp]". simpl in Hpvs.
    rewrite bool_decide_true in Hpvs; last done.
    simpl in Hpvs.
    iMod ("Hclose" with "[Hp]") as "HΦ".
    { iExists (decode_actions pvs').
      rewrite Hts in Hpvs. iSplit; first done.
      iExists _. by iFrame. }
    iModIntro. by iApply "HΦ".
  Qed.

  Lemma wp_ResolveAbort p (tid : u64) (ts : nat) :
    ⊢
    {{{ ⌜uint.nat tid = ts⌝ }}}
    <<< ∀∀ acs, own_txn_proph p acs >>>
      ResolveAbort #p #tid @ ∅
    <<< ∃ acs', ⌜acs = ActAbort ts :: acs'⌝ ∗ own_txn_proph p acs' >>>
    {{{ RET #(); True }}}.
  Proof.
    iIntros "!> %Φ %Hts AU". wp_rec. wp_pures.
    replace (⊤ ∖ ∅) with (⊤ : coPset) by set_solver.
    iMod "AU" as (acs) "[(%pvs & %Hpvs & Hp) Hclose]".
    wp_apply (wp_resolve_proph with "Hp").
    iIntros (pvs') "[-> Hp]". simpl in Hpvs.
    rewrite bool_decide_false in Hpvs; last done.
    rewrite bool_decide_true in Hpvs; last done.
    simpl in Hpvs.
    iMod ("Hclose" with "[Hp]") as "HΦ".
    { iExists (decode_actions pvs').
      rewrite Hts in Hpvs. iSplit; first done.
      iExists _. by iFrame. }
    iModIntro. by iApply "HΦ".
  Qed.

  Lemma wp_ResolveCommit
    p (tid : u64) (ts : nat) (wrsP : loc) q (wrs : dbmap) :
    ⊢
    {{{ ⌜uint.nat tid = ts⌝ ∗ own_map wrsP q wrs }}}
    <<< ∀∀ acs, own_txn_proph p acs >>>
      ResolveCommit #p #tid #wrsP @ ∅
    <<< ∃ acs', ⌜acs = ActCommit ts wrs :: acs'⌝ ∗ own_txn_proph p acs' >>>
    {{{ RET #(); own_map wrsP q wrs }}}.
  Proof.
    iIntros "!> %Φ [%Hts Hm] AU". wp_rec. wp_pures.
    replace (⊤ ∖ ∅) with (⊤ : coPset) by set_solver.
    wp_rec.
    rewrite /own_map /map.own_map.
    iDestruct "Hm" as (mv ?) "Hmref".
    wp_untyped_load. wp_pures.
    iMod "AU" as (acs) "[(%pvs & %Hpvs & Hp) Hclose]".
    wp_apply (wp_resolve_proph with "Hp").
    iIntros (pvs') "[-> Hp]". simpl in Hpvs.
    rewrite bool_decide_false in Hpvs; last done.
    rewrite bool_decide_false in Hpvs; last done.
    rewrite bool_decide_true in Hpvs; last done.
    simpl in Hpvs.
    iMod ("Hclose" with "[Hp]") as "HΦ".
    { iExists (decode_actions pvs').
      rewrite Hts in Hpvs.
      iSplit.
      { admit. (* todo: bad definition of decode dbmap *) }
      iExists _. by iFrame. }
    iModIntro. iApply "HΦ".
    iFrame "Hmref".
    eauto.
  Admitted.

End proph.
