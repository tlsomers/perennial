From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import
  repr paxos_cquorum paxos_log.
From Perennial.program_proof.tulip.paxos.invariance Require Import ascend.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section ascend.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__ascend (px : loc) (nidme : u64) nids γ :
    nidme ∈ nids ->
    is_paxos_fname px nidme γ -∗
    know_paxos_file_inv γ nids -∗
    know_paxos_inv γ nids -∗
    {{{ own_paxos_nominated px nidme nids γ }}}
      Paxos__ascend #px
    {{{ RET #(); own_paxos px nidme nids γ }}}.
  Proof.
    iIntros (Hnidme) "#Hfname #Hinvfile #Hinv".
    iIntros (Φ) "!> Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) ascend() {                                             @*)
    (*@     // Nothing should be done before obtaining a classic quorum of responses. @*)
    (*@     if !px.cquorum(uint64(len(px.respp))) {                             @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hpx". iNamed "Hcand". iNamed "Honlyc".
    wp_loadField.
    wp_apply (wp_MapLen with "Hrespp").
    iIntros "[%Hsz Hrespp]".
    iNamed "Hpx".
    wp_apply (wp_Paxos__cquorum with "Hsc").
    iIntros (ok) "[Hsc %Hquorum]".
    wp_if_destruct.
    { iApply "HΦ".
      iFrame "HtermcP HtermlP HiscandP HlogP HentspP".
      by iFrame "∗ # %".
    }

    (*@     // Add the longest prefix in the largest term among some quorum (i.e., @*)
    (*@     // @px.entsp) to our log starting from @px.lsnc.                    @*)
    (*@     px.log = append(px.log[: px.lsnc], px.entsp...)                     @*)
    (*@                                                                         @*)
    do 3 wp_loadField.
    wp_apply (wp_SliceTake_full with "Hlog"); first word.
    iIntros "Hlog".
    iDestruct (own_slice_to_small with "Hentsp") as "Hentsp".
    wp_apply (wp_SliceAppendSlice with "[$Hlog $Hentsp]"); first done.
    iIntros (logP') "[Hlog Hentsp]".
    wp_storeField.

    (*@     // Update @px.terml to @px.termc here.                              @*)
    (*@     px.terml = px.termc                                                 @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_storeField.

    (*@     // Transit from the candidate to the leader.                        @*)
    (*@     px.iscand = false                                                   @*)
    (*@     px.isleader = true                                                  @*)
    (*@     px.lsnpeers = make(map[uint64]uint64)                               @*)
    (*@                                                                         @*)
    iNamed "Hleader".
    do 2 wp_storeField.
    wp_apply (wp_NewMap u64 u64).
    iIntros (lsnpeersP') "Hlsnpeers".
    wp_storeField.

    (*@     // Logical action: Ascend(@px.termc, @px.log).                      @*)
    (*@                                                                         @*)
    iNamed "Hfname".
    do 4 wp_loadField.
    wp_apply (wp_logAdvance with "Hentsp").
    iInv "Hinv" as "> HinvO" "HinvC".
    iInv "Hinvfile" as "> HinvfileO" "HinvfileC".
    iDestruct (big_sepS_elem_of_acc with "HinvfileO") as "[Hnodefile HinvfileO]".
    { apply Hnidme. }
    iNamed "Hnodefile".
    iMod (own_crash_ex_open with "Htermc") as "(>Htermc&Hclose_termc)"; first solve_ndisj.
    iApply ncfupd_mask_intro; first solve_ndisj.
    iIntros "Hmask".
    iDestruct (node_wal_fname_agree with "Hfnameme Hwalfname") as %->.
    iFrame "Hfile".
    iExists wal.
    iSplit; first done.
    iIntros (bs') "[Hfile %Hbs']".
    set logc := take (uint.nat lsnc) log.
    set log' := logc ++ entsp.
    iMod (paxos_inv_ascend entsp log' with "[] Hwalfile Htermc Hterml Hlsnc Hlogn HinvO")
      as "(Hwalfile & Htermc & Hterml & Hlsnc & Hlogn & HinvO & Hps & #Hpsb & #Hacptlb)".
    { apply Hnidme. }
    { apply Hton. }
    { word. }
    { clear -Hlsncub. word. }
    { subst log'.
      assert (uint.nat lsnc = length logc) as ->.
      { rewrite length_take. clear -Hlsncub. lia. }
      by rewrite drop_app_length.
    }
    { rewrite length_app length_take. clear -Hlsncub. lia. }
    { by apply prefix_app_r. }
    { iFrame "Hvotes".
      iPureIntro.
      split; first apply Hdomvts.
      rewrite /cquorum_size size_dom.
      word.
    }
    iDestruct ("HinvfileO" with "[Hfile Hwalfile]") as "HinvfileO".
    { iFrame "∗ # %". }
    iMod "Hmask" as "_".
    iMod ("Hclose_termc" with "Htermc") as "Htermc".
    iMod ("HinvfileC" with "HinvfileO") as "_".
    iMod ("HinvC" with "HinvO") as "_".
    iIntros "!> Hents".
    wp_pures.

    (*@     // TODO: Write @px.log and @px.terml to disk.                       @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    set logc' := take (uint.nat lsnc) log'.
    iAssert (own_paxos_leader px nidme termc termc log' true nids γ)%I
      with "[$HisleaderP $HlsnpeersP $Hlsnpeers $Hps]" as "Hleader".
    { iSplit; last done.
      iExists ∅.
      by rewrite big_sepM2_empty.
    }
    iAssert (prefix_base_ledger γ (uint.nat termc) log')%I as "#Hpfb'".
    { by iFrame "Hpsb". }
    iDestruct (safe_ledger_above_mono (uint.nat terml) (uint.nat termc) logc' with "[]")
      as "Hcmted'".
    { word. }
    { subst logc log' logc'.
      rewrite take_app_le; last first.
      { rewrite length_take. lia. }
      by rewrite take_idemp.
    }
    iClear "Hcmted".
    iFrame "Hleader".
    iFrame "HtermcP HtermlP HiscandP Hpfb'".
    iFrame "∗ # %".
    iModIntro.
    iSplit.
    { iClear "Hpreped". by case_decide. }
    iPureIntro.
    split; first done.
    subst log'.
    rewrite length_app length_take.
    lia.
  Qed.

End ascend.
