From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import  replica_repr.
From Perennial.program_proof.tulip.program.txnlog Require Import txnlog.
From Perennial.program_proof.tulip.program.tuple Require Import res.
From Perennial.program_proof.tulip.program.index Require Import index.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_serve replica_applier.
From Perennial.program_proof.tulip.paxos Require Import prelude.
From Goose.github_com.mit_pdos.tulip Require Import replica.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ, !paxos_ghostG Σ}.

  Theorem wp_Start
    (rid : u64) (addr : chan) (fname : string) (addrmpxP : loc) (fnamepx : string)
    (termc : u64) (terml : u64) (lsnc : u64) (log : list string) (addrmpx : gmap u64 chan)
    (addrm : gmap u64 chan) gid γ π :
    termc = (W64 0) ->
    terml = (W64 0) ->
    lsnc = (W64 0) ->
    log = [] ->
    (* remove above assumptions once recovery is proven *)
    gid ∈ gids_all ->
    rid ∈ rids_all ->
    addrm !! rid = Some addr ->
    is_node_wal_fname π rid fnamepx -∗
    (* paxos atomic invariants *)
    know_paxos_inv π (dom addrmpx) -∗
    know_paxos_file_inv π (dom addrmpx) -∗
    know_paxos_network_inv π addrmpx -∗
    (* txnlog atomic invariants *)
    know_tulip_txnlog_inv γ π gid -∗
    (* tulip atomic invariants *)
    know_tulip_inv γ -∗
    know_tulip_network_inv γ gid addrm -∗
    {{{ (* persistent states passed to paxos *)
        own_map addrmpxP (DfracOwn 1) addrmpx ∗
        own_current_term_half π rid (uint.nat termc) ∗
        own_ledger_term_half π rid (uint.nat terml) ∗
        own_committed_lsn_half π rid (uint.nat lsnc) ∗
        own_node_ledger_half π rid log ∗
        (* persistent states of replica; TODO: replace [] once proving recovery *)
        own_replica_clog_half γ gid rid [] ∗
        own_replica_ilog_half γ gid rid []
    }}}
      Start #rid (to_val addr) #(LitString fname) #addrmpxP #(LitString fnamepx)
    {{{ (rp : loc), RET #rp; is_replica rp gid rid γ }}}.
  Proof.
    iIntros (Htermcz Htermlz Hlsncz Hlogz).
    iIntros (Hgid Hrid Haddr).
    iIntros "#Hfnamewal #Hinvpx #Hinvpxfile #Hinvpxnet".
    iIntros "#Hinvtxnlog #Hinv #Hinvnet".
    iIntros (Φ).
    iIntros "!> (Haddrmpx & Htermc & Hterml & Hlsnc & Hlogn & Hclog & Hilog) HΦ".
    wp_rec. wp_pures.

    (*@ func Start(rid uint64, addr grove_ffi.Address, fname string, addrmpx map[uint64]uint64, fnamepx string) *Replica { @*)
    (*@     txnlog := txnlog.Start(rid, addrmpx, fnamepx)                       @*)
    (*@                                                                         @*)
    wp_apply (wp_Start
      with "Hfnamewal Hinvpx Hinvpxfile Hinvpxnet Hinvtxnlog [$Haddrmpx $Htermc $Hterml $Hlsnc $Hlogn]").
    { done. }
    { done. }
    { done. }
    { done. }
    iIntros (txnlogP) "#Htxnlog".

    (*@     // termc, terml, lsnc, log := resume(fname)                         @*)
    (*@                                                                         @*)
    (*@     rp := &Replica{                                                     @*)
    (*@         mu     : new(sync.Mutex),                                       @*)
    (*@         rid    : rid,                                                   @*)
    (*@         addr   : addr,                                                  @*)
    (*@         fname  : fname,                                                 @*)
    (*@         txnlog : txnlog,                                                @*)
    (*@         lsna   : 0,                                                     @*)
    (*@         prepm  : make(map[uint64][]tulip.WriteEntry),                   @*)
    (*@         ptgsm  : make(map[uint64][]uint64),                             @*)
    (*@         pstbl  : make(map[uint64]PrepareProposal),                      @*)
    (*@         rktbl  : make(map[uint64]uint64),                               @*)
    (*@         txntbl : make(map[uint64]bool),                                 @*)
    (*@         ptsm   : make(map[string]uint64),                               @*)
    (*@         sptsm  : make(map[string]uint64),                               @*)
    (*@         idx    : index.MkIndex(),                                       @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply wp_new_free_lock.
    iIntros (muP) "Hfree".
    wp_apply (wp_NewMap u64 Slice.t).
    iIntros (prepmP) "Hprepm".
    wp_apply (wp_NewMap u64 Slice.t).
    iIntros (ptgsmP) "Hptgsm".
    wp_apply wp_NewMap.
    iIntros (pstblP) "Hpstbl".
    wp_apply wp_NewMap.
    iIntros (rktblP) "Hrktbl".
    wp_apply wp_NewMap.
    iIntros (txntblP) "Htxntbl".
    wp_apply wp_NewMap.
    iIntros (ptsmP) "Hptsm".
    wp_apply wp_NewMap.
    iIntros (sptsmP) "Hsptsm".
    (* Allocate physical history. *)
    iMod phys_hist_alloc as (α) "[Hphysm HphysmX]".
    (* Obtain lower bounds of txn log and replicated history for later use. *)
    iAssert (|={⊤}=> is_txn_log_lb γ gid [])%I as "Htxnloglb".
    { iNamed "Hinv".
      iInv "Hinv" as "> HinvO" "HinvC".
      iNamed "HinvO".
      iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]".
      { apply Hgid. }
      iDestruct (group_inv_extract_log with "Hgroup") as (tlog) "[Htlog Hgroup]".
      iDestruct (txn_log_witness with "Htlog") as "#Htloglb".
      iDestruct (txn_log_lb_weaken [] with "Htloglb") as "#Htloglb'".
      { apply prefix_nil. }
      iDestruct (group_inv_merge_log with "Htlog Hgroup") as "Hgroup".
      iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
      by iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
    }
    iMod "Htxnloglb" as "#Htxnloglb".
    iAssert (|={⊤}=> [∗ set] key ∈ keys_all, is_repl_hist_lb γ key [None])%I as "Hrepllb".
    { iNamed "Hinv".
      iInv "Hinv" as "> HinvO" "HinvC".
      iNamed "HinvO".
      iAssert ([∗ set] key ∈ keys_all, is_repl_hist_lb γ key [None])%I as "#Hreplm".
      { iApply (big_sepS_mono with "Hkeys").
        iIntros (k Hk) "Hkey".
        do 2 iNamed "Hkey".
        iDestruct (repl_hist_witness with "Hrepl") as "#Hrepllb".
        iDestruct (repl_hist_lb_weaken [None] with "Hrepllb") as "#Hrepllb'".
        { by apply prefix_singleton. }
        done.
      }
      by iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
    }
    iMod "Hrepllb" as "#Hrepllb".
    wp_apply (wp_MkIndex with "Hrepllb HphysmX").
    iIntros (idxP) "#Hidx".
    wp_apply (wp_allocStruct).
    { by auto 20. }
    iIntros (rp) "Hrp".
    iDestruct (struct_fields_split with "Hrp") as "Hrp".
    iNamed "Hrp".
    (* Make read-only persistent resources. *)
    iMod (readonly_alloc_1 with "mu") as "#HmuP".
    iMod (readonly_alloc_1 with "addr") as "#HaddrP".
    iMod (readonly_alloc_1 with "rid") as "#HridP".
    iMod (readonly_alloc_1 with "idx") as "#HidxP".
    iMod (readonly_alloc_1 with "txnlog") as "#HtxnlogP".
    iAssert (own_replica_cm rp ∅)%I with "[$txntbl $Htxntbl]" as "Hcm"; first done.
    iAssert (own_replica_histm rp (gset_to_gmap [None] keys_all : gmap dbkey dbhist) α)%I
      with "[Hphysm]" as "Hhistm".
    { iApply (big_sepS_sepM_impl with "Hphysm").
      { by rewrite dom_gset_to_gmap. }
      iIntros (k h Hh) "!> Hphys".
      by apply lookup_gset_to_gmap_Some in Hh as [_ <-].
    }
    iAssert (own_replica_cpm rp ∅)%I with "[$prepm $Hprepm]" as "Hcpm".
    { iExists ∅. by rewrite big_sepM2_empty. }
    set ptsm_init : gmap dbkey nat := gset_to_gmap O keys_all.
    iAssert (own_replica_ptsm_sptsm rp ptsm_init ptsm_init)%I
      with "[$ptsm $sptsm $Hptsm $Hsptsm]" as "Hptsmsptsm".
    { iPureIntro.
      split.
      { intros k Hk. by rewrite lookup_empty lookup_gset_to_gmap_Some. }
      { intros k Hk. by rewrite lookup_empty lookup_gset_to_gmap_Some. }
    }
    iAssert (own_replica_psm_rkm rp ∅ ∅)%I
      with "[$pstbl $rktbl $Hpstbl $Hrktbl]" as "Hpsmrkm"; first done.
    iAssert (own_replica_with_cloga_no_lsna rp [] gid rid γ α)%I
      with "[$Hcm $Hhistm $Hcpm $Hptsmsptsm $Hpsmrkm $Hclog $Hilog]" as "Hrp".
    { iExists ∅.
      iSplit; first by rewrite dom_empty_L big_sepS_empty.
      iSplit; first by rewrite big_sepM_empty.
      iSplit; first done.
      by rewrite merge_clog_ilog_nil.
    }
    iAssert (own_replica rp gid rid γ α)%I with "[$lsna Hrp]" as "Hrp".
    { iExists []. by iFrame. }
    iMod (alloc_lock _ _ _ (own_replica rp gid rid γ α) with "Hfree [$Hrp]") as "#Hlock".
    iAssert (is_replica_plus_txnlog rp gid rid γ)%I as "#Hrptxnlog".
    { by iFrame "#". }
    iAssert (is_replica_plus_network rp addr gid rid γ)%I as "#Hrpnet".
    { by iFrame "#". }
    wp_pures.

    (*@     go func() {                                                         @*)
    (*@         rp.Serve()                                                      @*)
    (*@     }()                                                                 @*)
    (*@                                                                         @*)
    wp_apply wp_fork.
    { by wp_apply (wp_Replica__Serve with "Hrpnet"). }

    (*@     go func() {                                                         @*)
    (*@         rp.Applier()                                                    @*)
    (*@     }()                                                                 @*)
    (*@                                                                         @*)
    wp_apply wp_fork.
    { by wp_apply (wp_Replica__Applier with "Hrptxnlog"). }
    wp_pures.

    (*@     return rp                                                           @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    by iFrame "#".
  Qed.

End program.
