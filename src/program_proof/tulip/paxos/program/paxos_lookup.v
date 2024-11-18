From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Perennial.program_proof.tulip.paxos.invariance Require Import commit.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section lookup.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__Lookup (px : loc) (lsn : u64) nidme γ :
    is_paxos px nidme γ -∗
    {{{ True }}}
    <<< ∀∀ log, own_log_half γ log >>>
      Paxos__Lookup #px #lsn @ ↑paxosNS
    <<< ∃∃ log', own_log_half γ log' >>>
    {{{ (v : string) (ok : bool), RET (#(LitString v), #ok);
        ⌜if ok then log' !! (uint.nat lsn) = Some v else True⌝
    }}}.
  Proof.
    iIntros "#Hinv" (Φ) "!> _ HAU".
    wp_rec.

    (*@ func (px *Paxos) Lookup(lsn uint64) (string, bool) {                    @*)
    (*@     px.mu.Lock()                                                        @*)
    (*@                                                                         @*)
    iNamed "Hinv".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked [Hpx Hcomm]]".

    (*@     if px.lsnc <= lsn {                                                 @*)
    (*@         px.mu.Unlock()                                                  @*)
    (*@         return "", false                                                @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    do 2 iNamed "Hpx".
    wp_loadField.
    wp_if_destruct.
    { wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HAU]").
      { iFrame "Hlock Hlocked".
        iFrame "∗ # %".
      }
      wp_pures.
      (* Simply take and give back the same log. *)
      iMod (ncfupd_mask_subseteq (⊤ ∖ ↑paxosNS)) as "Hclose"; first solve_ndisj.
      iMod "HAU" as (logcli) "[Hlogcli HAU]".
      iMod ("HAU" with "Hlogcli") as "HΦ".
      iMod "Hclose" as "_".
      by iApply "HΦ".
    }
    rename Heqb into Hlt.
    rewrite Z.nle_gt in Hlt.

    (*@     v := px.log[lsn]                                                    @*)
    (*@                                                                         @*)
    wp_loadField.
    iDestruct (own_slice_small_acc with "Hlog") as "[Hlog HlogC]".
    assert (is_Some (log !! uint.nat lsn)) as [c Hc].
    { apply lookup_lt_is_Some_2. clear -Hlt Hlsncub. word. }
    wp_apply (wp_SliceGet with "[$Hlog]").
    { iPureIntro. apply Hc. }
    iIntros "Hlog".
    iDestruct ("HlogC" with "Hlog") as "Hlog".
    wp_pures.

    (*@     // Logical action: Commit(@px.log) if @px.log is longer than the global log. @*)
    (*@                                                                         @*)
    iApply ncfupd_wp.
    iInv "Hinv" as "> HinvO" "HinvC".
    iMod (ncfupd_mask_subseteq (⊤ ∖ ↑paxosNS)) as "Hmask"; first solve_ndisj.
    iMod "HAU" as (logcli) "[Hlogcli HAU]".
    set logc := take _ log.
    iNamed "Hnids".
    iMod (paxos_inv_commit logc with "[] Hlogcli Hlogn HinvO") as "(Hlogcli & Hlogn & HinvO)".
    { set_solver. }
    { apply prefix_take. }
    { iDestruct "Hcmted" as (t) "[Hsafe _]".
      iFrame "Hsafe".
    }
    iDestruct "Hlogcli" as (logcli') "[Hlogcli %Hprefix]".
    iMod ("HAU" with "Hlogcli") as "HΦ".
    iMod "Hmask" as "_".
    iMod ("HinvC" with "HinvO") as "_".
    iModIntro.

    (*@     px.mu.Unlock()                                                      @*)
    (*@     return v, true                                                      @*)
    (*@ }                                                                       @*)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "Hlock Hlocked".
      iFrame "Hcand Hleader".
      iFrame "∗ # %".
    }
    wp_pures.
    iApply "HΦ".
    iPureIntro.
    rewrite -(prefix_lookup_lt logc log) in Hc; last first.
    { apply prefix_take. }
    { rewrite length_take. clear -Hlsncub Hlt. word. }
    eapply prefix_lookup_Some; [apply Hc | apply Hprefix].
  Qed.

End lookup.
