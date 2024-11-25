From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_repr replica_apply_commit replica_apply_abort.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__apply
    rp cmd pwrsS cloga gid rid γ α :
    let cloga' := cloga ++ [cmd] in
    valid_ccommand gid cmd ->
    group_histm_lbs_from_log γ gid cloga' -∗
    is_txn_log_lb γ gid cloga' -∗
    is_replica_idx rp γ α -∗
    {{{ own_pwrs_slice pwrsS cmd ∗
        own_replica_with_cloga_no_lsna rp cloga gid rid γ α
    }}}
      Replica__apply #rp (ccommand_to_val pwrsS cmd)
    {{{ RET #();
        own_pwrs_slice pwrsS cmd ∗ 
        own_replica_with_cloga_no_lsna rp cloga' gid rid γ α
    }}}.
  Proof.
    iIntros (cloga' Hvcmd) "#Hsafe #Hlb' #Hidx".
    iIntros (Φ) "!> [Hpwrs Hrp] HΦ".
    wp_rec.

    (*@ func (rp *Replica) apply(cmd txnlog.Cmd) {                              @*)
    (*@     if cmd.Kind == 1 {                                                  @*)
    (*@         rp.applyCommit(cmd.Timestamp, cmd.PartialWrites)                @*)
    (*@     } else if cmd.Kind == 2 {                                           @*)
    (*@         rp.applyAbort(cmd.Timestamp)                                    @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_pures.
    destruct cmd eqn:Hcmd; wp_pures.
    { (* Case: CmdCommit. *)
      destruct Hvcmd as [Hvts Hvpwrs].
      iDestruct "Hpwrs" as (pwrsL) "Hpwrs".
      wp_apply (wp_Replica__applyCommit with "[Hsafe] [Hlb'] Hidx [$Hpwrs $Hrp]").
      { apply Hvpwrs. }
      { rewrite uint_nat_W64_of_nat; first done. rewrite /valid_ts in Hvts. word. }
      { rewrite uint_nat_W64_of_nat; first done. rewrite /valid_ts in Hvts. word. }
      iIntros "[Hpwrs Hrp]".
      wp_pures.
      iApply "HΦ".
      rewrite uint_nat_W64_of_nat; last first.
      { rewrite /valid_ts in Hvts. word. }
      by iFrame.
    }
    { (* Case: CmdAbort. *)
      simpl in Hvcmd.
      rewrite /group_histm_lbs_from_log.
      destruct (apply_cmds cloga') as [cpm histm |] eqn:Happly; last done.
      wp_apply (wp_Replica__applyAbort with "[Hlb'] Hrp").
      { rewrite uint_nat_W64_of_nat; first by rewrite Happly. rewrite /valid_ts in Hvcmd. word. }
      { rewrite uint_nat_W64_of_nat; first done. rewrite /valid_ts in Hvcmd. word. }
      iIntros "Hrp".
      wp_pures.
      iApply "HΦ".
      rewrite uint_nat_W64_of_nat; last first.
      { rewrite /valid_ts in Hvcmd. word. }
      by iFrame.
    }
  Qed.

End program.
