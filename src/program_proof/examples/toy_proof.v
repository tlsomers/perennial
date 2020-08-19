From RecordUpdate Require Import RecordSet.

From Perennial.Helpers Require Import ModArith.
From Perennial.goose_lang Require Import crash_modality wpr_lifting.
From Perennial.algebra Require Import deletable_heap.

From Goose.github_com.mit_pdos.perennial_examples Require Import toy.
From Perennial.program_logic Require Import na_crash_inv.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import proof_prelude.

Section goose.
  Context `{!heapG Σ}.
  Context `{!crashG Σ}.
  Context `{!stagedG Σ}.

  (* TODO: these are copied from the circ proof *)
  Definition block0: Block :=
    list_to_vec (replicate (Z.to_nat 4096) (U8 0)).

  Lemma replicate_zero_to_block0 :
    replicate (int.nat 4096) (zero_val byteT) =
    Block_to_vals block0.
  Proof.
    change (zero_val byteT) with #(U8 0).
    change (int.nat 4096) with (Z.to_nat 4096).
    rewrite /Block_to_vals /block0.
    reflexivity.
  Qed.

  Definition EBlk (addr: u64) :=
   (∃ v n, "Ha" ∷ int.val addr d↦ v ∗ "%H0iseven" ∷ ⌜ Block_to_vals v !! O = Some #(U8 n) ∧ Z.even n ⌝)%I.

  Definition written_slice : list val :=
    <[int.nat 0:=#(U8 4)]> (replicate (int.nat 4096) (zero_val byteT)).

  Definition written_block : Block := list_to_vec (U8 4 :: replicate (int.nat 4095) (U8 0)).

  Lemma written_slice_to_written_block:
    written_slice = Block_to_vals written_block.
  Proof.
    rewrite /written_slice.
    change (zero_val byteT) with #(U8 0).
    change (int.nat 4095) with (Z.to_nat 4095).
    rewrite /Block_to_vals /written_block //=.
  Qed.

  Theorem wpc_consumeEvenBlock_seq {k E1 E2} (d_ref: loc) (addr: u64) :
    {{{ EBlk addr }}}
      consumeEvenBlock #d_ref #addr @ NotStuck;k; E1;E2
    {{{ RET #(); EBlk addr }}}
    {{{ EBlk addr }}}.
  Proof.
    iIntros (Φ Φc) "HE HΦ"; iNamed "HE".
    wpc_call.
    { iExists _, _; eauto. }
    { iExists _, _; eauto. }
    rewrite /BlockSize.
    iCache (<disc> ▷ Φc)%I with "HΦ Ha".
    { crash_case. iExists _, _; eauto. }
    wpc_pures.
    wpc_frame_seq.
    wp_apply (wp_new_slice).
    { apply to_val_has_zero. }
    iIntros (s) "Hslice". iNamed 1.
    wpc_pures.
    wpc_frame_seq.
    iDestruct (is_slice_small_acc with "Hslice") as "(H1&H2)".
    wp_apply (wp_SliceSet with "[$H1]").
    { eauto. }
    iIntros "Hslice"; iNamed 1.
    wpc_pures.
    wpc_bind (Write _ _).
    iApply (wpc_Write_fupd E1 with "[ Hslice]").
    { rewrite /is_block. iExactEq "Hslice". f_equal.
      erewrite <-written_slice_to_written_block. eauto.
    }
    iSplit; first iFromCache.
    iModIntro.
    iExists _. iFrame. iNext.
    iIntros "Hwritten".
    iModIntro.
    iCache (<disc> ▷ Φc)%I with "Hwritten HΦ".
    { crash_case. iExists _, 4. iFrame. iPureIntro. rewrite //=. }
    iSplit; first iFromCache.
    iIntros "Hblock".
    wpc_pures.

    wpc_bind (Read _).
    iApply (wpc_Read with "Hwritten").
    iSplit.
    { iLeft in "HΦ". iModIntro. iNext. iIntros "Hwritten". iApply "HΦ".
      iExists _, 4. iFrame. iPureIntro. rewrite //=. }
    iNext. iIntros (s') "(Hwritten&Hslice)".
    wpc_pures.

    wpc_frame.
    wp_bind (SliceGet _ _ _).
    iDestruct (is_slice_small_acc with "Hslice") as "(H1&H2')".
    iApply (wp_SliceGet with "[$H1]").
    { iPureIntro. rewrite //=. }
    iNext. iIntros "(H1&%Hval)".
    wp_pures.
    iNamed 1.
    iApply "HΦ". iExists _, _. iFrame. eauto.
  Qed.

  Theorem wpc_consumeEvenBlock {k k' E2} (d_ref: loc) (addr: u64):
    (S k ≤ k')%nat →
    {{{ na_crash_inv (S k') (EBlk addr) (EBlk addr) }}}
      consumeEvenBlock #d_ref #addr @ NotStuck; (S k); ⊤;E2
    {{{ RET #() ; True }}}
    {{{ True }}}.
  Proof.
    iIntros (? Φ Φc) "Hcrash_inv HΦ".
    iApply (wpc_na_crash_inv_open with "Hcrash_inv"); try eassumption.
    { lia. }
    iSplit; first by crash_case.
    iIntros ">Hblk".
    wpc_apply (wpc_consumeEvenBlock_seq with "[$]").
    iSplit.
    { iLeft in "HΦ". iModIntro. iNext. iIntros; iFrame. by iApply "HΦ". }
    iNext. iIntros "$ _".
    iSplit; first by crash_case.
    by iApply "HΦ".
  Qed.

  Theorem wpc_TransferEvenBlock {E2} (d_ref: loc) (addr: u64) :
    {{{ EBlk addr }}}
      TransferEvenBlock #d_ref #addr @ NotStuck; 2; ⊤;E2
    {{{ RET #() ; True }}}
    {{{ EBlk addr }}}.
  Proof using stagedG0.
    iIntros (Φ Φc) "HEblk HΦ".
    iMod (na_crash_inv_alloc 1 _ (EBlk addr) (EBlk addr) with "HEblk []") as "(Hcrash&Hcfupd)".
    { auto. }
    (* Weaken the levels. *)
    iMod "Hcfupd" as "_".
    (*  { apply LVL_le. lia. } *)
    wpc_call.
    { by iLeft in "HΦ". }
    { by iLeft in "HΦ". }
    wpc_pures.
    { by iLeft in "HΦ". }
    iApply (wpc_idx_mono 1); first by lia.
    iApply (wpc_fork with "[Hcrash]").
    { iNext. iApply (wpc_consumeEvenBlock with "Hcrash"); eauto. iSplit; try iModIntro; eauto. }
    iSplit.
    { by iLeft in "HΦ". }
    { iNext; by iApply "HΦ". }
  Qed.

End goose.
