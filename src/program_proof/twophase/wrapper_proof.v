From Perennial.goose_lang Require Import lang notation typing.
From Perennial.goose_lang.lib Require Import map.impl list.impl list_slice.
From Perennial.goose_lang.ffi Require Import jrnl_ffi.
From Perennial.goose_lang.ffi Require Import disk.
From Goose.github_com.mit_pdos.goose_nfsd Require Import txn twophase.
From Perennial.program_proof Require Import lockmap_proof.
From Perennial.program_proof Require Import twophase.op_wrappers.
From Perennial.program_proof Require Import addr.addr_proof buf.buf_proof txn.txn_proof.
From Perennial.program_proof Require Import buftxn.sep_buftxn_proof.
From Perennial.program_proof Require Import twophase.twophase_proof.
From Perennial.goose_lang.lib.list Require Import list.
From Perennial.goose_lang Require Import spec_assert.

From Perennial.goose_lang Require Import ffi.disk_prelude.
From Perennial.program_proof Require Import proof_prelude.

Section proof.
  Context `{!buftxnG Σ}.
  Context `{!heapG Σ}.
  Existing Instances jrnl_spec_ext jrnl_spec_ffi_model jrnl_spec_ext_semantics jrnl_spec_ffi_interp
           jrnl_spec_interp_adequacy.
  Context `{!refinement_heapG Σ}.

  Implicit Types (N: namespace).

  Definition is_twophase_system N γ :=
    is_txn_system N γ.

  Definition val_of_obj (o : obj) := val_of_list ((λ u, LitV (LitByte u)) <$> o).

  Definition is_twophase_pre N l γ γ' dinit objs_dom : iProp Σ :=
    ∃ (txnl locksl : loc) ghs,
      let objs_dom_blknos := get_addr_set_blknos objs_dom in
      "Histwophase_txnl" ∷ readonly (l ↦[TwoPhasePre.S :: "txn"] #txnl) ∗
      "Histwophase_locksl" ∷ readonly (l ↦[TwoPhasePre.S :: "locks"] #locksl) ∗
      "#Histxn_system" ∷ is_txn_system N γ ∗
      "#Histxn" ∷ is_txn txnl γ.(buftxn_txn_names) dinit ∗
      "#HlockMap" ∷ is_lockMap locksl ghs objs_dom_blknos (twophase_linv γ objs_dom) ∗
      "#Htxn_cinv" ∷ txn_cinv N γ γ'.

  Definition is_twophase_started N l γ γ' dinit objs_dom j e1 e2 : iProp Σ :=
    ∃ (txnl locksl : loc) ls ghs σj1 σj2,
    let objs_dom_blknos := get_addr_set_blknos objs_dom in
    "Htwophase.txn" ∷ readonly (l ↦[TwoPhase.S :: "txn"] #txnl) ∗
    "Htwophase.locks" ∷ readonly (l ↦[TwoPhase.S :: "locks"] #locksl) ∗
    "%Halways_steps" ∷ ⌜ always_steps e1 σj1 e2 σj2 ⌝ ∗
    "#Histxn_system" ∷ is_txn_system N γ ∗
    "#Histxn" ∷ is_txn txnl γ.(buftxn_txn_names) dinit ∗
    "#HlockMap" ∷ is_lockMap locksl ghs objs_dom_blknos (twophase_linv γ objs_dom) ∗
    "#Htxn_cinv" ∷ txn_cinv N γ γ' ∗
    "#Hspec_ctx" ∷ spec_ctx ∗
    "Hj" ∷ j ⤇ Atomically ls e1 ∗
    (* TODO: this should be at least all the na_crash_invs in σj1 and the ephemeral values
       for σj2 *)
    "Hlock_resources" ∷ True.

  Definition is_twophase_committed N l γ γ' dinit objs_dom : iProp Σ :=
    ∃ (txnl locksl : loc) ghs (σj : gmap addr obj),
    let objs_dom_blknos := get_addr_set_blknos objs_dom in
    "Htwophase.txn" ∷ readonly (l ↦[TwoPhase.S :: "txn"] #txnl) ∗
    "Htwophase.locks" ∷ readonly (l ↦[TwoPhase.S :: "locks"] #locksl) ∗
    "#Histxn_system" ∷ is_txn_system N γ ∗
    "#Histxn" ∷ is_txn txnl γ.(buftxn_txn_names) dinit ∗
    "#HlockMap" ∷ is_lockMap locksl ghs objs_dom_blknos (twophase_linv γ objs_dom) ∗
    "#Htxn_cinv" ∷ txn_cinv N γ γ' ∗
    (* TODO: this should be at least all the na_crash_invs in σj1 and the ephemeral values
       for σj *)
    "Hlock_resources" ∷ True.

  Theorem wpc_Init' N (d: loc) γ dinit logm objs_dom k :
    {{{ is_txn_durable γ dinit logm }}}
      TwoPhase__Init' #d @ k; ⊤
    {{{ γ' (l: loc), RET #l; is_twophase_pre N l γ γ' dinit objs_dom}}}
    {{{ ∃ γ' logm', ⌜ γ'.(buftxn_txn_names).(txn_kinds) = γ.(buftxn_txn_names).(txn_kinds) ⌝ ∗
        is_txn_durable γ' dinit logm' ∗
       (⌜ γ' = γ ⌝ ∨ txn_cinv N γ γ') }}}.
  Proof. Admitted.

  Theorem wp_TwoPhase__Begin' N l ls γ γ' dinit objs_dom j e1 a sz :
    {{{ is_twophase_pre N l γ γ' dinit objs_dom ∗
        j ⤇ Atomically ls e1 }}}
      TwoPhase__Begin' #l (addr2val a) #sz
    {{{ tph, RET #tph;
        is_twophase_started N tph γ γ' dinit objs_dom
                            j e1 e1 }}}.
  Proof. Admitted.

  Theorem wp_TwoPhase__CommitNoRelease' N l γ γ' dinit objs_dom j e1 e2 :
    {{{ is_twophase_started N l γ γ' dinit objs_dom j e1 e2 }}}
      TwoPhase__CommitNoRelease #l
    {{{ (ok:bool), RET #ok;
        if ok then
          is_twophase_committed N l γ γ' dinit objs_dom ∗
          j ⤇ e2
        else
          is_twophase_started N l γ γ' dinit objs_dom
                              j e1 e2
    }}}.
  Proof. Admitted.

  Theorem wp_TwoPhase__Release' N l γ γ' dinit objs_dom :
    {{{ is_twophase_committed N l γ γ' dinit objs_dom }}}
      TwoPhase__Release #l
    {{{ RET #(); True }}}.
  Proof. Admitted.

  (* Among other things, this and the next spec are missing an assumption that
     the kind/size is correct, so they cannot be proven as is. *)
  Theorem wp_TwoPhase__ReadBuf' N l γ γ' dinit objs_dom j K {HCTX: LanguageCtx K} e1 a sz :
    {{{ is_twophase_started N l γ γ' dinit objs_dom j
                            e1
                            (K (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext)
                                           ReadBufOp (PairV (addr2val' a) #sz))) }}}
      TwoPhase__ReadBuf' #l (addr2val a) #sz
    {{{ v, RET (val_of_obj v);
        is_twophase_started N l γ γ' dinit objs_dom j
                            e1 (K (val_of_obj' v)) }}}.
  Proof. Admitted.

  Theorem wp_TwoPhase__OverWrite' N l γ γ' dinit objs_dom j K {HCTX: LanguageCtx K} e1 a ov :
    {{{ is_twophase_started N l γ γ' dinit objs_dom j
                            e1
                            (K (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext)
                                           OverWriteOp (addr2val' a, val_of_obj' ov))) }}}
      TwoPhase__OverWrite' #l (addr2val a) (val_of_obj ov)
    {{{  RET #();
        is_twophase_started N l γ γ' dinit objs_dom j
                            e1 (K #()) }}}.
  Proof. Admitted.

End proof.
