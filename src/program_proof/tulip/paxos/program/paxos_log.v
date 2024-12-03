From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.program.util Require Import encode_string encode_strings.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

(* Copy pasted from grove_ffi_typed.v *)
Ltac inv_undefined :=
  match goal with
  | [ H: relation.denote (match ?e with | _ => _ end) _ _ _ |- _ ] =>
    destruct e; try (apply suchThat_false in H; contradiction)
  end.
Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
  [ apply heap_base_atomic; cbn [relation.denote base_trans]; intros * H;
    repeat inv_undefined;
    try solve [ apply atomically_is_val in H; auto ]
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].
Local Ltac solve_atomic2 :=
  solve_atomic;
  (* TODO(Joe): Cleanup *)
  repeat match goal with
    | [ H: relation.denote _ ?s1 ?s2 ?v |- _ ] => inversion_clear H
    | _ => progress monad_inv
    | _ => case_match
    end; eauto.

Section log.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_logAdvance
    (fname : string) (termW : u64) (lsnW : u64) (entsS : Slice.t) (ents : list string) :
    let lsn := uint.nat lsnW in
    let term := uint.nat termW in
    ⊢
    {{{ own_slice_small entsS stringT (DfracOwn 1) ents }}}
    <<< ∀∀ bs wal, fname f↦ bs ∗ ⌜encode_paxos_cmds wal bs⌝ >>>
      logAdvance #(LitString fname) #termW #lsnW (to_val entsS) @ ∅
    <<< ∃∃ bs', fname f↦ bs' ∗ ⌜encode_paxos_cmds (wal ++ [CmdPaxosAdvance term lsn ents]) bs'⌝ >>>
    {{{ RET #(); own_slice_small entsS stringT (DfracOwn 1) ents }}}.
  Proof.
    iIntros (lsn term Φ) "!> Hents HAU".
    wp_rec.

    (*@ func logAdvance(fname string, term uint64, lsn uint64, ents []string) { @*)
    (*@     bs := make([]byte, 0, 64)                                           @*)
    (*@                                                                         @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p1) "Hbs".
    rewrite uint_nat_W64_0 replicate_0.

    (*@     bs1 := marshal.WriteInt(bs, CMD_ADVANCE)                            @*)
    (*@     bs2 := marshal.WriteInt(bs1, term)                                  @*)
    (*@     bs3 := marshal.WriteInt(bs2, lsn)                                   @*)
    (*@     bs4 := util.EncodeStrings(bs3, ents)                                @*)
    (*@                                                                         @*)
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p3) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p4) "Hbs".
    wp_apply (wp_EncodeStrings with "[$Hbs $Hents]").
    iIntros (p5) "[Hbs Hents]".
    wp_pures.

    (*@     grove_ffi.FileAppend(fname, bs4)                                    @*)
    (*@ }                                                                       @*)
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_bind (ExternalOp _ _).
    rewrite difference_empty_L.
    iApply (wp_ncatomic _ _ ∅).
    { solve_atomic2. }
    iDestruct (own_slice_to_small with "Hbs") as "Hbs".
    iDestruct (own_slice_small_sz with "Hbs") as %Hszbs.
    iMod "HAU" as (bs wal) "[[Hfile %Henc] HAU]".
    iModIntro.
    wp_apply (wp_FileAppendOp with "[$Hfile Hbs]").
    { apply Hszbs. }
    { iApply (own_slice_small_byte_pointsto_vals with "Hbs"). }
    iIntros (err) "[Hfile Hbs]".
    iMod ("HAU" with "[$Hfile]") as "HΦ".
    iModIntro.
    wp_pures.
    destruct err; wp_pures.
    { wp_apply wp_Exit. iIntros "[]". }
    by iApply "HΦ".
  Qed.

  Theorem wp_logAccept
    (fname : string) (lsnW : u64) (entsS : Slice.t) (ents : list string) :
    let lsn := uint.nat lsnW in
    ⊢
    {{{ own_slice_small entsS stringT (DfracOwn 1) ents }}}
    <<< ∀∀ bs wal, fname f↦ bs ∗ ⌜encode_paxos_cmds wal bs⌝ >>>
      logAccept #(LitString fname) #lsnW (to_val entsS) @ ∅
    <<< ∃∃ bs', fname f↦ bs' ∗ ⌜encode_paxos_cmds (wal ++ [CmdPaxosAccept lsn ents]) bs'⌝ >>>
    {{{ RET #(); own_slice_small entsS stringT (DfracOwn 1) ents }}}.
  Proof.
    iIntros (lsn Φ) "!> Hents HAU".
    wp_rec.

    (*@ func logAccept(fname string, lsn uint64, ents []string) {               @*)
    (*@     bs := make([]byte, 0, 64)                                           @*)
    (*@                                                                         @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p1) "Hbs".
    rewrite uint_nat_W64_0 replicate_0.

    (*@     bs1 := marshal.WriteInt(bs, CMD_ACCEPT)                             @*)
    (*@     bs2 := marshal.WriteInt(bs1, lsn)                                   @*)
    (*@     bs3 := util.EncodeStrings(bs2, ents)                                @*)
    (*@                                                                         @*)
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p3) "Hbs".
    wp_apply (wp_EncodeStrings with "[$Hbs $Hents]").
    iIntros (p4) "[Hbs Hents]".
    wp_pures.

    (*@     grove_ffi.FileAppend(fname, bs3)                                    @*)
    (*@ }                                                                       @*)
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_bind (ExternalOp _ _).
    rewrite difference_empty_L.
    iApply (wp_ncatomic _ _ ∅).
    { solve_atomic2. }
    iDestruct (own_slice_to_small with "Hbs") as "Hbs".
    iDestruct (own_slice_small_sz with "Hbs") as %Hszbs.
    iMod "HAU" as (bs wal) "[[Hfile %Henc] HAU]".
    iModIntro.
    wp_apply (wp_FileAppendOp with "[$Hfile Hbs]").
    { apply Hszbs. }
    { iApply (own_slice_small_byte_pointsto_vals with "Hbs"). }
    iIntros (err) "[Hfile Hbs]".
    iMod ("HAU" with "[$Hfile]") as "HΦ".
    iModIntro.
    wp_pures.
    destruct err; wp_pures.
    { wp_apply wp_Exit. iIntros "[]". }
    by iApply "HΦ".
  Qed.

  Theorem wp_logPrepare (fname : string) (termW : u64) :
    let term := uint.nat termW in
    ⊢
    {{{ True }}}
    <<< ∀∀ bs wal, fname f↦ bs ∗ ⌜encode_paxos_cmds wal bs⌝ >>>
      logPrepare #(LitString fname) #termW @ ∅
    <<< ∃∃ bs', fname f↦ bs' ∗ ⌜encode_paxos_cmds (wal ++ [CmdPaxosPrepare term]) bs'⌝ >>>
    {{{ RET #(); True }}}.
  Proof.
    iIntros (term Φ) "!> Hents HAU".
    wp_rec.

    (*@ func logPrepare(fname string, term uint64) {                            @*)
    (*@     bs := make([]byte, 0, 16)                                           @*)
    (*@                                                                         @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p1) "Hbs".
    rewrite uint_nat_W64_0 replicate_0.

    (*@     bs1 := marshal.WriteInt(bs, CMD_PREPARE)                            @*)
    (*@     bs2 := marshal.WriteInt(bs1, term)                                  @*)
    (*@                                                                         @*)
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p3) "Hbs".
    wp_pures.

    (*@     grove_ffi.FileAppend(fname, bs2)                                    @*)
    (*@ }                                                                       @*)
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_bind (ExternalOp _ _).
    rewrite difference_empty_L.
    iApply (wp_ncatomic _ _ ∅).
    { solve_atomic2. }
    iDestruct (own_slice_to_small with "Hbs") as "Hbs".
    iDestruct (own_slice_small_sz with "Hbs") as %Hszbs.
    iMod "HAU" as (bs wal) "[[Hfile %Henc] HAU]".
    iModIntro.
    wp_apply (wp_FileAppendOp with "[$Hfile Hbs]").
    { apply Hszbs. }
    { iApply (own_slice_small_byte_pointsto_vals with "Hbs"). }
    iIntros (err) "[Hfile Hbs]".
    iMod ("HAU" with "[$Hfile]") as "HΦ".
    iModIntro.
    wp_pures.
    destruct err; wp_pures.
    { wp_apply wp_Exit. iIntros "[]". }
    by iApply "HΦ".
  Qed.

  Theorem wp_logAppend (fname : string) (ent : string) :
    ⊢
    {{{ True }}}
    <<< ∀∀ bs wal, fname f↦ bs ∗ ⌜encode_paxos_cmds wal bs⌝ >>>
      logAppend #(LitString fname) #(LitString ent) @ ∅
    <<< ∃∃ bs', fname f↦ bs' ∗ ⌜encode_paxos_cmds (wal ++ [CmdPaxosExtend [ent]]) bs'⌝ >>>
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "!> Hents HAU".
    wp_rec.

    (*@ func logAppend(fname string, ent string) {                              @*)
    (*@     bs := make([]byte, 0, 32)                                           @*)
    (*@                                                                         @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p1) "Hbs".
    rewrite uint_nat_W64_0 replicate_0.

    (*@     bs1 := marshal.WriteInt(bs, CMD_APPEND)                             @*)
    (*@     bs2 := util.EncodeString(bs1, ent)                                  @*)
    (*@                                                                         @*)
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_EncodeString with "Hbs").
    iIntros (p3) "Hbs".
    wp_pures.

    (*@     grove_ffi.FileAppend(fname, bs2)                                    @*)
    (*@ }                                                                       @*)
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_bind (ExternalOp _ _).
    rewrite difference_empty_L.
    iApply (wp_ncatomic _ _ ∅).
    { solve_atomic2. }
    iDestruct (own_slice_to_small with "Hbs") as "Hbs".
    iDestruct (own_slice_small_sz with "Hbs") as %Hszbs.
    iMod "HAU" as (bs wal) "[[Hfile %Henc] HAU]".
    iModIntro.
    wp_apply (wp_FileAppendOp with "[$Hfile Hbs]").
    { apply Hszbs. }
    { iApply (own_slice_small_byte_pointsto_vals with "Hbs"). }
    iIntros (err) "[Hfile Hbs]".
    iMod ("HAU" with "[$Hfile]") as "HΦ".
    iModIntro.
    wp_pures.
    destruct err; wp_pures.
    { wp_apply wp_Exit. iIntros "[]". }
    by iApply "HΦ".
  Qed.

  Theorem wp_logExtend (fname : string) (entsS : Slice.t) (ents : list string) :
    ⊢
    {{{ own_slice_small entsS stringT (DfracOwn 1) ents }}}
    <<< ∀∀ bs wal, fname f↦ bs ∗ ⌜encode_paxos_cmds wal bs⌝ >>>
      logExtend #(LitString fname) (to_val entsS) @ ∅
    <<< ∃∃ bs', fname f↦ bs' ∗ ⌜encode_paxos_cmds (wal ++ [CmdPaxosExtend ents]) bs'⌝ >>>
    {{{ RET #(); own_slice_small entsS stringT (DfracOwn 1) ents }}}.
  Proof.
    iIntros (Φ) "!> Hents HAU".
    wp_rec.

    (*@ func logExtend(fname string, ents []string) {                           @*)
    (*@     // Currently not used. For batch optimization.                      @*)
    (*@     bs := make([]byte, 0, 64)                                           @*)
    (*@                                                                         @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p1) "Hbs".
    rewrite uint_nat_W64_0 replicate_0.

    (*@     bs1 := marshal.WriteInt(bs, CMD_EXTEND)                             @*)
    (*@     bs2 := util.EncodeStrings(bs1, ents)                                @*)
    (*@                                                                         @*)
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_EncodeStrings with "[$Hbs $Hents]").
    iIntros (p3) "[Hbs Hents]".
    wp_pures.

    (*@     grove_ffi.FileAppend(fname, bs2)                                    @*)
    (*@ }                                                                       @*)
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_bind (ExternalOp _ _).
    rewrite difference_empty_L.
    iApply (wp_ncatomic _ _ ∅).
    { solve_atomic2. }
    iDestruct (own_slice_to_small with "Hbs") as "Hbs".
    iDestruct (own_slice_small_sz with "Hbs") as %Hszbs.
    iMod "HAU" as (bs wal) "[[Hfile %Henc] HAU]".
    iModIntro.
    wp_apply (wp_FileAppendOp with "[$Hfile Hbs]").
    { apply Hszbs. }
    { iApply (own_slice_small_byte_pointsto_vals with "Hbs"). }
    iIntros (err) "[Hfile Hbs]".
    iMod ("HAU" with "[$Hfile]") as "HΦ".
    iModIntro.
    wp_pures.
    destruct err; wp_pures.
    { wp_apply wp_Exit. iIntros "[]". }
    by iApply "HΦ".
  Qed.

  Theorem wp_logExpand (fname : string) (lsnW : u64) :
    let lsn := uint.nat lsnW in
    ⊢
    {{{ True }}}
    <<< ∀∀ bs wal, fname f↦ bs ∗ ⌜encode_paxos_cmds wal bs⌝ >>>
      logExpand #(LitString fname) #lsnW @ ∅
    <<< ∃∃ bs', fname f↦ bs' ∗ ⌜encode_paxos_cmds (wal ++ [CmdPaxosExpand lsn]) bs'⌝ >>>
    {{{ RET #(); True }}}.
  Proof.
    iIntros (lsn Φ) "!> Hents HAU".
    wp_rec.

    (*@ func logExpand(fname string, lsn uint64) {                              @*)
    (*@     bs := make([]byte, 0, 16)                                           @*)
    (*@                                                                         @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p1) "Hbs".
    rewrite uint_nat_W64_0 replicate_0.

    (*@     bs1 := marshal.WriteInt(bs, CMD_EXPAND)                             @*)
    (*@     bs2 := marshal.WriteInt(bs1, lsn)                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p3) "Hbs".
    wp_pures.

    (*@     grove_ffi.FileAppend(fname, bs2)                                    @*)
    (*@ }                                                                       @*)
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_rec. wp_pures.
    wp_bind (ExternalOp _ _).
    rewrite difference_empty_L.
    iApply (wp_ncatomic _ _ ∅).
    { solve_atomic2. }
    iDestruct (own_slice_to_small with "Hbs") as "Hbs".
    iDestruct (own_slice_small_sz with "Hbs") as %Hszbs.
    iMod "HAU" as (bs wal) "[[Hfile %Henc] HAU]".
    iModIntro.
    wp_apply (wp_FileAppendOp with "[$Hfile Hbs]").
    { apply Hszbs. }
    { iApply (own_slice_small_byte_pointsto_vals with "Hbs"). }
    iIntros (err) "[Hfile Hbs]".
    iMod ("HAU" with "[$Hfile]") as "HΦ".
    iModIntro.
    wp_pures.
    destruct err; wp_pures.
    { wp_apply wp_Exit. iIntros "[]". }
    by iApply "HΦ".
  Qed.

End log.
