From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Export
     lang notation array typing struct
     tactics lifting proofmode.
From Perennial.goose_lang Require Import slice basic_triples.
From Perennial.goose_lang Require Export encoding.

Set Default Proof Using "Type".

Section heap.
Context `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ}.
Context {ext_ty: ext_types ext}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).
Implicit Types v : val.
Implicit Types vs : list val.
Implicit Types z : Z.
Implicit Types off : nat.

Lemma word_sru_0 width (word: Interface.word width) (ok: word.ok word)
      (x: word) s : int.val s = 0 -> word.sru x s = x.
Proof.
  intros.
  apply word.unsigned_inj.
  rewrite word.unsigned_sru.
  - rewrite H.
    rewrite Z.shiftr_0_r.
    unfold word.wrap.
    rewrite word.wrap_unsigned.
    auto.
  - rewrite H.
    apply word.width_pos.
Qed.

Theorem word_wrap_wrap `{word1: Interface.word width1} `{word2: Interface.word width2}
        {ok1: word.ok word1}
        {ok2: word.ok word2} z :
  width1 <= width2 ->
  word.wrap (word:=word1) (word.wrap (word:=word2) z) = word.wrap (word:=word1) z.
Proof.
  unfold word.wrap; intros.
  pose proof (@word.width_pos width1 _ _).
  pose proof (@word.width_pos width2 _ _).
  pose proof (Z.pow_pos_nonneg 2 width1 ltac:(lia) ltac:(lia)).
  pose proof (Z.pow_pos_nonneg 2 width2 ltac:(lia) ltac:(lia)).
  rewrite <- Znumtheory.Zmod_div_mod; try lia.
  exists (2 ^ (width2 - width1)).
  rewrite <- Z.pow_add_r; try lia.
  f_equal.
  lia.
Qed.

Theorem word_wrap_wrap' `{word1: Interface.word width1} `{word2: Interface.word width2}
        {ok1: word.ok word1}
        {ok2: word.ok word2} z :
  width2 <= width1 ->
  word.wrap (word:=word1) (word.wrap (word:=word2) z) = word.wrap (word:=word2) z.
Proof.
  unfold word.wrap; intros.
  pose proof (@word.width_pos width1 _ _).
  pose proof (@word.width_pos width2 _ _).
  pose proof (Z.pow_pos_nonneg 2 width1 ltac:(lia) ltac:(lia)).
  pose proof (Z.pow_pos_nonneg 2 width2 ltac:(lia) ltac:(lia)).
Admitted.

Hint Rewrite word.unsigned_of_Z : word.
Hint Rewrite word.unsigned_sru : word.

Theorem word_byte_extract (x:u32) k :
  0 <= k < 4 ->
  word.of_Z (int.val x ≫ (k*8)) = u8_from_u32 (word.sru x (U32 (k*8))).
Proof.
  intros.
  apply word.unsigned_inj.
  unfold u8_from_u32, U8.
  autorewrite with word.
  rewrite word.unsigned_sru;
    rewrite unsigned_U32.
  { rewrite word_wrap_wrap; last lia.
    rewrite [word.wrap (k * _)]wrap_small; last lia.
    reflexivity.
  }
  rewrite wrap_small; lia.
Qed.

Theorem u32_le_to_sru (x: u32) :
  b2val <$> u32_le x =
  cons #(u8_from_u32 (word.sru x (U32 (0%nat * 8))))
       (cons #(u8_from_u32 (word.sru x (U32 (1%nat * 8))))
             (cons #(u8_from_u32 (word.sru x (U32 (2%nat * 8))))
                   (cons #(u8_from_u32 (word.sru x (U32 (3%nat * 8))))
                         nil))).
Proof.
  rewrite /b2val.
  cbv [u32_le fmap list_fmap LittleEndian.split HList.tuple.to_list List.map].
  rewrite -word_byte_extract; last lia.
  rewrite -word_byte_extract; last lia.
  rewrite -word_byte_extract; last lia.
  rewrite -word_byte_extract; last lia.
  reflexivity.
Qed.

Theorem wp_EncodeUInt32 (l: loc) (x: u32) vs s E :
  {{{ ▷ l ↦∗[byteT] vs ∗ ⌜ length vs = u32_bytes ⌝ }}}
    EncodeUInt32 #x #l @ s ; E
  {{{ RET #(); l ↦∗[byteT] (b2val <$> u32_le x) }}}.
Proof.
  iIntros (Φ) "(>Hl & %) HΦ".
  unfold EncodeUInt32.
  repeat (destruct vs; simpl in H; [ congruence | ]).
  destruct vs; [ | simpl in H; congruence ]; clear H.
  remember u8T.
  simpl.
  cbv [array].
  iDestruct "Hl" as "(Hv&Hv0&Hv1&Hv2&_)".
  wp_pures.
  rewrite ?Z.mul_1_l.
  wp_apply (wp_StoreAt with "[Hv]").
  { subst; repeat constructor. }
  { subst; iFrame. }
  iIntros "Hv".

  wp_pures.
  rewrite Z.mul_1_l.
  wp_apply (wp_StoreAt with "[Hv0]").
  { subst; repeat constructor. }
  { subst; iFrame. }
  iIntros "Hv0".

  wp_pures.
  rewrite Z.mul_1_l.
  wp_apply (wp_StoreAt with "[Hv1]").
  { subst; repeat constructor. }
  { subst; iFrame. }
  iIntros "Hv1".

  wp_pures.
  rewrite Z.mul_1_l.
  wp_apply (wp_StoreAt with "[Hv2]").
  { subst; repeat constructor. }
  { subst; iFrame. }
  iIntros "Hv2".

  iApply "HΦ".
  change (U32 8) with (U32 (1 * 8)).
  rewrite -?word_byte_extract; try lia.
  subst.
  simpl.
  iFrame.
Qed.

Definition u64_le_bytes (x: u64) : list val :=
  b2val <$> u64_le x.

Lemma u64_le_bytes_length x : length (u64_le_bytes x) = u64_bytes.
Proof.
  rewrite fmap_length //.
Qed.

Theorem wp_EncodeUInt64 (l: loc) (x: u64) vs stk E :
  {{{ ▷ l ↦∗[byteT] vs ∗ ⌜ length vs = u64_bytes ⌝ }}}
    EncodeUInt64 #x #l @ stk ; E
  {{{ RET #(); l ↦∗[byteT] (b2val <$> u64_le x) }}}.
Proof.
Admitted.

Theorem wp_UInt64Put stk E s x vs :
  {{{ is_slice_small s byteT vs ∗ ⌜length vs >= u64_bytes⌝ }}}
    UInt64Put (slice_val s) #x @ stk; E
  {{{ RET #(); is_slice_small s byteT (u64_le_bytes x ++ (drop u64_bytes vs)) }}}.
Proof.
  iIntros (Φ) "[Hsl %] HΦ".
  wp_lam.
  wp_let.
  wp_lam.
  wp_pures.
  iDestruct "Hsl" as "(Hptr&%)".
  iDestruct (array_split 8 with "Hptr") as "[Henc Hrest]"; [ lia .. | ].
  wp_apply (wp_EncodeUInt64 with "[$Henc]").
  { iPureIntro.
    rewrite take_length; lia. }
  iIntros "Henc".
  change (Z.to_nat 8) with 8%nat.
  iDestruct (array_app with "[$Henc $Hrest]") as "Htogether".
  iApply "HΦ".
  iFrame.
  rewrite app_length drop_length u64_le_bytes_length.
  iPureIntro.
  lia.
Qed.

Definition u32_le_bytes (x: u32) : list val :=
  b2val <$> u32_le x.

Lemma u32_le_bytes_length x : length (u32_le_bytes x) = u32_bytes.
Proof.
  rewrite fmap_length //.
Qed.

Theorem wp_UInt32Put stk E s (x: u32) vs :
  {{{ is_slice_small s byteT vs ∗ ⌜length vs >= u32_bytes⌝ }}}
    UInt32Put (slice_val s) #x @ stk; E
  {{{ RET #(); is_slice_small s byteT (u32_le_bytes x ++ (drop u32_bytes vs)) }}}.
Proof.
  iIntros (Φ) "[Hsl %] HΦ".
  wp_lam.
  wp_let.
  wp_lam.
  wp_pures.
  iDestruct "Hsl" as "(Hptr&%)".
  iDestruct (array_split 4 with "Hptr") as "[Henc Hrest]"; [ lia .. | ].
  wp_apply (wp_EncodeUInt32 with "[$Henc]").
  { iPureIntro.
    rewrite take_length; lia. }
  iIntros "Henc".
  change (Z.to_nat 4) with 4%nat.
  iDestruct (array_app with "[$Henc $Hrest]") as "Htogether".
  iApply "HΦ".
  iFrame.
  rewrite app_length drop_length u32_le_bytes_length.
  iPureIntro.
  lia.
Qed.

Hint Rewrite word.unsigned_or_nowrap : word.
Hint Rewrite word.unsigned_slu : word.

Theorem val_u32 z :
  0 <= z < 2 ^ 32 ->
  int.val (U32 z) = z.
Proof.
  intros.
  unfold U32.
  rewrite word.unsigned_of_Z.
  rewrite wrap_small; auto.
Qed.

Ltac eval_term t :=
  let t' := (eval cbv in t) in change t with t'.

Ltac eval_u32 :=
  match goal with
  | |- context[int.val (U32 ?z)] =>
    rewrite  (val_u32 z ltac:(lia))
  end.

Theorem u8_to_from_u32 x :
  int.val (u8_to_u32 (u8_from_u32 x)) =
  int.val x `mod` 2 ^ 8.
Proof.
  unfold u8_to_u32, u8_from_u32, U8, U32.
  autorewrite with word.
  rewrite word.unsigned_of_Z.
  rewrite word_wrap_wrap'; last lia.
  reflexivity.
Qed.

Lemma val_u8_to_u32 x :
  int.val (u8_to_u32 x) = int.val x.
Proof.
  unfold u8_to_u32, U32.
  rewrite word.unsigned_of_Z.
  pose proof (word.unsigned_range x).
  rewrite wrap_small; lia.
Qed.

Theorem decode_encode x :
  word.or (u8_to_u32 (word.of_Z (int.val x)))
        (word.slu
           (word.or (u8_to_u32 (word.of_Z (int.val x ≫ 8)))
              (word.slu
                 (word.or (u8_to_u32 (word.of_Z ((int.val x ≫ 8) ≫ 8)))
                    (word.slu (u8_to_u32 (word.of_Z (((int.val x ≫ 8) ≫ 8) ≫ 8))) (U32 8)))
                 (U32 8))) (U32 8)) = x.
Proof.
  apply word.unsigned_inj.
  pose proof (u32_le_to_word x).
  cbv [le_to_u32 u32_le map LittleEndian.combine LittleEndian.split length Datatypes.HList.tuple.to_list Datatypes.HList.tuple.of_list PrimitivePair.pair._1 PrimitivePair.pair._2] in H.
  rewrite Z.shiftl_0_l in H.
  rewrite Z.lor_0_r in H.
  rewrite ?word.unsigned_of_Z in H.
  rewrite word.unsigned_or_nowrap.
  rewrite word.unsigned_slu; eval_u32; try lia.
  rewrite word.unsigned_or_nowrap.
  rewrite word.unsigned_slu; eval_u32; try lia.
  rewrite word.unsigned_or_nowrap.
  rewrite word.unsigned_slu; eval_u32; try lia.
  rewrite ?val_u8_to_u32.
  rewrite <- H at 5.
  rewrite ?word.unsigned_of_Z.
Admitted.

Theorem wp_DecodeUInt32 (l: loc) (x: u32) s E :
  {{{ ▷ l ↦∗[byteT] (b2val <$> u32_le x) }}}
    DecodeUInt32 #l @ s ; E
  {{{ RET #x; l ↦∗[byteT] (b2val <$> u32_le x) }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  cbv [u32_le fmap list_fmap LittleEndian.split HList.tuple.to_list List.map].
  rewrite ?array_cons ?loc_add_assoc.
  iDestruct "Hl" as "(Hl0&Hl1&Hl2&Hl3&Hemp)".
  rewrite /DecodeUInt32.
  remember u8T.
  wp_pures.
  wp_apply (wp_LoadAt with "[Hl0]"); [ subst; iFrame | iIntros "Hl0" ].
  wp_apply (wp_LoadAt with "[Hl1]"); [ subst; iFrame | iIntros "Hl1" ].
  wp_apply (wp_LoadAt with "[Hl2]"); [ subst; iFrame | iIntros "Hl2" ].
  wp_apply (wp_LoadAt with "[Hl3]"); [ subst; iFrame | iIntros "Hl3" ].
  wp_pures.
  rewrite decode_encode.
  iApply "HΦ".
  subst; simpl.
  iFrame.
Qed.

Theorem wp_DecodeUInt64 (l: loc) (x: u64) s E :
  {{{ ▷ l ↦∗[byteT] (b2val <$> u64_le x) }}}
    DecodeUInt64 #l @ s ; E
  {{{ RET #x; l ↦∗[byteT] (b2val <$> u64_le x) }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  cbv [u64_le fmap list_fmap LittleEndian.split HList.tuple.to_list List.map].
  rewrite ?array_cons ?loc_add_assoc.
  iDestruct "Hl" as "(Hl0&Hl1&Hl2&Hl3&Hl4&Hl5&Hl6&Hl7&Hemp)".
  rewrite /DecodeUInt64.
  remember u8T.
  wp_apply (wp_LoadAt with "[Hl0]"); [ subst; iFrame | iIntros "Hl0" ].
  wp_apply (wp_LoadAt with "[Hl1]"); [ subst; iFrame | iIntros "Hl1" ].
  wp_apply (wp_LoadAt with "[Hl2]"); [ subst; iFrame | iIntros "Hl2" ].
  wp_apply (wp_LoadAt with "[Hl3]"); [ subst; iFrame | iIntros "Hl3" ].
  wp_apply (wp_LoadAt with "[Hl4]"); [ subst; iFrame | iIntros "Hl4" ].
  wp_apply (wp_LoadAt with "[Hl5]"); [ subst; iFrame | iIntros "Hl5" ].
  wp_apply (wp_LoadAt with "[Hl6]"); [ subst; iFrame | iIntros "Hl6" ].
  wp_apply (wp_LoadAt with "[Hl7]"); [ subst; iFrame | iIntros "Hl7" ].
  wp_pures.
  cbv [ty_size].
  rewrite ?Z.mul_1_l.
Admitted.

Theorem wp_UInt64Get stk E s (x: u64) vs :
  {{{ is_slice_small s byteT vs ∗ ⌜take 8 vs = u64_le_bytes x⌝ }}}
    UInt64Get (slice_val s) @ stk; E
  {{{ RET #x; is_slice_small s byteT (u64_le_bytes x ++ drop 8 vs) }}}.
Proof.
  iIntros (Φ) "[Hs %] HΦ".
  assert (vs = u64_le_bytes x ++ drop 8 vs).
  { rewrite -{1}(take_drop 8 vs).
    congruence. }
  rewrite [vs in is_slice_small _ _ vs](H0).
  wp_call.
  wp_apply wp_slice_ptr.
  iDestruct "Hs" as "(Hptr&%)".
  iDestruct (array_app with "Hptr") as "[Htake Hrest]"; try lia;
    rewrite u64_le_bytes_length.
  wp_apply (wp_DecodeUInt64 with "[$Htake]").
  iIntros "Htake".
  iDestruct (array_app with "[$Htake Hrest]") as "Hptr".
  { rewrite fmap_length u64_le_length.
    iFrame. }
  iApply "HΦ".
  iFrame.
  iPureIntro.
  rewrite app_length u64_le_bytes_length drop_length in H1 |- *.
  lia.
Qed.

Theorem wp_UInt64Get' stk E s (x: u64) :
  {{{ s.(Slice.ptr) ↦∗[byteT] u64_le_bytes x ∗ ⌜int.val s.(Slice.sz) >= 8⌝ }}}
    UInt64Get (slice_val s) @ stk; E
  {{{ RET #x; s.(Slice.ptr) ↦∗[byteT] u64_le_bytes x }}}.
Proof.
  iIntros (Φ) "[Ha %] HΦ".
  wp_call.
  wp_call.
  wp_apply (wp_DecodeUInt64 with "Ha").
  iApply "HΦ".
Qed.

Theorem wp_UInt32Get' stk E s (x: u32) :
  {{{ s.(Slice.ptr) ↦∗[byteT] u32_le_bytes x ∗ ⌜int.val s.(Slice.sz) >= 4⌝ }}}
    UInt32Get (slice_val s) @ stk; E
  {{{ RET #x; s.(Slice.ptr) ↦∗[byteT] u32_le_bytes x }}}.
Proof.
  iIntros (Φ) "[Ha %] HΦ".
  wp_call.
  wp_call.
  wp_apply (wp_DecodeUInt32 with "Ha").
  iApply "HΦ".
Qed.

End heap.
