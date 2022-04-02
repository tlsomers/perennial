From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.

From Perennial.program_proof.memkv Require Export memkv_shard_definitions memkv_put_proof memkv_conditional_put_proof memkv_get_proof memkv_install_shard_proof memkv_getcid_proof memkv_move_shard_proof common_proof.

Section memkv_shard_start_proof.

Context `{!heapGS Σ, rpcG Σ ShardReplyC, rpcregG Σ, kvMapG Σ}.

Lemma wp_KVShardServer__Start (s:loc) (host : u64) γ :
handlers_dom γ.(urpc_gn) {[ U64 0; U64 1; U64 2; U64 3; U64 4; U64 5 ]} -∗
is_shard_server host γ -∗
is_KVShardServer s γ -∗
  {{{
       True
  }}}
    KVShardServer__Start #s #host
  {{{
       RET #(); True
  }}}.
Proof.
  iIntros "#Hdom #His_shard #His_memkv !#" (Φ) "_ HΦ".
  wp_lam.
  wp_pures.
  wp_apply map.wp_NewMap.
  iIntros (handlers_ptr) "Hmap".
  wp_pures.

  wp_apply (map.wp_MapInsert with "Hmap").
  iIntros "Hmap".
  wp_pures.

  wp_apply (map.wp_MapInsert with "Hmap").
  iIntros "Hmap".
  wp_pures.

  wp_apply (map.wp_MapInsert with "Hmap").
  iIntros "Hmap".
  wp_pures.

  wp_apply (map.wp_MapInsert with "Hmap").
  iIntros "Hmap".
  wp_pures.

  wp_apply (map.wp_MapInsert with "Hmap").
  iIntros "Hmap".
  wp_pures.

  wp_apply (map.wp_MapInsert with "Hmap").
  iIntros "Hmap".
  wp_pures.

  wp_apply (wp_MakeServer with "[$Hmap]").
  iIntros (rs) "Hsown".
  wp_pures.

  rewrite is_shard_server_unfold.
  iNamed "His_shard".
  wp_apply (wp_StartServer with "[$Hsown]").
  { rewrite ?dom_insert_L; set_solver. }
  {
    iSplitL "".
    { rewrite /handlers_complete.
      rewrite ?dom_insert_L dom_empty_L. iExactEq "Hdom". f_equal. set_solver. }
    iApply (big_sepM_insert_2 with "").
    { (* MoveShardRPC handler_is *)
      simpl. iExists _.
      iFrame "#HmoveSpec".

      clear Φ.
      iIntros (??????) "!#".
      iIntros (Φ) "Hpre HΦ".
      wp_pures.
      iDestruct "Hpre" as "(Hreq_sl & Hrep & _ & Hargs)".
      simpl. iDestruct "Hargs" as (x) "[Hargs Hpost]".
      iDestruct "Hargs" as (?) "(%HencArgs & %HsidLe & #Hdst_is_shard)".
      wp_apply (wp_decodeMoveShardRequest with "[$Hreq_sl]").
      { done. }
      iIntros (args_ptr) "Hargs".
      wp_apply (wp_MoveShardRPC with "His_memkv [$Hargs $Hdst_is_shard]").
      { done. }
      wp_pures.
      wp_apply (typed_slice.wp_NewSlice (V:=u8)).
      iIntros (rep_sl) "Hrep_sl".
      iDestruct (is_slice_to_small with "Hrep_sl") as "Hrep_sl".
      wp_store.
      iApply "HΦ".
      iFrame.
      by iApply "Hpost".
    }

    iApply (big_sepM_insert_2 with "").
    { (* InstallShard() handler_is *)
      iExists _.
      iFrame "#HinstallSpec".

      clear Φ.
      iIntros (??????) "!#".
      iIntros (Φ) "Hpre HΦ".
      wp_pures.

      iDestruct "Hpre" as "(Hpre_sl & Hrep & _ & Hpre)".
      iDestruct "Hpre" as (x) "[Hpre Hpost]".
      iDestruct "Hpre" as (?) "(%Hargs_enc & %HsidLe & HreqInv)".
      wp_apply (wp_decodeInstallShardRequest with "[$Hpre_sl]").
      { done. }
      iIntros (args_ptr) "Hargs".
      wp_apply (wp_InstallShardRPC with "His_memkv [$Hargs $HreqInv]").
      {
        iPureIntro.
        word.
      }
      wp_pures.
      wp_apply (typed_slice.wp_NewSlice (V:=u8)).
      iIntros (reply_sl) "Hrep_sl".
      iDestruct (is_slice_to_small with "Hrep_sl") as "Hrep_sl".
      wp_store.
      iApply "HΦ".
      iFrame.
      iApply "Hpost". by iFrame.
    }

    iApply (big_sepM_insert_2 with "").
    { (* ConditionalPutRPC handler_is *)
      simpl.
      iExists _. iFrame "HconditionalPutSpec".

      clear Φ.
      iIntros (??????) "!#".
      iIntros (Φ) "Hpre HΦ".
      wp_pures.
      wp_apply (wp_allocStruct).
      {
        naive_solver.
      }
      iIntros (rep_ptr) "Hrep".
      wp_pures.
      iDestruct "Hpre" as "(Hreq_sl & Hrep_ptr & _ & Hpre)".
      iSimpl in "Hpre". iDestruct "Hpre" as ([[Q γreq] req1]) "[Hpre Hpost]".
      iDestruct "Hpre" as "(%Henc & #HreqInv)".
      wp_apply (wp_DecodeConditionalPutRequest with "[$Hreq_sl]").
      { done. }
      iIntros (args_ptr expv_sl newv) "Hargs".
      wp_apply (wp_ConditionalPutRPC with "His_memkv [$Hargs Hrep HreqInv]").
      {
        iFrame "HreqInv".
        iDestruct (struct_fields_split with "Hrep") as "HH".
        iNamed "HH".
        iExists (mkConditionalPutReplyC _ _).
        iFrame.
      }
      iIntros (rep') "[Hrep Hpost']".
      wp_pures.
      wp_apply (wp_EncodeConditionalPutReply with "Hrep").
      iIntros (repData rep_sl) "[Hrep_sl %HrepEnc]".
      iDestruct (is_slice_to_small with "Hrep_sl") as "Hrep_sl".
      wp_store.
      iApply "HΦ". iFrame. iApply "Hpost".
      iModIntro.
      iExists _; by iFrame.
    }

    iApply (big_sepM_insert_2 with "").
    { (* Get() handler_is *)
      simpl.
      iExists _; iFrame "HgetSpec".

      clear Φ.
      iIntros (??????) "!#".
      iIntros (Φ) "Hpre HΦ".
      wp_pures.
      wp_apply (wp_allocStruct).
      { val_ty. }
      iIntros (rep_ptr) "Hrep".
      wp_pures.
      iDestruct "Hpre" as "(Hreq_sl & Hrep_ptr & _ & Hpre)".
      iSimpl in "Hpre". iDestruct "Hpre" as ([[Q γreq] req1]) "[Hpre Hpost]".
      iDestruct "Hpre" as "(%Henc & #HreqInv)".
      wp_apply (wp_DecodeGetRequest with "[$Hreq_sl]").
      { done. }
      iIntros (args_ptr) "Hargs".
      iDestruct (typed_slice.is_slice_zero byteT 1%Qp) as "Hzero_sl".
      iDestruct (typed_slice.is_slice_small_acc with "Hzero_sl") as "{Hzero_sl} [Hzero_sl _]".
      iMod (readonly_alloc_1 with "Hzero_sl") as "{Hzero_sl} Hzero_sl".
      wp_apply (wp_GetRPC with "His_memkv [$Hargs Hrep HreqInv Hzero_sl]").
      {
        iFrame "HreqInv".
        rewrite 2!zero_prod_val zero_slice_val.

        iDestruct (struct_fields_split with "Hrep") as "HH".
        iNamed "HH".
        iExists (mkGetReplyC _ []).
        iFrame.
        iExists (Slice.nil).
        iFrame.
      }
      iIntros (rep') "[Hrep Hpost']".
      wp_pures.
      wp_apply (wp_EncodeGetReply with "Hrep").
      iIntros (repData rep_sl) "[Hrep_sl %HrepEnc]".
      iDestruct (is_slice_to_small with "Hrep_sl") as "Hrep_sl".
      wp_store.
      iApply "HΦ". iFrame. iApply "Hpost".
      iModIntro.
      iExists _; by iFrame.
    }

    iApply (big_sepM_insert_2 with "").
    { (* PutRPC handler_is *)
      simpl.
      iExists _. iFrame "HputSpec".

      clear Φ.
      iIntros (??????) "!#".
      iIntros (Φ) "Hpre HΦ".
      wp_pures.
      wp_apply (wp_allocStruct).
      {
        naive_solver.
      }
      iIntros (rep_ptr) "Hrep".
      wp_pures.
      iDestruct "Hpre" as "(Hreq_sl & Hrep_ptr & _ & Hpre)".
      iSimpl in "Hpre". iDestruct "Hpre" as ([[Q γreq] req1]) "[Hpre Hpost]".
      iDestruct "Hpre" as "(%Henc & #HreqInv)".
      wp_apply (wp_DecodePutRequest with "[$Hreq_sl]").
      { done. }
      iIntros (args_ptr val_sl) "Hargs".
      wp_apply (wp_PutRPC with "His_memkv [$Hargs Hrep HreqInv]").
      {
        iFrame "HreqInv".
        iDestruct (struct_fields_split with "Hrep") as "HH".
        iNamed "HH".
        iExists (mkPutReplyC _).
        iFrame.
      }
      iIntros (rep') "[Hrep Hpost']".
      wp_pures.
      wp_apply (wp_EncodePutReply with "Hrep").
      iIntros (repData rep_sl) "[Hrep_sl %HrepEnc]".
      iDestruct (is_slice_to_small with "Hrep_sl") as "Hrep_sl".
      wp_store.
      iApply "HΦ". iFrame. iApply "Hpost".
      iModIntro.
      iExists _; by iFrame.
    }

    iApply (big_sepM_insert_2 with "").
    { (* GetCIDRPC handler_is *)
      iExists _.
      iFrame "HfreshSpec".

      clear Φ.
      iIntros (??????) "!#".
      iIntros (Φ) "Hpre HΦ".
      wp_pures.
      wp_apply (wp_GetCIDRPC with "His_memkv").
      iIntros (cid) "Hcid".
      wp_apply (wp_EncodeUint64).
      iIntros (rep_sl repData) "[Hrep_sl %HrepEnc]".
      iDestruct (is_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iDestruct "Hpre" as "(Hreq_sl & Hrep & _ & Hpre)".
      iSimpl in "Hpre". iDestruct "Hpre" as (_) "[_ Hpost]".
      wp_store.
      iApply "HΦ".
      iFrame.
      iApply "Hpost".
      iExists _; by iFrame.
    }

    iApply big_sepM_empty.
    done.
  }
  wp_pures. by iApply "HΦ".
Qed.

End memkv_shard_start_proof.
