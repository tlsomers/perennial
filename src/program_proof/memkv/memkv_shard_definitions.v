From Perennial.program_proof Require Import grove_prelude.
From iris.bi.lib Require Import fixpoint.
From Perennial.goose_lang Require Import adequacy.
From Perennial.goose_lang Require Import dist_lifting.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.memkv Require Export common_proof.
From Perennial.program_proof.memkv Require Export urpc_lib urpc_proof urpc_spec connman_proof memkv_ghost memkv_marshal_put_proof memkv_marshal_get_proof memkv_marshal_conditional_put_proof memkv_marshal_install_shard_proof memkv_marshal_getcid_proof memkv_marshal_move_shard_proof.

(** "universal" reply type for the reply cache *)
Record ShardReplyC := mkShardReplyC {
  SR_Err : u64;
  SR_Value : list u8;
  SR_Success : bool;
}.

Section memkv_shard_pre_definitions.

Context `{rpcG Σ ShardReplyC, rpcregG Σ, kvMapG Σ}.
Context `{!gooseGlobalGS Σ}.

Definition uKV_FRESHCID: nat :=
  Eval vm_compute in match KV_FRESHCID with LitV (LitInt n) => int.nat n | _ => 0 end.
Definition uKV_PUT: nat :=
  Eval vm_compute in match KV_PUT with LitV (LitInt n) => int.nat n | _ => 0 end.
Definition uKV_CONDITIONAL_PUT: nat :=
  Eval vm_compute in match KV_CONDITIONAL_PUT with LitV (LitInt n) => int.nat n | _ => 0 end.
Definition uKV_GET: nat :=
  Eval vm_compute in match KV_GET with LitV (LitInt n) => int.nat n | _ => 0 end.
Definition uKV_INS_SHARD: nat :=
  Eval vm_compute in match KV_INS_SHARD with LitV (LitInt n) => int.nat n | _ => 0 end.
Definition uKV_MOV_SHARD: nat :=
  Eval vm_compute in match KV_MOV_SHARD with LitV (LitInt n) => int.nat n | _ => 0 end.

Record memkv_shard_names := {
 rpc_gn : rpc_names ;
 urpc_gn : server_chan_gnames ;
 kv_gn : gname
}
.

Implicit Type γ : memkv_shard_names.

Definition PreShardGet γkv key Q : iProp Σ :=
  |={⊤,∅}=> (∃ v, kvptsto γkv key v ∗ (kvptsto γkv key v -∗ |={∅,⊤}=> Q v)).
Definition PostShardGet γkv (key:u64) Q (rep:ShardReplyC) : iProp Σ :=
  ⌜rep.(SR_Err) ≠ 0⌝ ∗ (PreShardGet γkv key Q) ∨ ⌜rep.(SR_Err) = 0⌝ ∗ (Q rep.(SR_Value)).
Definition is_shard_server_getSpec γkv γrpc : RPCSpec :=
  {| spec_rpcid := uKV_GET;
     spec_ty := ((list u8 → iProp Σ) * rpc_request_names * GetRequestC);
     spec_Pre := (λ '(Q, γreq, req) reqData, ⌜has_encoding_GetRequest reqData req⌝ ∗
                  is_RPCRequest γrpc γreq
                    (PreShardGet γkv req.(GR_Key) Q)
                    (PostShardGet γkv req.(GR_Key) Q)
                    {| Req_CID:=req.(GR_CID); Req_Seq:=req.(GR_Seq) |}
             )%I;
     spec_Post :=(λ '(Q, γreq, req) reqData repData, ∃ rep, ⌜has_encoding_GetReply repData rep⌝ ∗
                  (RPCRequestStale γrpc {| Req_CID:=req.(GR_CID); Req_Seq:=req.(GR_Seq) |} ∨
                    ∃ dummy_succ, RPCReplyReceipt γrpc {| Req_CID:=req.(GR_CID); Req_Seq:=req.(GR_Seq) |} (mkShardReplyC rep.(GR_Err) rep.(GR_Value) dummy_succ))
             )%I |}.

Definition PreShardPut γkv key Q v : iProp Σ :=
  |={⊤,∅}=> (∃ oldv, kvptsto γkv key oldv ∗ (kvptsto γkv key v -∗ |={∅,⊤}=> Q)).
Definition PostShardPut γkv (key:u64) Q v (rep:ShardReplyC) : iProp Σ :=
  ⌜rep.(SR_Err) ≠ 0⌝ ∗ (PreShardPut γkv key Q v) ∨ ⌜rep.(SR_Err) = 0⌝ ∗ Q .
Definition is_shard_server_putSpec (γkv : gname) γrpc : RPCSpec :=
  {| spec_rpcid := uKV_PUT;
     spec_ty := (iProp Σ * rpc_request_names * PutRequestC)%type;
     spec_Pre := (λ '(Q, γreq, req) reqData, ⌜has_encoding_PutRequest reqData req⌝ ∗
                  is_RPCRequest γrpc γreq
                     (PreShardPut γkv req.(PR_Key) Q req.(PR_Value))
                     (PostShardPut γkv req.(PR_Key) Q req.(PR_Value))
                     {| Req_CID:=req.(PR_CID); Req_Seq:=req.(PR_Seq) |}
             )%I;
     spec_Post := (λ '(Q, γreq, req) reqData repData, ∃ rep, ⌜has_encoding_PutReply repData rep⌝ ∗
                  (RPCRequestStale γrpc {| Req_CID:=req.(PR_CID); Req_Seq:=req.(PR_Seq) |} ∨
                    ∃ dummy_val dummy_succ, RPCReplyReceipt γrpc {| Req_CID:=req.(PR_CID); Req_Seq:=req.(PR_Seq) |} (mkShardReplyC rep.(PR_Err) dummy_val dummy_succ))
             )%I |}.

Definition PreShardConditionalPut γkv key Q expv newv : iProp Σ :=
  |={⊤,∅}=> (∃ oldv, kvptsto γkv key oldv ∗
    (let succ := bool_decide (expv = oldv) in kvptsto γkv key (if succ then newv else oldv) -∗
      |={∅,⊤}=> Q succ)).
Definition PostShardConditionalPut γkv (key:u64) Q expv newv (rep:ShardReplyC) : iProp Σ :=
  ⌜rep.(SR_Err) ≠ 0⌝ ∗ (PreShardConditionalPut γkv key Q expv newv) ∨ ⌜rep.(SR_Err) = 0⌝ ∗ Q rep.(SR_Success).
Definition is_shard_server_conditionalPutSpec γkv γrpc : RPCSpec :=
  {| spec_rpcid := uKV_CONDITIONAL_PUT;
     spec_ty := ((bool → iProp Σ) * rpc_request_names * ConditionalPutRequestC);
     spec_Pre :=(λ '(Q, γreq, req) reqData, ⌜has_encoding_ConditionalPutRequest reqData req⌝ ∗
                  is_RPCRequest γrpc γreq
                     (PreShardConditionalPut γkv req.(CPR_Key) Q req.(CPR_ExpValue) req.(CPR_NewValue))
                     (PostShardConditionalPut γkv req.(CPR_Key) Q req.(CPR_ExpValue) req.(CPR_NewValue))
                     {| Req_CID:=req.(CPR_CID); Req_Seq:=req.(CPR_Seq) |}
             )%I;
     spec_Post :=(λ '(Q, γreq, req) reqData repData, ∃ rep, ⌜has_encoding_ConditionalPutReply repData rep⌝ ∗
                  (RPCRequestStale γrpc {| Req_CID:=req.(CPR_CID); Req_Seq:=req.(CPR_Seq) |} ∨
                    ∃ dummy_val, RPCReplyReceipt γrpc {| Req_CID:=req.(CPR_CID); Req_Seq:=req.(CPR_Seq) |} (mkShardReplyC rep.(CPR_Err) dummy_val rep.(CPR_Succ)))
             )%I |}.

Definition is_shard_server_installSpec γkv γrpc : RPCSpec :=
  {| spec_rpcid := uKV_INS_SHARD;
     spec_ty := rpc_request_names;
     spec_Pre := (λ x reqData, ∃ args, ⌜has_encoding_InstallShardRequest reqData args⌝ ∗
                                  ⌜int.Z args.(IR_Sid) < uNSHARD⌝ ∗
                                  is_RPCRequest γrpc x (own_shard γkv args.(IR_Sid) args.(IR_Kvs))
                                                            (λ _, True)
                                                            {| Req_CID:=args.(IR_CID); Req_Seq:=args.(IR_Seq) |}
             )%I;
     spec_Post := (λ x reqData repData, True)%I |}.

Definition is_shard_server_freshSpec γrpc : RPCSpec :=
  {| spec_rpcid := uKV_FRESHCID;
     spec_ty := unit;
     spec_Pre := (λ x reqData, True)%I;
     spec_Post := (λ x reqData repData, ∃ cid, ⌜has_encoding_Uint64 repData cid⌝ ∗
              RPCClient_own_ghost γrpc cid 1)%I |}.

Definition is_shard_server_moveSpec_pre γkv (ρ:u64 -d> memkv_shard_names -d> iPropO Σ) : RPCSpec :=
  {| spec_rpcid := uKV_MOV_SHARD;
     spec_ty := memkv_shard_names;
     spec_Pre :=(λ x reqData, ∃ args, ⌜has_encoding_MoveShardRequest reqData args⌝ ∗
                                  ⌜int.Z args.(MR_Sid) < uNSHARD⌝ ∗
                                  (▷ ρ args.(MR_Dst) x) ∗
                                  ⌜ x.(kv_gn) = γkv ⌝
             )%I;
     spec_Post := (λ x reqData repData, True)%I |}.

Definition is_shard_server_pre (ρ:u64 -d> memkv_shard_names -d> iPropO Σ) : (u64 -d> memkv_shard_names -d> iPropO Σ) :=
  (λ host γ,
  "#His_rpc" ∷ is_RPCServer γ.(rpc_gn) ∗
  "#HputSpec" ∷ handler_rpc_spec γ.(urpc_gn) host (is_shard_server_putSpec γ.(kv_gn) γ.(rpc_gn)) ∗
  "#HconditionalPutSpec" ∷ handler_rpc_spec γ.(urpc_gn) host (is_shard_server_conditionalPutSpec γ.(kv_gn) γ.(rpc_gn)) ∗
  "#HgetSpec" ∷ handler_rpc_spec γ.(urpc_gn) host (is_shard_server_getSpec γ.(kv_gn) γ.(rpc_gn)) ∗
  "#HmoveSpec" ∷ handler_rpc_spec γ.(urpc_gn) host (is_shard_server_moveSpec_pre γ.(kv_gn) ρ) ∗
  "#HinstallSpec" ∷ handler_rpc_spec γ.(urpc_gn) host (is_shard_server_installSpec γ.(kv_gn) γ.(rpc_gn)) ∗
  "#HfreshSpec" ∷ handler_rpc_spec γ.(urpc_gn) host (is_shard_server_freshSpec γ.(rpc_gn))
)%I.

(* Actually, handler_is is contractive now so we can remove the ▷ in is_shard_server *)
Instance is_shard_server_pre_contr : Contractive is_shard_server_pre.
Proof.
  rewrite /is_shard_server_pre=> n is1 is2 Hpre host γ.
  do 4 (f_contractive || f_equiv).
  f_equiv. rewrite /handler_rpc_spec /handler_spec. (* FIXME unfolding other abstractions *)
  do 10 f_equiv.
  unfold named.
  apply saved_spec.saved_spec_own_contractive.
  rewrite /dist_later. destruct n; auto.
  intros => ?.
  rewrite /RPCSpec_Spec /is_shard_server_moveSpec_pre /=.
  intros Φ. simpl.
  repeat f_equiv.
Qed.

Definition is_shard_server_def :=
  fixpoint (is_shard_server_pre).
Definition is_shard_server_aux : seal (is_shard_server_def). by eexists. Qed.
Definition is_shard_server := is_shard_server_aux.(unseal).
Definition is_shard_server_eq : is_shard_server = is_shard_server_def := is_shard_server_aux.(seal_eq).

Definition is_shard_server_moveSpec γkv := is_shard_server_moveSpec_pre γkv is_shard_server.

Lemma is_shard_server_unfold host γ :
  is_shard_server host γ ⊣⊢ is_shard_server_pre (is_shard_server) host γ
.
Proof.
  rewrite is_shard_server_eq. apply (fixpoint_unfold (is_shard_server_pre)).
Qed.

Global Instance is_shard_server_pers host γ : Persistent (is_shard_server host γ).
Proof.
  rewrite is_shard_server_unfold.
  apply _.
Qed.
End memkv_shard_pre_definitions.

Section memkv_shard_definitions.

Context `{!heapGS Σ (ext:=grove_op) (ffi:=grove_model), rpcG Σ ShardReplyC, rpcregG Σ, kvMapG Σ}.

Definition own_KVShardClerk (ck:loc) γkv : iProp Σ :=
  ∃ (cid seq:u64) (c:loc) (host:u64) (γ:memkv_shard_names),
    "Hcid" ∷ ck ↦[KVShardClerk :: "cid"] #cid ∗
    "Hseq" ∷ ck ↦[KVShardClerk :: "seq"] #seq ∗
    "Hc" ∷ ck ↦[KVShardClerk :: "c"] #c ∗
    "Hhost" ∷ ck ↦[KVShardClerk :: "host"] #host ∗
    "Hcrpc" ∷ RPCClient_own_ghost γ.(rpc_gn) cid seq ∗
    "#Hc_own" ∷ is_ConnMan c ∗
    "#His_shard" ∷ is_shard_server host γ ∗
    "%HseqPostitive" ∷ ⌜0%Z < int.Z seq⌝%Z ∗
    "%Hγeq" ∷ ⌜γ.(kv_gn) = γkv⌝
.

Definition memKVN := nroot .@ "memkv".

Definition own_KVShardServer (s:loc) γ : iProp Σ :=
  ∃ (lastReply_ptr lastSeq_ptr peers_ptr:loc) (kvss_sl shardMap_sl:Slice.t)
    (lastReplyM:gmap u64 ShardReplyC) (lastReplyMV:gmap u64 goose_lang.val) (lastSeqM:gmap u64 u64) (nextCID:u64) (shardMapping:list bool) (kvs_ptrs:list loc)
    (peersM:gmap u64 loc),
  "HlastReply" ∷ s ↦[KVShardServer :: "lastReply"] #lastReply_ptr ∗
  "HlastReplyMap" ∷ map.is_map lastReply_ptr 1 (lastReplyMV, zero_val (struct.t ShardReply)) ∗ (* TODO: default *)
  "%HlastReplyMVdom" ∷ ⌜dom (gset u64) lastReplyMV = dom (gset u64) lastSeqM⌝ ∗
  "HlastReply_structs" ∷ ([∗ map] k ↦ v;rep ∈ lastReplyMV ; lastReplyM,
    (∃ val_sl q, ⌜v = struct.mk_f ShardReply [
              "Err" ::= #rep.(SR_Err);
              "Value" ::= slice_val val_sl;
              "Success" ::= #rep.(SR_Success)
            ]%V⌝ ∗ typed_slice.is_slice_small val_sl byteT q rep.(SR_Value))) ∗
  "HlastSeq" ∷ s ↦[KVShardServer :: "lastSeq"] #lastSeq_ptr ∗
  "HlastSeqMap" ∷ is_map lastSeq_ptr 1 lastSeqM ∗
  "HnextCID" ∷ s ↦[KVShardServer :: "nextCID"] #nextCID ∗
  "HshardMap" ∷ s ↦[KVShardServer :: "shardMap"] (slice_val shardMap_sl) ∗
  "HshardMap_sl" ∷ typed_slice.is_slice shardMap_sl boolT 1%Qp shardMapping ∗
  "Hkvss" ∷ s ↦[KVShardServer :: "kvss"] (slice_val kvss_sl) ∗
  "Hkvss_sl" ∷ slice.is_slice kvss_sl (mapT (slice.T byteT)) 1%Qp (fmap (λ x:loc, #x) kvs_ptrs) ∗
  "Hpeers" ∷ s ↦[KVShardServer :: "peers"] #peers_ptr ∗
  "Hrpc" ∷ RPCServer_own_ghost γ.(rpc_gn) lastSeqM lastReplyM ∗
  "%HshardMapLength" ∷ ⌜Z.of_nat (length shardMapping) = uNSHARD⌝ ∗
  "%HkvssLength" ∷ ⌜Z.of_nat (length kvs_ptrs) = uNSHARD⌝ ∗
  "HownShards" ∷ ([∗ set] sid ∈ (fin_to_set u64),
                  ⌜(shardMapping !! (int.nat sid)) ≠ Some true⌝ ∨
                  (∃ (kvs_ptr:loc) (m:gmap u64 (list u8)) (mv:gmap u64 goose_lang.val),
                      own_shard γ.(kv_gn) sid m ∗ (* own shard *)
                      ⌜kvs_ptrs !! (int.nat sid) = Some kvs_ptr⌝ ∗
                      ⌜dom (gset _) m = dom (gset _) mv⌝ ∗
                      map.is_map kvs_ptr 1 (mv, (slice_val Slice.nil)) ∗
                      ([∗ set] k ∈ (fin_to_set u64),
                       ⌜shardOfC k ≠ sid ∧ mv !! k = None ∧ m !! k = None ⌝ ∨ (∃ q vsl, ⌜default (slice_val Slice.nil) (mv !! k) = (slice_val vsl)⌝ ∗ typed_slice.is_slice_small vsl byteT q (default [] (m !! k))) )
                  )
                 ) ∗
  "HpeersMap" ∷ is_map (V:=loc) peers_ptr 1 peersM ∗
  "HpeerClerks" ∷ ([∗ map] k ↦ ck ∈ peersM, own_KVShardClerk ck γ.(kv_gn)) ∗
  "Hcids" ∷ [∗ set] cid ∈ (fin_to_set u64), ⌜int.Z cid < int.Z nextCID⌝%Z ∨ (RPCClient_own_ghost γ.(rpc_gn) cid 1)
.

Definition is_KVShardServer (s:loc) γ : iProp Σ :=
  ∃ mu (cm:loc),
  "#His_srv" ∷ is_RPCServer γ.(rpc_gn) ∗
  "#Hmu" ∷ readonly (s ↦[KVShardServer :: "mu"] mu) ∗
  "#Hcm" ∷ readonly (s ↦[KVShardServer :: "cm"] #cm) ∗
  "#HmuInv" ∷ is_lock memKVN mu (own_KVShardServer s γ) ∗
  "#Hiscm" ∷ is_ConnMan cm
.

End memkv_shard_definitions.
