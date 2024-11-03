From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.pure Require Import list.
From Perennial.program_proof.tulip Require Import base cmd res stability.
(* TODO: might be better to separate out the common definitions from [inv_group]. *)
From Perennial.program_proof.tulip Require Import inv_group.

Section inv.
  Context `{!tulip_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : tulip_names).

  Definition validated_pwrs_of_txn γ gid rid vts : iProp Σ :=
    ∃ pwrs, is_txn_pwrs γ gid vts pwrs ∗
            ([∗ set] key ∈ dom pwrs, is_replica_key_validated_at γ gid rid key vts).

  Definition group_aborted_if_validated
    γ gid (kvdm : gmap dbkey (list bool)) (histm : gmap dbkey dbhist)
    (ptsm : gmap dbkey nat) : iProp Σ :=
    ∀ k ts,
    match kvdm !! k, histm !! k, ptsm !! k with
    | Some vdl, Some hist, Some pts =>
        match vdl !! ts with
        | Some true => if decide ((length hist ≤ ts)%nat ∧ ts ≠ pts)
                      then is_group_aborted γ gid ts
                      else True
        | _ => True
        end
    | _, _, _ => True
    end.

  (* TODO: Remove "_cpm" if we can also remove [stm] in the group invariant. *)
  Definition prepared_impl_locked_cpm (cpm : gmap nat dbmap) (ptsm : gmap dbkey nat) :=
    ∀ ts pwrs key,
    cpm !! ts = Some pwrs ->
    key ∈ dom pwrs ->
    ptsm !! key = Some ts.

  Lemma prepared_impl_locked_disjoint cpm ptsm t1 t2 pwrs1 pwrs2 :
    t1 ≠ t2 ->
    cpm !! t1 = Some pwrs1 ->
    cpm !! t2 = Some pwrs2 ->
    prepared_impl_locked_cpm cpm ptsm ->
    dom pwrs1 ## dom pwrs2.
  Proof.
    intros Hne Hpwrs1 Hpwrs2 Hpil.
    rewrite elem_of_disjoint.
    intros Hk Hin1 Hin2.
    pose proof (Hpil _ _ _ Hpwrs1 Hin1) as Ht1.
    pose proof (Hpil _ _ _ Hpwrs2 Hin2) as Ht2.
    rewrite Ht1 in Ht2.
    inv Ht2.
  Qed.

  Definition safe_ballot γ gid ts l : iProp Σ :=
    [∗ list] r ↦ b ∈ l, match b with
                        | Accept p => is_group_prepare_proposal γ gid ts r p
                        | _ => True
                        end.

  Definition replica_inv_ballot_map γ gid rid bm : iProp Σ :=
    "Hblt"      ∷ own_replica_ballot_map γ gid rid bm ∗
    "#Hsafebm"  ∷ ([∗ map] ts ↦ l ∈ bm, safe_ballot γ gid ts l).

  Definition replica_inv_internal
    γ (gid rid : u64) (clog : dblog) (ilog : list (nat * icommand))
    (cm : gmap nat bool) (cpm : gmap nat dbmap) : iProp Σ :=
    ∃ (vtss : gset nat) (kvdm : gmap dbkey (list bool)) (bm : gmap nat ballot)
      (histm : gmap dbkey dbhist) (ptgsm : gmap nat (gset u64)) (sptsm ptsm : gmap dbkey nat),
      let log := merge_clog_ilog clog ilog in
      "Hvtss"     ∷ own_replica_validated_tss γ gid rid vtss ∗
      "Hclog"     ∷ own_replica_clog_half γ rid clog ∗
      "Hilog"     ∷ own_replica_ilog_half γ rid ilog ∗
      "Hkvdm"     ∷ ([∗ map] k ↦ vd ∈ kvdm, own_replica_key_validation γ gid rid k vd) ∗
      "Hbm"       ∷ replica_inv_ballot_map γ gid rid bm ∗
      "#Hsafep"   ∷ ([∗ map] ts ↦ pwrs ∈ cpm, safe_txn_pwrs γ gid ts pwrs) ∗
      "#Hvpwrs"   ∷ ([∗ set] ts ∈ vtss, validated_pwrs_of_txn γ gid rid ts) ∗
      "#Hgabt"    ∷ group_aborted_if_validated γ gid kvdm histm ptsm ∗
      "#Hcloglb"  ∷ is_txn_log_lb γ gid clog ∗
      "%Hrsm"     ∷ ⌜execute_cmds log = LocalState cm histm cpm ptgsm sptsm ptsm⌝ ∗
      "%Hvtss"    ∷ ⌜vtss ⊆ dom cm ∪ dom cpm⌝ ∗
      "%Hdomkvdm" ∷ ⌜dom kvdm = keys_all⌝ ∗
      "%Hlenkvd"  ∷ ⌜map_Forall2 (λ _ vd spts, length vd = spts) kvdm sptsm⌝ ∗
      "%Hsptsmlk" ∷ ⌜map_Forall2 (λ _ spts pts, pts ≠ O -> spts = S pts) sptsm ptsm⌝ ∗
      "%Hpil"     ∷ ⌜prepared_impl_locked_cpm cpm ptsm⌝ ∗
      "%Hcpmnz"   ∷ ⌜cpm !! O = None⌝.

  Definition replica_inv_with_cm_with_cpm
    γ (gid rid : u64) (cm : gmap nat bool) (cpm : gmap nat dbmap) : iProp Σ :=
    ∃ clog ilog, "Hrp" ∷ replica_inv_internal γ gid rid clog ilog cm cpm.

  (* TODO: check if this is actually needed *)
  Definition replica_inv_with_clog_with_ilog
    γ (gid rid : u64) (clog : dblog) (ilog : list (nat * icommand)) : iProp Σ :=
    ∃ cm cpm, "Hrp" ∷ replica_inv_internal γ gid rid clog ilog cm cpm.

  Definition replica_inv γ (gid rid : u64) : iProp Σ :=
    ∃ clog ilog cm cpm, "Hrp" ∷ replica_inv_internal γ gid rid clog ilog cm cpm.

  Definition replica_inv_xfinalized γ (gid rid : u64) (ptsm : gset nat) : iProp Σ :=
    ∃ cm cpm,
      "Hrp"      ∷ replica_inv_with_cm_with_cpm γ gid rid cm cpm ∗
      "%Hxfinal" ∷ ⌜set_Forall (λ t, cm !! t = None) ptsm⌝.

  Lemma replica_inv_xfinalized_empty γ gid rid :
    replica_inv γ gid rid -∗
    replica_inv_xfinalized γ gid rid ∅.
  Proof. iNamed 1. iFrame. iPureIntro. apply set_Forall_empty. Qed.

  Lemma replicas_inv_xfinalized_empty γ gid rids :
    ([∗ set] rid ∈ rids, replica_inv γ gid rid) -∗
    ([∗ set] rid ∈ rids, replica_inv_xfinalized γ gid rid ∅).
  Proof.
    iIntros "Hreplicas".
    iApply (big_sepS_mono with "Hreplicas").
    iIntros (rid Hrid).
    iApply replica_inv_xfinalized_empty.
  Qed.

  Lemma replica_inv_xfinalized_validated_impl_prepared
    γ gid rid cm cpm (tss : gset nat) ts :
    set_Forall (λ t, cm !! t = None) tss ->
    ts ∈ tss ->
    is_replica_validated_ts γ gid rid ts -∗
    replica_inv_with_cm_with_cpm γ gid rid cm cpm -∗
    ⌜∃ pwrs, cpm !! ts = Some pwrs⌝.
  Proof.
    iIntros (Hxfinal Hin) "Hvd Hrp".
    do 2 iNamed "Hrp".
    iDestruct (replica_validated_ts_elem_of with "Hvd Hvtss") as %Hinvtss.
    destruct (cpm !! ts) as [pwrs |] eqn:Hpwrs; first by eauto.
    exfalso.
    specialize (Hxfinal _ Hin).
    apply not_elem_of_dom in Hpwrs, Hxfinal.
    clear -Hpwrs Hxfinal Hvtss Hinvtss.
    set_solver.
  Qed.

  Lemma replica_inv_validated_keys_of_txn γ gid rid ts :
    is_replica_validated_ts γ gid rid ts -∗
    replica_inv γ gid rid -∗
    validated_pwrs_of_txn γ gid rid ts.
  Proof.
    iIntros "#Hvd Hrp".
    do 2 iNamed "Hrp".
    iDestruct (replica_validated_ts_elem_of with "Hvd Hvtss") as %Hinvtss.
    by iDestruct (big_sepS_elem_of with "Hvpwrs") as "Hvts"; first apply Hinvtss.
  Qed.

  Lemma replicas_inv_validated_keys_of_txn γ gid rids ts :
    ([∗ set] rid ∈ rids, is_replica_validated_ts γ gid rid ts) -∗
    ([∗ set] rid ∈ rids, replica_inv γ gid rid) -∗
    ([∗ set] rid ∈ rids, validated_pwrs_of_txn γ gid rid ts).
  Proof.
    iIntros "#Hvds Hrps".
    iApply big_sepS_forall.
    iIntros (rid Hrid).
    iDestruct (big_sepS_elem_of with "Hvds") as "Hvd"; first apply Hrid.
    iDestruct (big_sepS_elem_of with "Hrps") as "Hrp"; first apply Hrid.
    iApply (replica_inv_validated_keys_of_txn with "Hvd Hrp").
  Qed.

  Definition read_promise γ gid rid key lb ub : iProp Σ :=
    ∃ vdl,
      "#Hvdl"    ∷ is_replica_key_validation_lb γ gid rid key vdl ∗
      "#Habtifp" ∷ ([∗ list] i ↦ b ∈ vdl,
                      ⌜(lb < i)%nat ∧ b = true⌝ -∗ is_group_aborted γ gid i) ∗
      "%Hlenvdl" ∷ ⌜length vdl = ub⌝.

  Lemma read_promise_weaken_lb {γ gid rid key lb ub} lb' :
    (lb ≤ lb')%nat ->
    read_promise γ gid rid key lb ub -∗
    read_promise γ gid rid key lb' ub.
  Proof.
    iIntros (Hge).
    iNamed 1.
    iFrame "Hvdl %".
    iApply (big_sepL_impl with "Habtifp").
    iIntros (t b Hb) "!> Habt [%Ht %Htrue]".
    iApply "Habt".
    iPureIntro.
    split; [lia | done].
  Qed.

  Lemma read_promise_weaken_ub {γ gid rid key lb ub} ub' :
    (ub' ≤ ub)%nat ->
    read_promise γ gid rid key lb ub -∗
    read_promise γ gid rid key lb ub'.
  Proof.
    iIntros (Hle).
    iNamed 1.
    iDestruct (replica_key_validation_lb_weaken (take ub' vdl) with "Hvdl") as "Hvdl'".
    { apply prefix_take. }
    iFrame "Hvdl'".
    iSplit; last first.
    { iPureIntro. rewrite length_take. lia. }
    by iDestruct (big_sepL_take_drop _ _ ub' with "Habtifp") as "[Htake Hdrop]".
  Qed.

  Lemma replica_inv_weaken_ballot_map γ gid rid :
    replica_inv γ gid rid -∗
    ∃ bm, replica_inv_ballot_map γ gid rid bm.
  Proof. iIntros "Hrp". do 2 iNamed "Hrp". iFrame "Hbm". Qed.

  Lemma replicas_inv_weaken_ballot_map γ gid rids :
    ([∗ set] rid ∈ rids, replica_inv γ gid rid) -∗
    ∃ bmm,
      ([∗ map] rid ↦ bm ∈ bmm, replica_inv_ballot_map γ gid rid bm) ∗
      ⌜dom bmm = rids⌝.
  Proof.
    iIntros "Hrps".
    iDestruct (big_sepS_impl with "Hrps []") as "Hrps".
    { iIntros (rid Hrid) "!> Hrp".
      iApply (replica_inv_weaken_ballot_map with "Hrp").
    }
    iDestruct (big_sepS_exists_sepM with "Hrps") as (bmm) "[%Hdom Hrps]".
    iFrame "Hrps %".
  Qed.

End inv.
