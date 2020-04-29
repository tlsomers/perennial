From RecordUpdate Require Import RecordSet.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant.

Section simulation.
  Context `{!invG Σ}.
  Context {state: Type} (wf: state -> Prop) (P: state -> iProp Σ).
  Context (E: coPset).
  (* TODO: if we can start using this everywhere I think we can start proving
  generic theorems about simulation, like the one below *)
  Definition simulation_fupd {T} (tr: transition state T) (Q: T -> iProp Σ): iProp Σ :=
    (∀ σ σ' r,
         ⌜wf σ⌝ -∗
         ⌜relation.denote tr σ σ' r⌝ -∗
        (P σ ={E}=∗ P σ' ∗ ⌜wf σ'⌝ ∗ Q r)).

  Theorem simulation_bind_fupd {A B}
          (tr1: transition state A)
          (tr2: A -> transition state B)
          (Q: B -> iProp Σ) :
    simulation_fupd tr1 (fun x => simulation_fupd (tr2 x) Q) -∗
    simulation_fupd (bind tr1 tr2) Q.
  Proof.
    iIntros "Hfupd".
    iIntros (σ1 σ3 r Hwf Htr) "HP".
    simpl in Htr.
    inversion Htr; subst; clear Htr.
    rename s2 into σ2.
    iMod ("Hfupd" with "[] [] HP") as "(HP&%Hwf2&Hfupd2)"; eauto.
    iMod ("Hfupd2" with "[] [] HP") as "(HP&%Hwf3&HQ)"; eauto.
    iFrame.
    auto.
  Qed.
End simulation.

Section goose_lang.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!walG Σ}.

Implicit Types (v:val) (z:Z).
Implicit Types (γ: wal_names (Σ:=Σ)).
Implicit Types (s: log_state.t) (memLog: list update.t) (txns: list (u64 * list update.t)).
Implicit Types (pos: u64) (txn_id: nat).

Context (P: log_state.t -> iProp Σ).
Let N := walN.
Let circN := walN .@ "circ".

Definition in_bounds γ (a: u64): iProp Σ. Admitted.
Instance in_bounds_persistent γ a : Persistent (in_bounds γ a).
Proof. Admitted.

(* TODO: this will actually require combining in_bounds with some authoritative
resource from the invariant, obviously it can't be for an arbitrary [σ] *)
Theorem in_bounds_valid γ σ a :
  in_bounds γ a -∗ ⌜is_Some (σ.(log_state.d) !! int.val a)⌝.
Proof. Admitted.

(* this is more or less big_sepM_lookup_acc, but with is_installed_read unfolded *)
Theorem is_installed_read_lookup {γ d txns installed_lb} {a: u64} :
  is_Some (d !! int.val a) ->
  is_installed_read γ d txns installed_lb -∗
  ∃ txn_id b,
    ⌜(installed_lb ≤ txn_id)%nat ∧
      apply_upds (txn_upds (take txn_id txns)) d !! int.val a = Some b⌝ ∗
    int.val a d↦ b ∗ (int.val a d↦ b -∗ is_installed_read γ d txns installed_lb).
Proof.
  rewrite /is_installed_read.
  iIntros (Hlookup) "Hbs".
  destruct Hlookup as [b0 Hlookup].
  iDestruct (big_sepM_lookup_acc _ _ _ _ Hlookup with "Hbs") as "[Hb Hbs]".
  iDestruct "Hb" as (b) "(%Hbvalue&Hb&%Ha_bound)".
  destruct Hbvalue as [txn_id (Htxn_id_bound&Htxns_val)].
  iExists txn_id, b.
  iFrame "Hb".
  iSplit; first by auto.
  iIntros "Hb".
  iApply ("Hbs" with "[Hb]").
  { iExists _; iFrame.
    iPureIntro; eauto. }
Qed.

(* simpler read_installed just for experimenting *)
Definition log_read_installed (a:u64): transition log_state.t Block :=
  installed_txn_id ← suchThat (fun s txn_id =>
                                 s.(log_state.installed_lb) ≤
                                 txn_id)%nat;
  d ← reads (disk_at_txn_id installed_txn_id);
  unwrap (d !! int.val a).

Theorem wp_Walog__ReadInstalled (Q: Block -> iProp Σ) l γ a :
  {{{ is_wal P l γ ∗
      in_bounds γ a ∗
       (∀ σ σ' b,
         ⌜wal_wf σ⌝ -∗
         ⌜relation.denote (log_read_installed a) σ σ' b⌝ -∗
         (P σ ={⊤ ∖↑ N}=∗ P σ' ∗ Q b))
   }}}
    Walog__ReadInstalled #l #a
  {{{ bl, RET slice_val bl; ∃ b, is_block bl 1 b ∗ Q b}}}.
Proof.
  iIntros (Φ) "(#Hwal & #Ha_valid & Hfupd) HΦ".
  wp_call.
  wp_apply (wp_Read_fupd (⊤∖↑walN) (λ b, Q b)%I _ 1 (* q=1 *) with "[Hfupd]").
  { iDestruct "Hwal" as "[Hwal Hcirc]".
    iInv "Hwal" as (σ) "[Hinner HP]" "Hclose".
    iDestruct "Hinner" as "(>? & ? & ? & Hinstalled & ?)"; iNamed.
    iDestruct (is_installed_to_read with "Hinstalled") as "[>Hinstalled_read Hinstalled]".
    iDestruct (in_bounds_valid _ σ with "Ha_valid") as %Hlookup.
    iDestruct (is_installed_read_lookup Hlookup with "Hinstalled_read") as
        (txn_id b [Htxn_id Hbval]) "(Hb&Hinstalled_read)".
    iModIntro.
    iExists b; iFrame "Hb".
    iNext.
    iIntros "Hb".
    iSpecialize ("Hinstalled_read" with "Hb").
    iSpecialize ("Hinstalled" with "Hinstalled_read").
    iMod ("Hfupd" $! σ σ b with "[//] [] HP") as "[HP HQ]".
    { iPureIntro.
      repeat (simpl; monad_simpl).
      exists σ txn_id.
      { econstructor; eauto. }
      repeat (simpl; monad_simpl). }
    iFrame.
    iApply "Hclose".
    iModIntro.
    iExists _; iFrame "HP".
    iFrame.
    auto.
  }
  iIntros (s b) "(HQ&Hs)".
  iApply "HΦ".
  iExists _; iFrame.
  iDestruct (is_slice_to_small with "Hs") as "$".
Qed.

Definition cutMemLog (installEnd: u64) (σ: locked_state) : locked_state :=
  set memStart (λ _, installEnd)
      (set memLog (drop (int.nat installEnd-int.nat σ.(memStart))%nat) σ).

Theorem wp_WalogState__cutMemLog γ (st: loc) σ (installEnd: u64) :
  {{{ wal_linv_fields st σ ∗
      memLog_linv γ σ.(memStart) σ.(memLog)}}}
    WalogState__cutMemLog #st #installEnd
  {{{ σ', RET #();
      ⌜σ' = cutMemLog installEnd σ⌝ ∗
      wal_linv_fields st σ' ∗
      memLog_linv γ σ'.(memStart) σ'.(memLog)
  }}}.
Proof.
Admitted.

Fixpoint list_to_gmap_set {A} `{!EqDecision A} `{!Countable A} (l: list A): gmap A unit :=
  match l with
  | [] => ∅
  | x::l => <[x := tt]> (list_to_gmap_set l)
  end.

Theorem list_to_gmap_set_lookup {A} `{!EqDecision A} `{!Countable A} (l: list A) (x: A) :
  In x l <-> list_to_gmap_set l !! x = Some tt.
Proof.
  induction l; simpl.
  - rewrite lookup_empty; split; [ intros [] | congruence ].
  - destruct (decide (a = x)); subst.
    + rewrite lookup_insert.
      split; intuition idtac.
    + rewrite -> lookup_insert_ne by auto.
      split; intuition idtac.
Qed.

Theorem wp_installBlocks γ d bufs_s (bufs: list update.t)
        (installed_txn_id new_installed_txn_id: nat) :
  {{{ readonly (updates_slice_frag bufs_s 1 bufs) ∗
      (* these aren't enough assumptions - we need bufs to actually match the
      new transactions being installed (which will come from snapshotting the
      memLog invariant) *)
      own γ.(being_installed_name) (◯ Excl' (∅: gmap Z unit)) ∗
      own γ.(new_installed_name) (◯ Excl' installed_txn_id)
   }}}
    installBlocks #d (slice_val bufs_s)
  {{{ RET #(); updates_slice bufs_s bufs ∗
      (* probably not enough in the postcondition, but it can only be ghost
      variables so maybe this is it *)
      own γ.(being_installed_name) (◯ Excl' (list_to_gmap_set ((λ u, int.val (update.addr u)) <$> bufs))) ∗
      own γ.(new_installed_name) (◯ Excl' installed_txn_id)
  }}}.
Proof.
Admitted.

Theorem wp_Walog__logInstall γ l σₛ :
  {{{ "#st" ∷ readonly (l ↦[Walog.S :: "st"] #σₛ.(wal_st)) ∗
      "#d" ∷ readonly (l ↦[Walog.S :: "d"] σₛ.(wal_d)) ∗
      "#memLock" ∷ readonly (l ↦[Walog.S :: "memLock"] #σₛ.(memLock)) ∗
      "#condInstall" ∷ readonly (l ↦[Walog.S :: "condInstall"] #σₛ.(condInstall)) ∗
      "Hlkinv" ∷ wal_linv σₛ.(wal_st) γ ∗
      "His_locked" ∷ locked γ.(lock_name) ∗
      "#lk" ∷ is_lock N γ.(lock_name) #σₛ.(memLock) (wal_linv σₛ.(wal_st) γ) ∗
      "#cond_install" ∷ is_cond σₛ.(condInstall) #σₛ.(memLock)
  }}}
    Walog__logInstall #l
  {{{ (blkCount installEnd:u64), RET (#blkCount, #installEnd);
      "Hlkinv" ∷ wal_linv σₛ.(wal_st) γ ∗
      "His_locked" ∷ locked γ.(lock_name)
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ"; iNamed "Hpre". (* TODO: would be nice to do this anonymously *)
  iNamed "Hlkinv".
  iNamed "Hfields".
  iNamed "Hfield_ptsto".
  wp_call.
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_loadField.
  (* TODO: SliceTake of memLog (but should be read-only) *)
Admitted.

Theorem wp_Walog__installer γ l :
  {{{ is_wal P l γ }}}
    Walog__installer #l
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "#Hwal HΦ".
  iMod (is_wal_read_mem with "Hwal") as "#Hmem".
  wp_call.
  iNamed "Hmem".
  iNamed "Hstfields".
  wp_loadField.
  wp_apply (acquire_spec with "lk").
  iIntros "[Hlocked Hlockinv]".
  wp_apply (wp_inc_nthread with "[$Hlockinv $st]"); iIntros "Hlockinv".
  wp_pures.
  wp_bind (For _ _ _).
  wp_apply (wp_forBreak_cond (fun _ => "Hlockinv" ∷ wal_linv σₛ.(wal_st) γ ∗ "Hlocked" ∷ locked γ.(lock_name))%I
           with "[] [$Hlocked $Hlockinv]").
  { clear Φ.
    iIntros "!>" (Φ) "I HΦ"; iNamed "I".
    wp_apply (wp_load_shutdown with "[$st $Hlockinv]"); iIntros (shutdown) "Hlockinv".
    wp_pures.
    wp_if_destruct.
    - wp_pures.
      wp_apply (wp_Walog__logInstall with "[$st $d $lk $memlock $condInstall $cond_install $Hlocked $Hlockinv]").
      iIntros (blkCount installEnd) "post"; iNamed "post".
      wp_pures.
      wp_bind (If _ _ _).
      wp_if_destruct.
      { wp_apply util_proof.wp_DPrintf; wp_pures.
        iApply ("HΦ" with "[$]"). }
      wp_loadField.
      wp_apply (wp_condWait with "[$cond_install $lk $His_locked $Hlkinv]").
      iIntros "[His_locked Hlkinv]".
      wp_pures.
      iApply ("HΦ" with "[$]").
    - iApply ("HΦ" with "[$]"). }
  iIntros "I"; iNamed "I".
  wp_apply util_proof.wp_DPrintf.
  wp_apply (wp_dec_nthread with "[$Hlockinv $st]"); iIntros "Hlockinv".
  wp_loadField.
  wp_apply (wp_condSignal with "[$cond_shut]").
  wp_loadField.
  wp_apply (release_spec with "[$lk $Hlocked $Hlockinv]").
  iApply ("HΦ" with "[$]").
Qed.

End goose_lang.
