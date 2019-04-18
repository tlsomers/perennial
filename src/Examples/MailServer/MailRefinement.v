From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
From RecoveryRefinement.Examples.MailServer Require Import MailAPI MailAPILemmas MailHeap MailTriples.
From RecoveryRefinement.Goose.Examples Require Import MailServer.
From RecoveryRefinement.Goose.Proof Require Import Interp.
Require Import Goose.Proof.RefinementAdequacy.
From RecoveryRefinement Require AtomicPair.Helpers.
From RecoveryRefinement.Goose Require Import Machine GoZeroValues Heap GoLayer.
From RecoveryRefinement.Goose Require Import Machine.
From RecoveryRefinement.Goose Require Import GoZeroValues.

Inductive compile_mail_base {gm: GoModel} : forall {T}, proc Mail.Op T → proc GoLayer.Op T → Prop :=
| cm_open :
    compile_mail_base (Call Mail.Open)
                      (MailServer.Open)
| cm_pickup uid :
    compile_mail_base (Mail.pickup uid)
                      (MailServer.Pickup uid)
| cm_deliver uid msg :
    compile_mail_base (Mail.deliver uid msg)
                      (MailServer.Deliver uid msg)
| cm_delete uid msg :
    compile_mail_base (Call (Mail.Delete uid msg))
                      (MailServer.Delete uid msg)
| cm_unlock uid :
    compile_mail_base (Call (Mail.Unlock uid))
                      (MailServer.Unlock uid)
| cm_dataop {T} (op: Data.Op T) :
    compile_mail_base (Call (Mail.DataOp op))
                      (Call (DataOp op)).

Definition mail_impl {gm: GoModel} :=
  {| compile_rel_base := @compile_mail_base gm;
     recover_rel := rec_singleton (MailServer.Recover) |}.

Import Filesys.FS.
Import GoLayer.Go.
Import Mail.

Set Default Proof Using "Type".
Section refinement_recovery_defs.
  Context `{@gooseG gmodel gmodelHwf Σ, !@cfgG (Mail.Op) (Mail.l) Σ}.
  Context {hGcontents: ghost_mapG contentsC Σ}.
  Context {hGinit: ghost_mapG ghost_init_statusC Σ}.
  Context {hGTmp: gen_heapG string Filesys.FS.Inode Σ}.

  Definition HeapInv_crash (σ: Mail.State) : iProp Σ := True%I.

  Definition InitInv_crash (Γ: gmap uint64 gname) γ σ :=
    (ghost_mapsto_auth γ Uninit
        ∗ ghost_mapsto γ O Uninit
        ∗ ([∗ map] uid↦lm ∈ σ.(messages), ∃ γuid, ⌜ Γ !! uid = Some γuid ⌝ ∗ InboxLockInv γuid O))%I.

  Definition MsgsInv_crash (Γ : gmap uint64 gname) (γ: gname) (σ: Mail.State) : iProp Σ :=
    (∃ ls, GlobalInv ls false ∗ RootDirInv σ ∗ InitInv_crash Γ γ σ
                     ∗ ([∗ map] uid↦lm ∈ σ.(messages), MsgInv Γ ls uid lm false))%I.

  Lemma MsgsInv_crash_set_false Γ γ σ :
    MsgsInv_crash Γ γ σ -∗ MsgsInv Γ γ (RecordSet.set open (λ _, false) σ).
  Proof.
    iIntros "H". iDestruct "H" as (ls) "(Hglobal&Hrootdir&Hinit&Hmsgs)".
    iExists ls. iFrame.
    rewrite /InitInv_crash/InitInv.
    iExists Uninit. iDestruct "Hinit" as "($&$&$)". eauto.
  Qed.

  Global Instance MsgsInv_crash_timeless  Γ γ σ:
    Timeless (MsgsInv_crash Γ γ σ).
  Proof. apply _. Qed.

  Definition TmpInv_crash γtmp : iProp Σ :=
    (∃ tmps_map, SpoolDir ↦ dom (gset string) tmps_map
                 ∗ ghost_mapsto_auth (A := discreteC (gset string)) γtmp (dom (gset _) tmps_map)
                          ∗ [∗ map] name↦inode ∈ tmps_map,
                                      path.mk SpoolDir name ↦ inode)%I.

  Definition CrashInv γtmp :=
    (∃ Γ γ, source_ctx
              ∗ inv execN (∃ σ, source_state σ ∗ MsgsInv_crash Γ γ σ
              ∗ HeapInv_crash σ ∗ TmpInv_crash γtmp))%I.

  Definition CrashStarter γtmp :=
    (∃ tmps : gset string, ghost_mapsto (A := discreteC (gset string)) γtmp 0 tmps
                                                        ∗ SpoolDir ↦ Unlocked)%I.

  Definition CrashInner : iProp Σ :=
    (∃ γtmp,
    (∃ Γ γ σ, source_state σ ∗ MsgsInv_crash Γ γ σ
               ∗ HeapInv_crash σ ∗ TmpInv_crash γtmp) ∗ CrashStarter γtmp)%I.


End refinement_recovery_defs.

Definition init_base `{@GoModelWf gm} (s: GoLayer.Go.State) :=
  s.(fs).(FS.heap) = ∅ ∧
  (forall (uid: uint64),
      (uid < 100 -> s.(fs).(dirents) !! (UserDir uid) = Some ∅) ∧
      (uid >= 100 -> s.(fs).(dirents) !! (UserDir uid) = None)) ∧
  s.(fs).(FS.dirents) !! SpoolDir = Some ∅ ∧
  (∀ d, is_Some (s.(fs).(FS.dirents) !! d) →
        d = SpoolDir ∨ (∃ uid, d = UserDir uid)) ∧
  dom (gset string) s.(fs).(FS.dirents) =
  dom (gset string) s.(fs).(FS.dirlocks) ∧
  (∀ dir l, s.(fs).(FS.dirlocks) !! dir = Some l → fst l = Unlocked) ∧
  s.(maillocks) = None.

Definition init_absr `{@GoModelWf gm} sa sc := Mail.initP sa ∧ init_base sc.

Definition myΣ {gm} {Hgwf: GoModelWf gm} : gFunctors :=
  #[@gooseΣ gm Hgwf; @cfgΣ Mail.Op Mail.l;
    ghost_mapΣ ghost_init_statusC; ghost_mapΣ contentsC;
    gen_heapΣ string (Filesys.FS.Inode)].

Existing Instance subG_goosePreG.
Existing Instance subG_cfgPreG.

Lemma init_dirs {gm} {Hgwf: GoModelWf gm} σ1a σ1c:
  init_absr σ1a σ1c →
  dom (gset string) σ1c.(fs).(dirents) =
                  (set_map UserDir (dom (gset uint64) σ1a.(messages)) ∪ {[SpoolDir]}).
Proof.
  intros (Hinita&Hinitc).
  destruct Hinita as (Hheap&?&Hrange).
  destruct Hinitc as (Hheap'&Hrange'&Hspool&Hdirs&Hlocks1&Hlocks2).
  assert (dom (gset string) σ1c.(fs).(dirents) =
          (set_map UserDir (dom (gset uint64) σ1a.(messages)) ∪ {[SpoolDir]})) as ->; auto.
  rewrite -leibniz_equiv_iff => d.
  split.
  * intros Hin. apply elem_of_dom in Hin. edestruct (Hdirs d) as [|(uid&Heq)]; eauto.
    ** subst. set_solver+.
    ** rewrite Heq.
       destruct (lt_dec uid 100); last first.
       { exfalso. destruct (Hrange' uid) as (?&Hnone). subst.
         rewrite Hnone in Hin; try lia. eapply is_Some_None; eauto.
       }
       apply elem_of_union_l. apply elem_of_map.
       exists uid; split; eauto.
       apply elem_of_dom. destruct (Hrange uid) as (Hsome&?).
       rewrite Hsome; auto. eauto.
  * intros [Huser|Hisspool]%elem_of_union.
    ** apply elem_of_dom. apply elem_of_map in Huser as (uid&Heq&Hin).
       apply elem_of_dom in Hin.
       subst.
       destruct (lt_dec uid 100); last first.
       { exfalso. destruct (Hrange uid) as (?&Hnone).
         rewrite Hnone in Hin; try lia. eapply is_Some_None; eauto.
       }
       destruct (Hrange' uid) as (Hsome&?).
       rewrite Hsome; eauto.
    ** apply elem_of_singleton in Hisspool. subst.
       eapply elem_of_dom; eauto.
Qed.

Lemma init_base_dirs_empty `{@GoModelWf gm} σ dir x:
  init_base σ →
  σ.(fs).(dirents) !! dir = Some x →
  x = ∅.
Proof.
  intros (_&Hrange&Hspool&Hdom&_).
  intros Hsome. destruct (Hdom dir) as [|(uid&?)]; eauto.
  * subst. congruence.
  * destruct (lt_dec uid 100); last first.
    { exfalso. destruct (Hrange uid) as (?&Hnone). subst.
      rewrite Hnone in Hsome; try lia. congruence.
    }
    destruct (Hrange uid) as (Hsome'&?).
    subst. rewrite Hsome' in Hsome; try lia. congruence.
Qed.

(* TODO: the goal statement here looks really confusing -- it's extracted from
   one of the obligations from applying crash_refinement_seq below. I only break
   it out to shorten the qed time of that proof below.

   The explicit implicit arguments are needed or else the wrong things get resolved. *)

Program Lemma recovery_triple {gm} {Hgmwf: @GoModelWf gm}:
  ∀ (H1 : cfgG myΣ) (H2 : gooseG gm myΣ) (param : gname),
    (@CrashInv _ _ myΣ H2 H1 _ _ param) ∗ Registered ∗ (@CrashStarter _ _ myΣ H2 param)
    -∗ WP Recover
       {{ _, |={⊤,nclose sourceN}=>
          ∃ σ2a σ2a' : l.(OpState),
            source_state σ2a
              ∗ ⌜l.(Proc.crash_step) σ2a (Val σ2a' tt)⌝
              ∗ (∀ (Hcfg' : cfgG myΣ) (Hinv' : invG myΣ) (tr' : tregG myΣ),
                    source_ctx ∗ source_state σ2a'
                    ={⊤}=∗
                        (λ H1 H2,
                         ∃ hGTmp, @ExecInner gm Hgmwf myΣ H2 H1 _ _ hGTmp)
                        Hcfg'
                        (GooseG _ _ myΣ Hinv' go_heap_inG go_fs_inG go_global_inG tr')) }}.
Proof.
  intros. iIntros "(Hrest&Hreg&Hstarter)".
  iDestruct "Hrest" as (Γ γ) "(#Hsource&#Hinv)".
  iDestruct "Hstarter" as (tmps) "(Htmps_frag&Hlock)".
  wp_bind. wp_bind.
  iApply (wp_list_start with "[$]").
  iIntros "!> Hlock".
  iInv "Hinv" as "H".
  iDestruct "H" as (σ) "(>Hstate&>Hmsgs&>Hheap&>Htmp)".
  iDestruct "Htmp" as (tmps_map) "(Hdir&Hauth&Hpaths)".
  iDestruct (ghost_var_agree (A := discreteC (gset string)) with "[$] [$]") as %Heq_dom.
  iApply (wp_list_finish with "[$]").
  iIntros (s ltmps) "!> (Hltmps&Hs&Htmps&Hlock)".
  iExists _.
  iSplitL "Hstate Hmsgs Hheap Hauth Htmps Hpaths".
  { iFrame. iExists _. by iFrame. }
  iModIntro.
  iDestruct "Hltmps" as %Hltmps.

  iAssert (ghost_mapsto (A := discreteC (gset string))
                        param 0 (tmps ∖ list_to_set (take 0 ltmps)))%I with "[Htmps_frag]"
    as "Htmps_frag".
  { by rewrite difference_empty_L. }
  iDestruct (slice_mapsto_len with "Hs") as %->.
  assert (0 <= length ltmps) as Hlen by lia.
  revert Hlen.
  remember 0 as i eqn:Heq_i.
  intros Hlen.
  rewrite [a in S a]Heq_i.
  clear Heq_i.
  iLöb as "IH" forall (i Hlen).
  wp_loop.
  destruct equal as [Heqlen|Hneq].
  - iClear "IH". subst.
    rewrite firstn_all.
    (* in a sense we do not even need to argue that the spool dir is actually empty at
       this point, it is totally irrelevant *)
    wp_ret. wp_ret. iNext.
    iInv "Hinv" as "H" "_".
    clear σ.
    iDestruct "H" as (σ) "(>Hstate&>Hmsgs&>Hheap&>Htmp)".
    iApply (fupd_mask_weaken _ _).
    { solve_ndisj. }
    iExists _, _.
    iFrame. iSplitL "".
    { iPureIntro. do 2 eexists; split; econstructor. }
    iClear "Hsource".
    iIntros (???) "(#Hsource&Hstate)".
    iDestruct "Htmp" as (tmps_map') "(Hdir&Hauth&Hpaths)".
    iDestruct (ghost_var_agree (A := discreteC (gset string)) with "[$] [$]") as %Heq_dom.
    rewrite <-Heq_dom.
    iMod (gen_heap_init tmps_map') as (hGTmp) "Htmp".
    iExists hGTmp, Γ, γ, _.
    iFrame.
    iSplitL "".
    { eauto. }
    iSplitL "Hmsgs".
    { by iApply MsgsInv_crash_set_false. }
    iSplitL "".
    { iModIntro. by iApply big_sepDM_empty. }
    iExists _. by iFrame.
  - wp_bind.
    destruct (nth_error ltmps i) as [curr_name|] eqn:Heq_curr_name; last first.
    { exfalso. eapply nth_error_Some; eauto.  inversion Hlen; try congruence; try lia. }
    iApply (wp_sliceRead with "[$]"); first eauto.
    iIntros "!> Hs".
    wp_bind.
    iInv "Hinv" as "H".
    clear σ.
    iDestruct "H" as (σ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
    iDestruct "Htmp" as (tmps_map') "(Hdir&Hauth&Hpaths)".
    iDestruct (ghost_var_agree (A := discreteC (gset string)) with "[$] [$]") as %Heq_dom'.
    rewrite Heq_dom'.
    assert (Hcurr_in: curr_name ∈ tmps ∖ list_to_set (take i ltmps)).
    {
      apply elem_of_difference; split.
      - rewrite -Heq_dom. apply elem_of_elements.
        rewrite -Hltmps. apply elem_of_list_In.
        eapply nth_error_In; eauto.
      - rewrite elem_of_list_to_set. rewrite elem_of_list_In.
        assert (NoDup ltmps) as HNoDup.
        { rewrite Hltmps. apply NoDup_elements. }
        eapply nth_error_split in Heq_curr_name as (l1&l2&Hsplit&Hlen').
        rewrite Hsplit. rewrite -Hlen' take_app.
        rewrite Hsplit in HNoDup.
        apply NoDup_app in HNoDup as (?&Hnotin&?).
        intros Hin. eapply Hnotin.
        { apply elem_of_list_In. eauto. }
        by left.
    }
    assert (∃ v, tmps_map' !! curr_name = Some v) as (inode&Hcurr_inode).
    {
      rewrite -Heq_dom' in Hcurr_in.
      apply elem_of_dom in Hcurr_in as (v&?).
      eauto.
    }
    iDestruct (big_sepM_delete with "Hpaths") as "(Hcurr&Hpaths)"; eauto.
    iApply (wp_delete with "[$]").
    iIntros "!> (Hdir&Hdirlock)".
    iMod (ghost_var_update (A := discreteC (gset string)) with "Hauth [$]") as "(Hauth&Hfrag)".
    iSplitL "Hstate Hmsgs Hheap Hpaths Hdir Hauth".
    {
      iExists _. iFrame.
      iModIntro. iNext. iExists _. iFrame.
      rewrite dom_delete_L. rewrite Heq_dom'. iFrame.
    }
    wp_ret. iModIntro. iNext.
    iApply ("IH" with "[] [$] [$] [$] [Hfrag]").
    { iPureIntro. inversion Hlen; try congruence; try lia. }
    rewrite dom_delete_L Heq_dom'.
    rewrite difference_difference_L.
    assert ((tmps ∖ list_to_set (take (i + 1) ltmps)) =
            (tmps ∖ (list_to_set (take i ltmps) ∪ {[curr_name]}))) as ->; last by auto.
    f_equal.
    eapply nth_error_split in Heq_curr_name as (l1&l2&Hsplit&Hlen').
    rewrite Hsplit -Hlen' take_app.
    rewrite firstn_app_2 //= firstn_O.
    rewrite list_to_set_app_L //= right_id_L //.
    Unshelve.
    eapply sigPtr_eq_dec.
Qed.

Lemma mail_crash_refinement_seq {gm} {Hgmwf: @GoModelWf gm} {T} σ1c σ1a esa esc:
  init_absr σ1a σ1c →
  wf_client_seq esa →
  compile_rel_proc_seq mail_impl esa esc →
  ¬ proc_exec_seq Mail.l esa (rec_singleton (Ret ())) (1, σ1a) Err →
  ∀ σ2c (res: T), proc_exec_seq GoLayer.Go.l esc
                                      (rec_singleton MailServer.Recover) (1, σ1c) (Val σ2c res) →
  ∃ σ2a, proc_exec_seq Mail.l esa (rec_singleton (Ret tt)) (1, σ1a) (Val σ2a res).
Proof.
  eapply (@exmach_crash_refinement_seq gm Hgmwf (@myΣ gm Hgmwf)) with
      (Λa := Mail.l)
      (es := esa)
      (T := T)
      (exec_inv := fun H1 H2 => (∃ hGTmp, @ExecInv gm Hgmwf myΣ H2 H1 _ _ hGTmp)%I)
      (exec_inner := fun H1 H2 => (∃ hGTmp, @ExecInner gm Hgmwf myΣ H2 H1 _ _ hGTmp)%I)
      (crash_inner := fun H1 H2 => @CrashInner gm Hgmwf myΣ H2 H1 _ _)
      (crash_param := fun H1 H2 => gname)
      (crash_inv := fun H1 H2 γ => @CrashInv _ _ myΣ H2 H1 _ _ γ)
      (crash_starter := fun H1 H2 γ => @CrashStarter _ _ myΣ H2 γ)
      (E := nclose sourceN).
  { apply _. }
  { apply _. }
  { intros. apply _. }
  { intros. apply _. }
  { set_solver+. }
  { idtac "obligation 1".
    intros ???? j K Hctx p p' Hcompile. iIntros "(Hj&Hreg&Hexec)".
    iDestruct "Hexec" as (hGTmp) "Hexec". inversion Hcompile; inj_pair2.
    - iApply (open_refinement with "[$]"). iIntros "!>".
      iIntros (?) "(?&?)"; iFrame.
    - iApply (pickup_refinement with "[$]"). iIntros "!>".
      iIntros (?) "(?&?)"; iFrame.
    - iApply (deliver_refinement with "[$]"). iIntros "!>".
      iIntros (?) "(?&?)"; iFrame.
    - iApply (delete_refinement with "[$]"). iIntros "!>".
      iIntros (?) "(?&?)"; iFrame.
    - iApply (unlock_refinement with "[$]"). iIntros "!>".
      iIntros (?) "(?&?)"; iFrame.
    - iDestruct "Hexec" as (Γ γ) "(#Hsource&#Hinv)".
      iInv "Hinv" as "H".
      iDestruct "H" as (σ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
      iApply (data_op_refinement j K with "[$]").
      { solve_ndisj. }
      iIntros (v) "!> H".
      iDestruct "H" as (h') "(Hj&Hreg&Hstate&Hheap)".
      iModIntro. iFrame. iNext. iExists _. iFrame.
  }
  { intros. iIntros "H". iDestruct "H" as (hGTmp ??) "($&?)". }
  { idtac "obligation 2".
    eapply recovery_triple.
  }
  { rewrite /init_absr/initP/init_base. intuition. }
  { idtac "obligation 3".
    clear. iIntros (σ1a σ1c Hinit).
    iIntros (??) "(Hdirs&Hroot&Hdirlocks&Hsrc&Hstate&Hglobal)".
    pose proof (init_dirs _ _ Hinit) as Hdirs.
    destruct Hinit as (Hinita&Hinitc).
    iMod (gen_heap_init (∅: gmap string Inode)) as (hGTmp) "Htmp".
    iExists hGTmp.
    iMod (ghost_var_alloc (A := @ghost_init_statusC gm Hgmwf) Uninit) as "H".
    iDestruct "H" as (γ) "(Hauth&Hfrag)".
    iMod (ghost_var_bulk_alloc (A := contentsC) (σ1a.(messages)) (λ _ _, ∅)) as "H".
    iDestruct "H" as (Γ HΓdom) "HΓ".
    iAssert ([∗ map] k↦_ ∈ σ1a.(messages), ∃ γ0 : gname, ⌜Γ !! k = Some γ0⌝)%I
            with "[HΓ]" as "#HΓ'".
    { iApply big_sepM_mono; last eauto. iIntros (???) "H". iDestruct "H" as (?) "(?&?)"; eauto. }
    iExists Γ, γ, σ1a. iFrame.
    assert (SpoolDir ∈ dom (gset string) σ1c.(fs).(dirents)).
    { rewrite /init_base in Hinitc. intuition.
      apply elem_of_dom. eexists; eauto.
    }
    iSplitL "".
    { iPureIntro. destruct Hinita as (?&->&?); auto. }
    iDestruct (big_opS_delete with "Hdirlocks") as "(Hlock&Hdirlocks)"; eauto.
    iDestruct (big_opM_delete with "Hdirs") as "(Hspool&Hdirs)".
    { rewrite /init_base in Hinitc. intuition. eauto. }
    iSplitR "Htmp Hlock Hspool".
    { rewrite /MsgsInv. iExists [].
      rewrite /initP in Hinita.
      destruct Hinita as (Hheap&Hopen&Hrange).
      rewrite Hopen.
      iFrame.
      iSplitL "Hroot".
      { iModIntro. rewrite /RootDirInv. iSplitR ""; last first.
        - iPureIntro.  rewrite /userRange_ok => uid.
          destruct (Hrange uid). split; intros.
          * apply elem_of_dom; eexists; eauto.
          * apply not_elem_of_dom; eauto.
        - rewrite /init_base in Hinitc.
          rewrite Hdirs. eauto.
      }
      iSplitR "Hdirs Hdirlocks"; last first.
      {rewrite -dom_delete_L.
        iDestruct (big_sepM_dom with "Hdirlocks") as "Hdirlocks".
        iAssert ([∗ map] uid↦lm ∈ σ1a.(messages), MsgInv Γ [] uid (MUnlocked, ∅) false)%I
                 with "[Hdirs Hdirlocks]" as "H"; last first.
        { iModIntro. iApply (big_sepM_mono with "H").
          iIntros (k x Hin) "H".
          iDestruct "H" as (? γuid) "(H1&H2&H3)". iExists _, _. iFrame.
          assert (x = (MUnlocked, ∅)) as ->; last by auto.
          destruct (lt_dec k 100) as [Hlt|Hnlt].
          * destruct (Hrange k) as (Hrange1&?).
            feed pose proof (Hrange1); first by lia. congruence.
          * destruct (Hrange k) as (?&Hgt).
            feed pose proof (Hgt); first by lia. congruence.
        }
        iAssert ([∗ map] k↦y ∈ base.delete SpoolDir σ1c.(fs).(dirents), k ↦ ∅)%I
          with "[Hdirs]" as "Hdirs".
        { iApply big_sepM_mono; last eauto.
          iIntros (dir x Hin) "Hk".
          cut (x = ∅).
          { intros ->. by rewrite dom_empty_L. }
          apply lookup_delete_Some in Hin as (Hneq&Hlookup).
          destruct (Hinitc) as (?&Hrange'&_).
          eapply init_base_dirs_empty; eauto.
        }
        assert (Hdirs_delete : dom (gset string) (map_delete SpoolDir (σ1c.(fs).(dirents))) =
                               set_map UserDir (dom (gset uint64) σ1a.(messages))).
        { rewrite dom_delete_L Hdirs.
          (* I'm amazed set_solver can handle this! *)
          set_solver+. }
        move: Hdirs_delete.
        rewrite /base.delete.
        generalize ((map_delete SpoolDir σ1c.(fs).(dirents))) => dirs.
        generalize (σ1a.(messages)) => msgs.
        clear Hrange Hdirs Hheap H => Hdom.
        iInduction msgs as [|k i m] "IH" using map_ind forall (dirs Hdom).
        { by iApply big_sepM_empty. }
        rewrite big_sepM_insert //.
        rewrite big_sepM_insert //.
        assert (∃ v, dirs !! (UserDir k) = Some v) as (v&Hin).
        {
          rewrite dom_insert_L in Hdom.
          assert (Hin: UserDir k ∈ dom (gset string) dirs).
          { set_solver. }
          apply elem_of_dom in Hin. eauto.
        }
        iDestruct (big_sepM_delete with "Hdirlocks") as "(Hlock&Hdirlocks)"; first eauto.
        iDestruct (big_sepM_delete with "Hdirs") as "(Hdir&Hdirs)"; first eauto.
        iDestruct "HΓ'" as "(Hghost&HΓ')".
        iSplitL "Hlock Hdir Hghost".
        { iDestruct "Hghost" as (γuid) "H".
          iExists (zeroValue _), γuid. iFrame.
          simpl. rewrite dom_empty_L. iFrame.
          iSplitL ""; auto.
        }
        iApply ("IH" with "[] [$] [$] [$]").
        iPureIntro. rewrite dom_insert_L in Hdom.
        rewrite dom_delete_L.
        rewrite Hdom.
        assert (Hnin: (UserDir k) ∉ (set_map UserDir (dom (gset uint64) m) : gset string)).
        {
          rewrite elem_of_map.
          intros (k0&Heq&Hin').
          apply string_app_inj, uint64_to_string_inj in Heq.
          subst. apply elem_of_dom in Hin' as (?&?); congruence.
        }
        clear -Hnin.
        rewrite set_map_union_singleton.
        rewrite -leibniz_equiv_iff.
        rewrite difference_union_distr_l.
        rewrite difference_diag_L left_id.
        rewrite difference_disjoint //.
        rewrite disjoint_singleton_r. auto.
      }
      iExists _. iFrame. iFrame.
      iSplitL ""; auto.
      iModIntro. iApply big_sepM_mono; last iApply "HΓ".
      iIntros (???) "H".
      iDestruct "H" as (γuid) "(?&?&?)".
      iExists _. iFrame. iExists _, _. iFrame.
    }
    { iSplitL "".
      - rewrite /HeapInv. rewrite /initP in Hinita. destruct Hinita as (->&?).
        simpl. iModIntro. by iApply big_sepDM_empty.
      - iExists ∅. iFrame. by iApply big_sepM_empty.
    }
  }
  {
    idtac "obligation 4".
    iIntros (??) "H".
    iDestruct "H" as (hGtmp_old) "Hrest".
    iDestruct "Hrest" as (Γold γold) "(#Hsource&#Hinv)".

    iInv "Hinv" as "H" "_".
    iDestruct "H" as (σ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
    iApply (fupd_mask_weaken _ _).
    { solve_ndisj. }
    iDestruct "Hmsgs" as (?) "(_&>Hroot&Hinit&Hmsgs)".
    iDestruct (big_sepM_mono with "Hmsgs") as "Hmsgs".
    { iIntros (???). iApply MsgInv_weaken. }
    iDestruct "Hmsgs" as ">Hmsgs".
    iIntros (?????) "(Hroot'&Hglobal)".
    iDestruct "Hroot'" as (S) "(Hroot'&Hdirlocks)".
    iDestruct "Hroot" as "(Hroot&%)".
    iDestruct (ghost_var_agree2 (A := discreteC (gset string))_ with "Hroot Hroot'") as %Heq_dom.


    iDestruct "Htmp" as (tmp_map) "(Hdir&_&_&Hpaths)".
    iMod (gen_heap_init (tmp_map: gmap string Inode)) as (hGTmp) "Htmp".
    iMod (ghost_var_alloc (A := @ghost_init_statusC gm Hgmwf) Uninit) as "H".
    iDestruct "H" as (γ) "(Hauth&Hfrag)".
    iMod (ghost_var_bulk_alloc (A := contentsC) (σ.(messages)) (λ _ _, ∅)) as "H".
    iDestruct "H" as (Γ HΓdom) "HΓ".
    iAssert ([∗ map] k↦_ ∈ σ.(messages), ∃ γ0 : gname, ⌜Γ !! k = Some γ0⌝)%I
            with "[HΓ]" as "#HΓ'".
    { iApply big_sepM_mono; last eauto. iIntros (???) "H". iDestruct "H" as (?) "(?&?)"; eauto. }
    iMod (ghost_var_alloc (A := @discreteC (gset string)) (dom (gset _) tmp_map)) as "H".
    iDestruct "H" as (γtmp) "(Hauth_tmp&Hfrag_tmp)".

    iModIntro.
    iExists γtmp, Γ, γ, _. iFrame.
    rewrite <-Heq_dom.
    iDestruct (big_sepS_delete with "Hdirlocks") as "(Hspoollock&Hdirlocks)".
    { by apply elem_of_union_r, elem_of_singleton. }
    iSplitR "Hfrag_tmp Hspoollock"; last first.
    { iExists _. iFrame. }
    iExists [].
    rewrite /HeapInv.
    iSplitR "Htmp Hdir Hauth_tmp Hpaths"; last first.
    { iSplitL ""; auto.
      iExists _. iFrame. }
    iSplitL ""; auto.
    iSplitL "HΓ".
    {  iApply big_sepM_mono; last (iApply "HΓ").
       iIntros (???) "H".
       iDestruct "H" as (γuid ?) "(?&?)".
       iExists _. iSplitL ""; auto.
       iExists _, _. iFrame.
    }
    iClear "Hheap".
    assert (((set_map UserDir (dom (gset uint64) σ.(messages)) ∪ {[SpoolDir]})
               ∖ {[SpoolDir]} : gset string) =
           ((set_map UserDir (dom (gset uint64) σ.(messages))))) as ->.
    { set_solver. }
    rewrite big_opS_fmap; last first.
    { rewrite /UserDir. intros ?? Heq. apply string_app_inj, uint64_to_string_inj in Heq. auto. }
    iDestruct (big_sepM_dom with "Hdirlocks") as "Hdirlocks".
    iDestruct (big_sepM_sepM with "[Hdirlocks Hmsgs]") as "Hmsgs".
    { iFrame. }
    iDestruct (big_sepM_sepM with "[Hmsgs]") as "Hmsgs".
    { iFrame. iFrame "HΓ'". }
    iApply (big_sepM_mono with "Hmsgs").
    iIntros (k x Hlookup) "((H1&H2)&H3)".
    iDestruct "H3" as %Hlookup'.
    destruct Hlookup' as (γ'&?).
    iDestruct "H1" as (??) "(_&(?&?&?))".
    iExists _, _.
    iSplitL ""; eauto.
    iSplitL ""; eauto.
    iFrame. auto.
  }
  {
    (* Idempotence *)
    idtac "obligation 5 (idempotence)".
    iIntros (?? γtmp) "Hcrash".
    iDestruct "Hcrash" as (??) "(#Hsrc&#Hinv)".
    iInv "Hinv" as "H" "_".
    iDestruct "H" as (σ) "(>Hstate&>Hmsgs&>Hheap&>Htmp)".
    iApply (fupd_mask_weaken _ _).
    { solve_ndisj. }
    iDestruct "Hmsgs" as (?) "(_&Hroot&Hinit&Hmsgs)".
    iIntros (?????) "(Hroot'&Hglobal)".
    iDestruct "Hroot'" as (S) "(Hroot'&Hdirlocks)".
    iDestruct "Hroot" as "(Hroot&%)".
    iDestruct (ghost_var_agree2 (A := discreteC (gset string))_ with "Hroot Hroot'") as %Heq_dom.


    iDestruct "Htmp" as (tmp_map) "(Hdir&_&Hpaths)".
    iMod (gen_heap_init (tmp_map: gmap string Inode)) as (hGTmp) "Htmp".
    iMod (ghost_var_alloc (A := @ghost_init_statusC gm Hgmwf) Uninit) as "H".
    iDestruct "H" as (γ) "(Hauth&Hfrag)".
    iMod (ghost_var_bulk_alloc (A := contentsC) (σ.(messages)) (λ _ _, ∅)) as "H".
    iDestruct "H" as (Γ HΓdom) "HΓ".
    iMod (ghost_var_alloc (A := @discreteC (gset string)) (dom (gset _) tmp_map)) as "H".
    iDestruct "H" as (γtmp') "(Hauth_tmp&Hfrag_tmp)".
    iAssert ([∗ map] k↦_ ∈ σ.(messages), ∃ γ0 : gname, ⌜Γ !! k = Some γ0⌝)%I
            with "[HΓ]" as "#HΓ'".
    { iApply big_sepM_mono; last eauto. iIntros (???) "H". iDestruct "H" as (?) "(?&?)"; eauto. }

    iModIntro.
    iExists γtmp', Γ, γ, _. iFrame.
    rewrite <-Heq_dom.
    iDestruct (big_sepS_delete with "Hdirlocks") as "(Hspoollock&Hdirlocks)".
    { by apply elem_of_union_r, elem_of_singleton. }
    iSplitR "Hfrag_tmp Hspoollock"; last first.
    { iExists _. iFrame. }
    iExists [].
    rewrite /HeapInv.
    iSplitR "Htmp Hdir Hauth_tmp Hpaths"; last first.
    { iExists _. iFrame. }
    iSplitL ""; auto.
    iSplitL "HΓ".
    {  iApply big_sepM_mono; last (iApply "HΓ").
       iIntros (???) "H".
       iDestruct "H" as (γuid ?) "(?&?)".
       iExists _. iSplitL ""; auto.
       iExists _, _. iFrame.
    }
    assert (((set_map UserDir (dom (gset uint64) σ.(messages)) ∪ {[SpoolDir]})
               ∖ {[SpoolDir]} : gset string) =
           ((set_map UserDir (dom (gset uint64) σ.(messages))))) as ->.
    { set_solver. }
    rewrite big_opS_fmap; last first.
    { rewrite /UserDir. intros ?? Heq. apply string_app_inj, uint64_to_string_inj in Heq. auto. }
    iDestruct (big_sepM_dom with "Hdirlocks") as "Hdirlocks".
    iDestruct (big_sepM_sepM with "[Hdirlocks Hmsgs]") as "Hmsgs".
    { iFrame. }
    iDestruct (big_sepM_sepM with "[Hmsgs]") as "Hmsgs".
    { iFrame. iFrame "HΓ'". }
    iApply (big_sepM_mono with "Hmsgs").
    iIntros (k x Hlookup) "((H1&H2)&H3)".
    iDestruct "H3" as %Hlookup'.
    destruct Hlookup' as (γ'&?).
    iDestruct "H1" as (??) "(_&(?&?&?&?&?))".
    iExists _, _.
    iSplitL ""; eauto.
    iSplitL ""; eauto.
    iFrame. auto.
  }
  { idtac "obligation 6".
    iIntros (??) "(H1&H2)". iDestruct "H1" as (Hinv γtmp) "(H&Hstarter)".
    iDestruct "H" as (???) "(?&?&?)".
    iExists _. iFrame.
    iExists _, _. iFrame.
    iMod (@inv_alloc myΣ (go_invG) execN _ _ with "[-]"); last eauto.
    iNext. iExists _. iFrame.
  }
  { idtac "obligation 7".
    iIntros (??) "(H1&H2)". iDestruct "H1" as (Hinv hGTmp ??? Hclosed) "(Hstate&Hmsgs&Heap&Htmps)".
    iExists hGTmp.
    iExists _, _. iFrame.
    iMod (@inv_alloc myΣ (go_invG) execN _ _ with "[-]"); last eauto.
    iNext. iExists _. iFrame "Hstate Heap Htmps".
    rewrite /MsgsInv.
    iDestruct "Hmsgs" as (?) "(Hglobal&Hroot&Hinit&Hmsgs)".
    iExists _. iFrame "Hglobal Hroot Hinit".
    rewrite Hclosed. eauto.
  }
  { idtac "obligation 8".
    iIntros (??) "_ H".
    iDestruct "H" as (hGTmp Γ γ) "Hrest".
    iDestruct "Hrest" as "(#Hsource&#Hinv)".
    iInv "Hinv" as "H" "_".
    iDestruct "H" as (σ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
    iDestruct "Hmsgs" as (?) "(_&>Hroot&Hinit&Hmsgs)".
    iDestruct (big_sepM_mono with "Hmsgs") as "Hmsgs".
    { iIntros (???). iApply MsgInv_weaken. }
    iDestruct "Hmsgs" as ">Hmsgs".
    iApply (fupd_mask_weaken _ _).
    { solve_ndisj. }
    iExists _, _.
    iFrame.
    iSplitL "".
    { iPureIntro. do 2 eexists. split; econstructor. }

    iDestruct "Hroot" as "(Hroot&%)".
    iClear "Hsource".
    iIntros (???????) "(#Hsource&Hstate&Hdirlocks&Hglobal)".
    iDestruct "Htmp" as (tmps_map') "(Hdir&Hdirlock&Hauth'&Hpaths)".
    iMod (gen_heap_init tmps_map') as (hGTmp') "Htmp".
    iMod (ghost_var_alloc (A := @ghost_init_statusC gm Hgmwf) Uninit) as "H".
    iDestruct "H" as (γ') "(Hauth&Hfrag)".
    iMod (ghost_var_bulk_alloc (A := contentsC) (σ.(messages)) (λ _ _, ∅)) as "H".
    iDestruct "H" as (Γ' HΓdom) "HΓ".
    iDestruct "Hdirlocks" as (S) "(Hroot'&Hdirlocks)".
    iDestruct (ghost_var_agree2 (A := discreteC (gset string))_ with "Hroot Hroot'") as %Heq_dom.
    iAssert ([∗ map] k↦_ ∈ σ.(messages), ∃ γ0 : gname, ⌜Γ' !! k = Some γ0⌝)%I
            with "[HΓ]" as "#HΓ'".
    { iApply big_sepM_mono; last eauto. iIntros (???) "H". iDestruct "H" as (?) "(?&?)"; eauto. }
    iExists hGTmp', Γ', γ', _.
    iModIntro. iFrame.
    iSplitL ""; first eauto.
    iExists []. iFrame.

    rewrite <-Heq_dom.
    iDestruct (big_sepS_delete with "Hdirlocks") as "(Hspoollock&Hdirlocks)".
    { by apply elem_of_union_r, elem_of_singleton. }
    iSplitR "Htmp Hdir Hpaths Hspoollock"; last first.
    { iSplitL "".
      { by iApply big_sepDM_empty. }
      iExists _. iFrame. }
    iSplitL ""; auto.
    iExists _. iFrame. iFrame.
    iSplitL "HΓ".
    { iSplitL ""; auto.
      iApply big_sepM_mono; last (iApply "HΓ").
       iIntros (???) "H".
       iDestruct "H" as (γuid ?) "(?&?)".
       iExists _. iSplitL ""; auto.
       iExists _, _. iFrame.
    }

    assert (((set_map UserDir (dom (gset uint64) σ.(messages)) ∪ {[SpoolDir]})
               ∖ {[SpoolDir]} : gset string) =
           ((set_map UserDir (dom (gset uint64) σ.(messages))))) as ->.
    { set_solver. }
    rewrite big_opS_fmap; last first.
    { rewrite /UserDir. intros ?? Heq. apply string_app_inj, uint64_to_string_inj in Heq. auto. }
    iDestruct (big_sepM_dom with "Hdirlocks") as "Hdirlocks".
    iDestruct (big_sepM_sepM with "[Hdirlocks Hmsgs]") as "Hmsgs".
    { iFrame. }
    iDestruct (big_sepM_sepM with "[Hmsgs]") as "Hmsgs".
    { iFrame. iFrame "HΓ'". }
    iApply (big_sepM_mono with "Hmsgs").
    iIntros (k x Hlookup) "((H1&H2)&H3)".
    iDestruct "H3" as %Hlookup'.
    destruct Hlookup' as (γ''&?).
    iDestruct "H1" as (??)  "(_&H)".
    iDestruct "H" as "(?&?&?)".
    iExists _, _.
    iSplitL ""; eauto.
    iSplitL ""; eauto.
    iFrame. auto.
  }
  (* TODO get rid of these *)
  Unshelve.
  apply sigPtr_eq_dec.
  apply (zeroValue _).
  apply (zeroValue _).
  apply sigPtr_eq_dec.
  apply (zeroValue _).
Time Qed.
Print Assumptions mail_crash_refinement_seq.
