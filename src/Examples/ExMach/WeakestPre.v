From iris.algebra Require Import auth gmap frac agree.
Require Export CSL.WeakestPre CSL.Lifting.
Require Import Helpers.RelationTheorems.
From iris.algebra Require Export functions.
From iris.base_logic.lib Require Export invariants gen_heap.
From iris.proofmode Require Export tactics.
Require Export ExMach.ExMachAPI.
Set Default Proof Using "Type".

Class exmachG Σ := ExMachG {
                     exm_invG : invG Σ;
                     exm_mem_inG :> gen_heapG nat nat Σ;
                     exm_disk_inG :> gen_heapG nat nat Σ;
                   }.

Import ExMach.

Lemma gen_heap_strong_init `{H: gen_heapPreG L V Σ} σs :
  (|==> ∃ (H0 : gen_heapG L V Σ) (Hpf: gen_heap_inG = gen_heap_preG_inG), gen_heap_ctx σs ∗
    own (gen_heap_name _) (◯ (to_gen_heap σs)))%I.
Proof.
  iMod (own_alloc (● to_gen_heap σs ⋅ ◯ to_gen_heap σs)) as (γ) "(?&?)".
  { apply auth_valid_discrete_2; split; auto. exact: to_gen_heap_valid. }
  iModIntro. unshelve (iExists (GenHeapG L V Σ _ _ _ γ), _); auto. iFrame.
Qed.

Definition ex_mach_interp {Σ} {hM: gen_heapG addr nat Σ} {hD: gen_heapG addr nat Σ} :=
      (λ s, ∃ mem disk, (gen_heap_ctx mem (hG := hM)) ∗
                        (gen_heap_ctx disk (hG := hD)) ∗
                        ⌜ mem = mem_state s ∧
                          disk = disk_state s ∧
                          (∀ i, is_Some (mem_state s !! i) → i < size) ∧
                          (∀ i, is_Some (disk_state s !! i) → i < size) ⌝
      )%I.

Definition ex_mach_interp' `{exmachG Σ} :=
    @ex_mach_interp _ exm_mem_inG exm_disk_inG.

Instance exmachG_irisG `{exmachG Σ} : irisG ExMach.Op ExMach.l Σ :=
  {
    iris_invG := exm_invG;
    state_interp := ex_mach_interp'
  }.


Definition mem_mapsto_vs k v k' :=
  match Nat.compare k' k with
  | Lt => None
  | Eq => Some v
  | Gt => Some 0
  end.

Global Notation "l m↦{ q } v " := (mapsto (hG := exm_mem_inG) l q v)
  (at level 20, q at level 50, format "l  m↦{ q } v") : bi_scope.
Global Notation "l m↦ v " :=
  (mapsto (hG := exm_mem_inG) l 1 v)
  (at level 20) : bi_scope.

Global Notation "l d↦{ q } v " := (mapsto (hG := exm_disk_inG) l q v)
  (at level 20, q at level 50, format "l  d↦{ q } v") : bi_scope.
Global Notation "l d↦ v " :=
  (mapsto (hG := exm_disk_inG) l 1 v)
  (at level 20) : bi_scope.

Section lifting.
Context `{exmachG Σ}.

Lemma nat_compare_lt_Lt: ∀ n m : nat, n < m → (n ?= m) = Lt.
Proof. intros. by apply nat_compare_lt. Qed.
Lemma nat_compare_gt_Gt: ∀ n m : nat, n > m → (n ?= m) = Gt.
Proof. intros. by apply nat_compare_gt. Qed.

Lemma mem_init_to_bigOp mem:
  own (i := @gen_heap_inG _ _ _ _ _ exm_mem_inG)
      (gen_heap_name (exm_mem_inG))
      (◯ to_gen_heap mem)
      -∗
  [∗ map] i↦v ∈ mem, i m↦ v .
Proof.
  induction mem using map_ind.
  - iIntros. rewrite //=.
  - iIntros "Hown".
    rewrite big_opM_insert //.

    iAssert (own (i := @gen_heap_inG _ _ _ _ _ exm_mem_inG) (gen_heap_name (exm_mem_inG))
                 (◯ to_gen_heap m) ∗
                 (i m↦ x))%I
                    with "[Hown]" as "[Hrest $]".
    {
      rewrite mapsto_eq /mapsto_def //.
      rewrite to_gen_heap_insert insert_singleton_op; last by apply lookup_to_gen_heap_None.
      rewrite auth_frag_op. iDestruct "Hown" as "(?&?)". iFrame.
    }
    by iApply IHmem.
Qed.

Lemma disk_init_to_bigOp disk:
  own (i := @gen_heap_inG _ _ _ _ _ exm_disk_inG)
      (gen_heap_name (exm_disk_inG))
      (◯ to_gen_heap disk)
      -∗
  [∗ map] i↦v ∈ disk, i d↦ v .
Proof.
  induction disk using map_ind.
  - iIntros. rewrite //=.
  - iIntros "Hown".
    rewrite big_opM_insert //.

    iAssert (own (i := @gen_heap_inG _ _ _ _ _ exm_disk_inG) (gen_heap_name (exm_disk_inG))
                 (◯ to_gen_heap m) ∗
                 (i d↦ x))%I
                    with "[Hown]" as "[Hrest $]".
    {
      rewrite mapsto_eq /mapsto_def //.
      rewrite to_gen_heap_insert insert_singleton_op; last by apply lookup_to_gen_heap_None.
      rewrite auth_frag_op. iDestruct "Hown" as "(?&?)". iFrame.
    }
    by iApply IHdisk.
Qed.

Lemma wp_write_mem s E i v' v :
  {{{ ▷ i m↦ v' }}} write_mem i v @ s; E {{{ RET tt; i m↦ v }}}.
Proof.
  iIntros (Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros (σ) "Hown".
  iModIntro. iSplit; first by destruct s.
  iIntros (e2 σ2 Hstep) "!>".
  inversion Hstep; subst.
  iDestruct "Hown" as (mems disks) "(Hown1&Hown2&Hp)".
  iDestruct "Hp" as %(Heq_mem&?&Hsize&?).
  iDestruct (gen_heap_valid with "Hown1 Hi") as %Hin_bound.
  iMod (@gen_heap_update with "Hown1 Hi") as "[Hown1 Hi]".
  iModIntro. iSplitR "Hi HΦ".
  - iExists _, _. iFrame.
    iPureIntro. split_and!.
    * rewrite /set_mem/set_default -Heq_mem Hin_bound //.
    * done.
    * rewrite /set_mem/set_default//= => i'.
      specialize (Hsize i').
      destruct ((mem_state σ) !! i) eqn:Heq; rewrite Heq.
      ** case (decide (i = i')).
         *** intros -> ?. apply Hsize; eauto.
         *** intros ?. rewrite lookup_insert_ne //=.
      ** apply Hsize.
    * eauto.
  - iApply "HΦ". eauto.
Qed.

Lemma wp_read_mem s E i v :
  {{{ ▷ i m↦ v }}} read_mem i @ s; E {{{ RET v; i m↦ v }}}.
Proof.
  iIntros (Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros (σ) "Hown".
  iModIntro. iSplit; first by destruct s.
  iIntros (e2 σ2 Hstep) "!>".
  inversion Hstep; subst.
  iDestruct "Hown" as (mems disks) "(Hown1&Hown2&Hp)".
  iDestruct "Hp" as %(Heq_mem&?&Hsize&?).
  iDestruct (gen_heap_valid with "Hown1 Hi") as %Hin_bound.
  iModIntro. iSplitR "Hi HΦ".
  - iExists _, _. iFrame; iPureIntro; split_and!; eauto.
  - rewrite /get_mem/get_default -Heq_mem Hin_bound.
    by iApply "HΦ".
Qed.

Lemma cas_non_stuck i v1 v2 σ:
  ¬ ExMach.l.(step) (CAS i v1 v2) σ Err.
Proof.
  intros Hstuck. destruct Hstuck as [Hread|(v'&?&Hread&Hrest)].
  - inversion Hread.
  - destruct nat_eq_dec; subst; [apply bind_pure_no_err in Hrest|]; inversion Hrest.
Qed.

Lemma wp_cas_fail s E i v1 v2 v3 :
  v1 ≠ v2 →
  {{{ ▷ i m↦ v1 }}} cas i v2 v3 @ s; E {{{ RET v1; i m↦ v1 }}}.
Proof.
  iIntros (Hneq Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros (σ) "Hown".
  iModIntro. iSplit.
  { destruct s; auto using cas_non_stuck. }
  iIntros (e2 σ2 Hstep) "!>".
  iDestruct "Hown" as (mems disks) "(Hown1&Hown2&Hp)".
  iDestruct "Hp" as %(Heq_mem&?&Hsize&?).
  iDestruct (gen_heap_valid with "Hown1 Hi") as %Hin_bound.
  assert (Hlookup: σ.(mem_state) !! i = Some v1).
  { rewrite -Heq_mem. apply Hin_bound. }
  inversion Hstep as (v'&σ2'&Hread&Hrest); subst.
  rewrite /get_mem/get_default/reads Hlookup in Hread.
  inversion Hread; subst.
  destruct nat_eq_dec; first by exfalso.
  inversion Hrest; subst.
  iModIntro. iSplitR "Hi HΦ".
  - iExists _, _. iFrame; iPureIntro; split_and!; eauto.
  - by iApply "HΦ".
Qed.

Lemma wp_cas_suc s E i v1 v2 :
  {{{ ▷ i m↦ v1 }}} cas i v1 v2 @ s; E {{{ RET v1; i m↦ v2 }}}.
Proof.
  iIntros (Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros (σ) "Hown".
  iModIntro. iSplit.
  { destruct s; auto using cas_non_stuck. }
  iIntros (v2' σ2 Hstep) "!>".
  iDestruct "Hown" as (mems disks) "(Hown1&Hown2&Hp)".
  iDestruct "Hp" as %(Heq_mem&?&Hsize&?).
  iDestruct (gen_heap_valid with "Hown1 Hi") as %Hin_bound.
  assert (Hlookup: σ.(mem_state) !! i = Some v1).
  { rewrite -Heq_mem. apply Hin_bound. }
  inversion Hstep as (v'&σ2'&Hread&Hrest); subst.
  inversion Hread; subst.
  rewrite /get_mem/get_default/reads Hlookup in Hread Hrest.
  destruct nat_eq_dec; last by eauto.
  destruct Hrest as ([]&?&Hputs&Hpure).
  inversion Hpure; subst.
  inversion Hputs; inversion Hpure; subst.
  iMod (@gen_heap_update with "Hown1 Hi") as "(Hown1&Hi)".
  iModIntro.
  iSplitR "Hi HΦ".
  - iExists _, _. iFrame.
    iPureIntro. split_and!.
    * rewrite /set_mem/set_default//= Hin_bound //.
    * done.
    * rewrite /set_mem/set_default//= => i'.
      specialize (Hsize i').
      destruct ((mem_state σ2') !! i) eqn:Heq; rewrite Heq.
      ** case (decide (i = i')).
         *** intros -> ?. apply Hsize; eauto.
         *** intros ?. rewrite lookup_insert_ne //=.
      ** apply Hsize.
    * eauto.
  - iApply "HΦ". eauto.
Qed.

Lemma wp_write_disk s E i v' v :
  {{{ ▷ i d↦ v' }}} write_disk i v @ s; E {{{ RET tt; i d↦ v }}}.
Proof.
  iIntros (Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros (σ) "Hown".
  iModIntro. iSplit; first by destruct s.
  iIntros (e2 σ2 Hstep) "!>".
  inversion Hstep; subst.
  iDestruct "Hown" as (mems disks) "(Hown1&Hown2&Hp)".
  iDestruct "Hp" as %(Heq_mem&Heq_disk&?&Hsize).
  iDestruct (gen_heap_valid with "Hown2 Hi") as %Hin_bound.
  iMod (@gen_heap_update with "Hown2 Hi") as "[Hown2 Hi]".
  iModIntro. iSplitR "Hi HΦ".
  - iExists _, _. iFrame.
    iPureIntro. split_and!.
    * done.
    * rewrite /set_disk/set_default -Heq_disk Hin_bound //.
    * eauto.
    * rewrite /set_disk/set_default//= => i'.
      specialize (Hsize i').
      destruct ((disk_state σ) !! i) eqn:Heq; rewrite Heq.
      ** case (decide (i = i')).
         *** intros -> ?. apply Hsize; eauto.
         *** intros ?. rewrite lookup_insert_ne //=.
      ** apply Hsize.
  - iApply "HΦ". eauto.
Qed.

Lemma wp_read_disk s E i v :
  {{{ ▷ i d↦ v }}} read_disk i @ s; E {{{ RET v; i d↦ v }}}.
Proof.
  iIntros (Φ) ">Hi HΦ". iApply wp_lift_call_step.
  iIntros (σ) "Hown".
  iModIntro. iSplit; first by destruct s.
  iIntros (e2 σ2 Hstep) "!>".
  inversion Hstep; subst.
  iDestruct "Hown" as (mems disks) "(Hown1&Hown2&Hp)".
  iDestruct "Hp" as %(Heq_mem&Heq_disk&Hsize&?).
  iDestruct (gen_heap_valid with "Hown2 Hi") as %Hin_bound.
  iModIntro. iSplitR "Hi HΦ".
  - iExists _, _. iFrame; iPureIntro; split_and!; eauto.
  - rewrite /get_disk/get_default -Heq_disk Hin_bound.
    by iApply "HΦ".
Qed.

Lemma wp_assert s E b:
  b = true →
  {{{ True }}} assert b @ s; E {{{ RET (); True }}}.
Proof.
  iIntros (Hb Φ) "_ HΦ". rewrite Hb -wp_bind_proc_val.
  iNext. wp_ret. by iApply "HΦ".
Qed.

Fixpoint ptr_iter (n: nat) (iters: nat) :=
  (match iters with
  | O => n d↦ 0
  | S n' => n d↦ 0 ∗ (ptr_iter (S n) n')
  end)%I.

Fixpoint rep_delete n (mem: gmap addr nat) :=
  match n with
  | O => mem
  | S n' => delete n' (rep_delete n' mem)
  end.

Lemma rep_delete_lookup m n:
  m ≥ n → rep_delete n ExMach.init_zero !! m = ExMach.init_zero !! m.
Proof.
  intros ?. induction n.
  * rewrite /rep_delete. auto.
  * rewrite /rep_delete lookup_delete_ne; last lia. eapply IHn. lia.
Qed.

Lemma disk_ptr_iter_split_aux n iters:
  n + iters < size →
  (([∗ map] i↦v ∈ rep_delete n ExMach.init_zero, i d↦ v)
     -∗ ptr_iter n iters ∗ [∗ map] i↦v ∈ rep_delete (n + S iters) ExMach.init_zero, i d↦ v)%I.
Proof.
  revert n. induction iters.
  - intros n ?. rewrite (big_opM_delete _ _ n 0); last first.
    rewrite rep_delete_lookup.
    { apply init_zero_lookup_lt_zero; first by lia. }
    { auto. }
    replace (n + 1) with (S n) by lia.
    iIntros "(?&?)". iFrame.
  - intros n ?.
    rewrite (big_opM_delete _ _ n 0); last first.
    rewrite rep_delete_lookup.
    { apply init_zero_lookup_lt_zero; first by lia. }
    { auto. }
    replace (n + S (S iters)) with (S n + S iters) by lia.
    iIntros "(?&?)". iFrame.
    iApply IHiters; first by lia.
    eauto.
Qed.

End lifting.

(* Essentially the same as the verification of the spinlock in Iris heap_lang
   except we don't allocate locks or pass the pointer to them; there is a dedicated
   lock register. *)

Class lockG Σ := LockG { lock_tokG :> inG Σ (exclR unitC) }.
Definition lockΣ : gFunctors := #[GFunctor (exclR unitC)].
Instance subG_lockΣ {Σ} : subG lockΣ Σ → lockG Σ.
Proof. solve_inG. Qed.

Section lock.
  Context `{!exmachG Σ, !lockG Σ}.

  Definition lock_inv (γ : gname) (i: addr) (P : iProp Σ) : iProp Σ :=
    ((i m↦ 0 ∗ P ∗ own γ (Excl ())) ∨ (∃ v, i m↦ v ∗ ⌜ v ≠ 0 ⌝))%I.

  Definition is_lock (N: namespace) (γ: gname) (i: addr) (P: iProp Σ) : iProp Σ :=
    (inv N (lock_inv γ i P))%I.

  Definition locked (γ: gname) : iProp Σ :=
    own γ (Excl ()).

  Global Instance is_lock_persistent N γ i R : Persistent (is_lock N γ i R).
  Proof. apply _. Qed.

  Global Instance locked_timless γ : Timeless (locked γ).
  Proof. apply _. Qed.

  Lemma lock_init N i v (R: iProp Σ) E : i m↦ v -∗ (⌜ v = 0 ⌝ -∗ R) ={E}=∗ ∃ γ, is_lock N γ i R.
  Proof.
    iIntros "Hl HR".
    iMod (own_alloc (Excl ())) as (γ) "Hexcl"; first done.
    iMod (inv_alloc N _ (lock_inv γ i R) with "[-]").
    { iNext.
      destruct (nat_eq_dec v 0).
      * subst. iLeft; iFrame. iApply "HR"; auto.
      * iRight. iExists _. iFrame. eauto.
    }
    iModIntro; iExists _; done.
  Qed.

  Lemma lock_crack N i (R: iProp Σ) γ E :
    ↑N ⊆ E →
    is_lock N γ i R ={E, E ∖ ↑N}=∗ ▷ ∃ v, i m↦ v ∗ (⌜ v = 0 ⌝ -∗ R).
  Proof.
    intros. rewrite /is_lock. iIntros "Hinv".
    iInv "Hinv" as "[(?&?&?)|HR]" "_".
    - iModIntro. iExists 0. iNext. iFrame; iIntros; auto.
    - iModIntro. iNext. iDestruct "HR" as (v) "(?&%)".
      iExists v. iFrame. iIntros; congruence.
  Qed.

  Lemma wp_lock N γ i (R: iProp Σ):
    {{{ is_lock N γ i R }}} lock i {{{ RET tt; locked γ ∗ R }}}.
  Proof.
    iIntros (Φ) "#Hlock HΦ". iLöb as "IH".
    wp_loop; wp_bind.
    iInv N as "[HL|>HUL]".
    - iDestruct "HL" as "(>H&?&>?)".
      iApply (wp_cas_suc with "[$]"). iIntros "!> Hl !>"; iFrame.
      iSplitL "Hl".
      { iRight. iNext. iExists _. iFrame. eauto. }
      rewrite //=. wp_ret. wp_ret.
      iApply "HΦ"; iFrame.
    - iDestruct "HUL" as (v) "(?&%)".
      iApply (wp_cas_fail with "[$]"); first done. iIntros "!> Hl !>"; iFrame.
      iSplitL "Hl".
      { iRight. iNext. iExists _. iFrame. eauto. }
      rewrite //=. destruct nat_eq_dec; first by congruence. wp_ret. iApply "IH"; eauto.
  Qed.

  Lemma wp_unlock N γ i (R: iProp Σ):
    {{{ is_lock N γ i R ∗ locked γ ∗ R }}} unlock i {{{ RET tt; True }}}.
  Proof.
    iIntros (Φ) "(#Hlock&Hlocked&HR) HΦ".
    iInv N as "[HL|>HUL]".
    - iDestruct "HL" as "(>H&?&>Htok)".
      iDestruct (own_valid_2 with "Htok Hlocked") as %H => //=.
    - iDestruct "HUL" as (v) "(?&%)".
      iApply (wp_write_mem with "[$]"); iIntros "!> H !>".
      iSplitR "HΦ"; last by iApply "HΦ".
      iLeft. iFrame.
  Qed.
End lock.