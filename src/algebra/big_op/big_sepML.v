From Perennial.algebra.big_op Require Import big_sepM.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.

Set Default Proof Using "Type*".

Section bi.
Context {PROP:bi}.
Implicit Types (P Q: PROP).

Section maplist.
  Context `{Countable K} {V LV : Type}.
  Implicit Types Φ Ψ : K → V → LV → PROP.
  Implicit Types m : gmap K V.
  Implicit Types l : list LV.

  Definition big_sepML_def Φ m l : PROP :=
    (∃ lm,
      ⌜ l ≡ₚ snd <$> (map_to_list lm) ⌝ ∗
      [∗ map] k ↦ v;lvm ∈ m;lm, Φ k v lvm)%I.
  Definition big_sepML_aux : seal (@big_sepML_def). Proof. by eexists. Qed.
  Definition big_sepML := unseal big_sepML_aux.
  Definition big_sepML_eq : @big_sepML = @big_sepML_def := big_sepML_aux.(seal_eq).

  Global Instance big_sepML_proper :
    Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (⊢)))
       ==> (=) ==> (Permutation) ==> (⊢))
           (big_sepML).
  Proof.
    intros P0 P1 HP.
    intros m0 m Hm; subst.
    intros l0 l1 Hl.
    rewrite big_sepML_eq.
    iIntros "Hml".
    iDestruct "Hml" as (lm) "[Hlm Hml]".
    rewrite Hl.
    iExists lm; iFrame.
    iSplitR; first done.
    iApply big_sepM2_mono; iFrame.
    iIntros (k v lv ? ?) "H".
    iApply HP; iFrame.
  Qed.

  Theorem big_sepML_empty Φ `{!∀ k v lv, Absorbing (Φ k v lv)} :
    ⊢ big_sepML Φ ∅ nil.
  Proof.
    iIntros.
    rewrite big_sepML_eq.
    iExists ∅.
    eauto.
  Qed.

  Theorem big_sepML_insert Φ m l k v lv `{!∀ k v lv, Absorbing (Φ k v lv)} :
    m !! k = None ->
    Φ k v lv ∗ big_sepML Φ m l -∗
    big_sepML Φ (<[k := v]> m) (lv :: l).
  Proof.
    iIntros "% [Hp Hml]".
    rewrite big_sepML_eq.
    iDestruct "Hml" as (lm) "[% Hml]".
    iDestruct (big_sepM2_lookup_1_none with "Hml") as %Hlmnone; eauto.
    iExists (<[k := lv]> lm).
    iSplitR.
    - iPureIntro.
      rewrite map_to_list_insert; eauto.
      rewrite /=.
      rewrite H2.
      reflexivity.
    - iApply big_sepM2_insert; eauto.
      iFrame.
  Qed.

  Theorem big_sepML_insert_app Φ m l k v lv `{!∀ k v lv, Absorbing (Φ k v lv)} :
    m !! k = None ->
    Φ k v lv ∗ big_sepML Φ m l -∗
    big_sepML Φ (<[k := v]> m) (l ++ [lv]).
  Proof.
    iIntros "% [Hp Hml]".
    rewrite -Permutation_cons_append.
    iApply big_sepML_insert; eauto; iFrame.
  Qed.

  Theorem big_sepML_delete_cons Φ m l lv `{!∀ k v lv, Absorbing (Φ k v lv)} :
    big_sepML Φ m (lv :: l) -∗
    ∃ k v,
      ⌜ m !! k = Some v ⌝ ∗
      Φ k v lv ∗
      big_sepML Φ (delete k m) l.
  Proof.
    iIntros "Hml".
    rewrite big_sepML_eq.
    iDestruct "Hml" as (lm) "[% Hml]".
    assert (lv ∈ lv :: l) by apply elem_of_list_here.
    setoid_rewrite H1 in H2.
    apply elem_of_list_fmap_2 in H2 as [[k lv0] H2].
    simpl in H2; intuition subst.
    apply elem_of_map_to_list in H4.
    iDestruct (big_sepM2_lookup_2_some with "Hml") as %[v Hmk]; eauto.
    iExists _, _.
    iSplitR; eauto.
    iDestruct (big_sepM2_delete with "Hml") as "[Hp Hml]"; eauto.
    iFrame.
    iExists _.
    iSplitR; last iFrame.
    iPureIntro.
    replace lm with (<[k := lv0]> (delete k lm)) in H1.
    2: {
      rewrite insert_delete.
      rewrite insert_id; eauto.
    }
    setoid_rewrite map_to_list_insert in H1.
    2: apply lookup_delete.
    simpl in H1.
    apply Permutation.Permutation_cons_inv in H1.
    done.
  Qed.

  Lemma map_to_list_insert_overwrite (l : list LV) (i : nat) (k : K) (lv lv' : LV) (lm : gmap K LV) :
    l !! i = Some lv ->
    lm !! k = Some lv ->
    l ≡ₚ (map_to_list lm).*2 ->
    <[i := lv']> l ≡ₚ (map_to_list (<[k := lv']> lm)).*2.
  Proof.
    intros.
    rewrite -insert_delete.
    rewrite map_to_list_insert.
    2: apply lookup_delete.

    erewrite delete_Permutation in H2; eauto.
    erewrite (delete_Permutation _ i lv').
    2: { rewrite list_lookup_insert; eauto.
         eapply lookup_lt_Some; eauto. }
    erewrite <- (insert_id lm) in H2; eauto.
    rewrite -insert_delete in H2.
    erewrite map_to_list_insert in H2.
    2: apply lookup_delete.
    simpl in *.
    apply Permutation.Permutation_cons_inv in H2.
    rewrite -H2.
    eapply Permutation_cons.
    repeat rewrite delete_take_drop.
    rewrite -> take_insert by lia.
    rewrite -> drop_insert_gt by lia.
    eauto.
  Qed.

  Lemma map_to_list_delete (l : list LV) (lm : gmap K LV) (k : K) (i : nat) (x : LV) :
    l !! i = Some x ->
    lm !! k = Some x ->
    l ≡ₚ (map_to_list lm).*2 ->
    delete i l ≡ₚ (map_to_list (delete k lm)).*2.
  Proof.
    intros.
    erewrite delete_Permutation in H2; eauto.
    erewrite <- (insert_id lm) in H2; eauto.
    rewrite -insert_delete in H2.
    erewrite map_to_list_insert in H2.
    2: apply lookup_delete.
    simpl in *.
    apply Permutation.Permutation_cons_inv in H2.
    eauto.
  Qed.

  Theorem big_sepML_delete_m Φ m l k v `{!∀ k v lv, Absorbing (Φ k v lv)} :
    m !! k = Some v ->
    big_sepML Φ m l -∗
    ∃ i lv,
      ⌜ l !! i = Some lv ⌝ ∗
      Φ k v lv ∗
      big_sepML Φ (delete k m) (delete i l).
  Proof.
    iIntros (Hm) "Hml".
    rewrite big_sepML_eq.
    iDestruct "Hml" as (lm) "[% Hml]".
    iDestruct (big_sepM2_lookup_1_some with "Hml") as (x2) "%"; eauto.
    iDestruct (big_sepM2_delete with "Hml") as "[Hk Hml]"; eauto.

    apply elem_of_map_to_list in H2 as H2'.
    eapply (elem_of_list_fmap_1 snd) in H2'.
    rewrite <- H1 in H2'.
    eapply elem_of_list_lookup_1 in H2'.
    destruct H2'.

    iExists _, _; iFrame.
    iSplitR; eauto.

    iExists _; iFrame.
    iPureIntro.
    eapply map_to_list_delete; eauto.
  Qed.

  Lemma list_some_map_to_list (l : list LV) (i : nat) (lv : LV) (lm : gmap K LV) :
    l !! i = Some lv ->
    l ≡ₚ (map_to_list lm).*2 ->
    ∃ k,
      lm !! k = Some lv.
  Proof.
    intros.
    assert (lv ∈ l). { eapply elem_of_list_lookup_2; eauto. }
    rewrite -> H1 in H2.
    eapply elem_of_list_fmap_2 in H2.
    destruct H2. intuition subst.
    destruct x.
    apply elem_of_map_to_list in H4.
    eexists. eauto.
  Qed.

  Lemma map_to_list_some_list (l : list LV) (k : K) (lv : LV) (lm : gmap K LV) :
    lm !! k = Some lv ->
    l ≡ₚ (map_to_list lm).*2 ->
    ∃ (i : nat),
      l !! i = Some lv.
  Proof.
    intros.
    apply elem_of_map_to_list in H0.
    eapply elem_of_list_fmap_1 in H0.
    erewrite <- H1 in H0.
    eapply elem_of_list_lookup_1 in H0.
    eauto.
  Qed.

  Theorem big_sepML_lookup_l_acc Φ m l i lv `{!∀ k v lv, Absorbing (Φ k v lv)} :
    l !! i = Some lv ->
    big_sepML Φ m l -∗
    ∃ k v, ⌜ m !! k = Some v ⌝ ∗ Φ k v lv ∗
    ∀ v' lv',
      Φ k v' lv' -∗
      big_sepML Φ (<[k := v']> m) (<[i := lv']> l).
  Proof.
    iIntros (Hi) "Hml".
    rewrite big_sepML_eq /big_sepML_def.
    iDestruct "Hml" as (lm) "[% Hml]".
    eapply list_some_map_to_list in Hi as Hi'; eauto. destruct Hi'.
    iDestruct (big_sepM2_lookup_2_some with "Hml") as (xm) "%"; eauto.
    iDestruct (big_sepM2_insert_acc with "Hml") as "[Hx Hml]"; eauto.
    iExists _, _.
    iSplitR; first by done.
    iFrame.
    iIntros (v' lv') "Hx".
    iSpecialize ("Hml" with "Hx").
    iExists (<[x:=lv']> lm). iFrame.
    iPureIntro.
    eapply map_to_list_insert_overwrite; eauto.
  Qed.

  Theorem big_sepML_lookup_l_app_acc Φ m lv l0 l1 `{!∀ k v lv, Absorbing (Φ k v lv)} :
    big_sepML Φ m (l0 ++ lv :: l1) -∗
    ∃ k v, ⌜ m !! k = Some v ⌝ ∗ Φ k v lv ∗
    ∀ v' lv',
      Φ k v' lv' -∗
      big_sepML Φ (<[k := v']> m) (l0 ++ lv' :: l1).
  Proof.
    iIntros "Hml".
    iDestruct (big_sepML_lookup_l_acc with "Hml") as "Hres".
    { rewrite lookup_app_r. erewrite Nat.sub_diag. eauto. lia. }
    iDestruct "Hres" as (k v) "(% & Hk & Hml)".
    iExists _, _.
    iSplitR; first eauto.
    iFrame.
    iIntros (v' lv') "Hk".
    iSpecialize ("Hml" with "Hk").
    replace (length l0) with (length l0 + 0) by lia.
    rewrite insert_app_r. simpl. iFrame.
  Qed.

  Theorem big_sepML_lookup_m_acc Φ m l k v `{!∀ k v lv, Absorbing (Φ k v lv)} :
    m !! k = Some v ->
    big_sepML Φ m l -∗
    ∃ i lv, ⌜ l !! i = Some lv ⌝ ∗ Φ k v lv ∗
    ∀ v' lv',
      Φ k v' lv' -∗
      big_sepML Φ (<[k := v']> m) (<[i := lv']> l).
  Proof.
    iIntros (Hi) "Hml".
    rewrite big_sepML_eq /big_sepML_def.
    iDestruct "Hml" as (lm) "[% Hml]".
    iDestruct (big_sepM2_lookup_1_some with "Hml") as (xm) "%"; eauto.
    iDestruct (big_sepM2_insert_acc with "Hml") as "[Hx Hml]"; eauto.
    eapply map_to_list_some_list in H2 as H2'; eauto. destruct H2'.
    iExists _, _.
    iSplitR; first by done.
    iFrame.
    iIntros (v' lv') "Hx".
    iSpecialize ("Hml" with "Hx").
    iExists (<[k := lv']> lm). iFrame.
    iPureIntro.
    eapply map_to_list_insert_overwrite; eauto.
  Qed.

  Theorem big_sepML_mono Φ Ψ m l `{!∀ k v lv, Absorbing (Φ k v lv)} `{!∀ k v lv, Absorbing (Ψ k v lv)} :
    big_sepML Φ m l -∗
    ⌜ ∀ k v lv, Φ k v lv -∗ Ψ k v lv ⌝ -∗
    big_sepML Ψ m l.
  Proof.
    rewrite big_sepML_eq; iIntros "Hml %".
    iDestruct "Hml" as (lm) "[% Hml]".
    iExists lm; iSplitR; first by eauto.
    iApply big_sepM2_mono; eauto.
  Qed.

  Theorem big_sepML_lookup_l_Some Φ m l i lv `{!∀ k v lv, Absorbing (Φ k v lv)} :
    l !! i = Some lv ->
    big_sepML Φ m l -∗
    ⌜ ∃ k v, m !! k = Some v ⌝.
  Proof.
    iIntros (Hl) "Hml".
    iDestruct (big_sepML_lookup_l_acc with "Hml") as (k v) "[% Hml]"; eauto.
  Qed.

  Theorem big_sepML_lookup_m_Some Φ m l k v `{!∀ k v lv, Absorbing (Φ k v lv)} :
    m !! k = Some v ->
    big_sepML Φ m l -∗
    ⌜ ∃ i lv, l !! i = Some lv ⌝.
  Proof.
    iIntros (Hm) "Hml".
    iDestruct (big_sepML_lookup_m_acc with "Hml") as (i lv) "[% Hml]"; eauto.
  Qed.

  Theorem big_sepML_empty_m Φ m `{!∀ k v lv, Absorbing (Φ k v lv)} :
    big_sepML Φ m [] -∗
    ⌜ m = ∅ ⌝.
  Proof.
    rewrite big_sepML_eq /big_sepML_def.
    iIntros "Hml".
    iDestruct "Hml" as (lm) "[% Hml]".
    destruct (map_to_list lm) eqn:Heq.
    - apply map_to_list_empty_inv in Heq; subst.
      iDestruct (big_sepM2_empty_l with "Hml") as %He. done.
    - simpl in *. apply Permutation_nil_cons in H1. eauto.
  Qed.

  Theorem big_sepML_empty_l Φ l `{!∀ k v lv, Absorbing (Φ k v lv)} :
    big_sepML Φ ∅ l -∗
    ⌜ l = [] ⌝.
  Proof.
    rewrite big_sepML_eq /big_sepML_def.
    iIntros "Hml".
    iDestruct "Hml" as (lm) "[% Hml]".
    iDestruct (big_sepM2_empty_r with "Hml") as %He; subst.
    rewrite map_to_list_empty /= in H1.
    iPureIntro. eapply Permutation.Permutation_nil. done.
  Qed.

  Theorem big_sepML_sep Φ Ψ m l :
    big_sepML (λ k v lv, Φ k v lv ∗ Ψ k v lv) m l -∗
    big_sepML Φ m l ∗ big_sepML Ψ m l.
  Proof.
    iIntros "Hml".
    rewrite big_sepML_eq.
    iDestruct "Hml" as (lm) "[% Hml]".
    iDestruct (big_sepM2_sep with "Hml") as "[Hml0 Hml1]".
    iSplitL "Hml0".
    { iExists _. iFrame. done. }
    { iExists _. iFrame. done. }
  Qed.

  Context `{BiAffine PROP}.
  Theorem big_sepML_sepM Φ (P : K -> V -> PROP) m l `{!∀ k v, Absorbing (P k v)}:
    big_sepML (λ k v lv, Φ k v lv ∗ P k v) m l ⊣⊢
    big_sepML Φ m l ∗ big_opM _ P m.
  Proof.
    rewrite big_sepML_eq; iSplit.
    - iIntros "Hlm".
      iDestruct "Hlm" as (lm) "[% Hlm]".
      iDestruct (big_sepM2_sep with "Hlm") as "[Hlm0 Hlm1]".
      iSplitL "Hlm0".
      + iExists _. iFrame. done.
      + iDestruct (big_sepM2_sepM_1 with "Hlm1") as "Hlm1".
        iDestruct (big_sepM_mono with "Hlm1") as "Hlm1"; last by iFrame.
        iIntros (k x Hkx) "H".
        iDestruct "H" as (y2) "[% H]". iFrame.
    - iIntros "[Hlm Hm]".
      iDestruct "Hlm" as (lm) "[% Hlm]".
      iExists _. iSplitR; first by eauto.
      iDestruct (big_sepM2_dom with "Hlm") as "%Hmlm".
      iApply big_sepM2_sep; iFrame.
      rewrite big_sepM2_eq /big_sepM2_def.
      iSplit.
      { iPureIntro. split; intros.
        { apply (elem_of_dom (D:=gset K)). rewrite -Hmlm. apply elem_of_dom. eauto. }
        { apply (elem_of_dom (D:=gset K)). rewrite Hmlm. apply elem_of_dom. eauto. }
      }
      clear H2.
      iInduction m as [|i x m] "IH" using map_ind forall (lm Hmlm).
      { rewrite dom_empty_L in Hmlm. rewrite (dom_empty_inv_L (D:=gset K) lm); eauto.
        rewrite map_zip_empty_l. iApply big_sepM_empty. done. }
      iDestruct (big_sepM_insert with "Hm") as "[Hi Hm]"; eauto.
      assert (is_Some (lm !! i)) as Hlmi.
      { apply (elem_of_dom (D:=gset K)). rewrite -Hmlm. apply elem_of_dom. rewrite lookup_insert; eauto. }
      destruct Hlmi.
      replace lm with (<[i:=x0]> (delete i lm)).
      2: { rewrite insert_delete insert_id; eauto. }
      rewrite map_zip_insert.
      iApply big_sepM_insert.
      { rewrite map_zip_lookup_none_1; eauto. }
      iFrame.
      iApply "IH"; last by iFrame.
      iPureIntro.
      rewrite dom_delete_L -Hmlm dom_insert_L.
      assert (i ∉ dom (gset K) m).
      { apply not_elem_of_dom. eauto. }
      set_solver.
  Qed.

  Theorem big_sepML_sepL_split Φ (P : LV -> PROP) m l `{!∀ lv, Absorbing (P lv)}:
    big_sepML (λ k v lv, Φ k v lv ∗ P lv) m l -∗
    big_sepML Φ m l ∗ big_opL _ (λ i, P) l.
  Proof.
    rewrite big_sepML_eq.
    iIntros "Hlm".
    iDestruct "Hlm" as (lm) "[% Hlm]".
    iDestruct (big_sepM2_sep with "Hlm") as "[Hlm0 Hlm1]".
    iSplitL "Hlm0".
    + iExists _. iFrame. done.
    + iDestruct (big_sepM2_sepM_2 with "Hlm1") as "Hlm1".
      rewrite big_opM_eq /big_opM_def H2 big_sepL_fmap.
      iApply big_sepL_mono; last by iFrame.
      iIntros (???) "H".
      destruct y.
      iDestruct "H" as (?) "[% H]". iFrame.
  Qed.

  Theorem big_sepML_sepL_combine Φ (P : LV -> PROP) m l `{!∀ lv, Absorbing (P lv)}:
    big_sepML Φ m l ∗ big_opL _ (λ i, P) l -∗
    big_sepML (λ k v lv, Φ k v lv ∗ P lv) m l.
  Proof.
    rewrite big_sepML_eq.
    iIntros "Hlm".
    iDestruct "Hlm" as "[Hlm Hl]".
    iDestruct "Hlm" as (lm) "[% Hlm]".
    iExists _. iSplitR; first by eauto.
    rewrite big_sepM2_eq /big_sepM2_def.
    iDestruct "Hlm" as "[% Hlm]".
    iSplit; eauto.
    rewrite H2.
    iApply big_sepM_sep; iFrame.

    clear H2.
    iInduction lm as [|i x lm] "IH" using map_ind forall (m H3).
    { rewrite map_zip_empty_r. iApply big_sepM_empty. done. }
    rewrite map_to_list_insert; eauto.
    rewrite fmap_cons /=.
    iDestruct "Hl" as "[Hx Hl]".
    assert (is_Some (m !! i)) as Hmi.
    { apply H3. rewrite lookup_insert. eauto. }
    destruct Hmi.
    replace m with (<[i:=x0]> (delete i m)).
    2: { rewrite insert_delete insert_id; eauto. }
    rewrite map_zip_insert.
    iApply big_sepM_insert.
    { rewrite map_zip_lookup_none_2; eauto. }
    iFrame.
    iApply "IH"; last by iFrame.

    iPureIntro.
    split; intros.
    - destruct (decide (i = k)); subst.
      + rewrite lookup_delete in H5. inversion H5. congruence.
      + rewrite lookup_delete_ne in H5; eauto.
        apply H3 in H5. rewrite lookup_insert_ne in H5; eauto.
    - destruct (decide (i = k)); subst.
      + inversion H5. congruence.
      + rewrite lookup_delete_ne; eauto.
        eapply H3. rewrite lookup_insert_ne; eauto.
  Qed.

  Theorem big_sepML_sepL Φ (P : LV -> PROP) m l `{!∀ lv, Absorbing (P lv)}:
    big_sepML (λ k v lv, Φ k v lv ∗ P lv) m l ⊣⊢
    big_sepML Φ m l ∗ big_opL _ (λ i, P) l.
  Proof.
    iSplit.
    - iApply big_sepML_sepL_split.
    - iApply big_sepML_sepL_combine.
  Qed.

  Theorem big_sepML_sepL_exists Φ m l `{!∀ k v lv, Absorbing (Φ k v lv)}:
    big_sepML Φ m l -∗
    big_opL _ (λ _ lv, ∃ k v, ⌜ m !! k = Some v ⌝ ∗ Φ k v lv) l.
  Proof.
    rewrite big_sepML_eq /big_sepML_def.
    iIntros "Hml".
    iDestruct "Hml" as (lm) "[%Hllm Hml]".
    iDestruct (big_sepM2_sepM_2 with "Hml") as "Hlm".

    rewrite Hllm; clear Hllm.
    iInduction lm as [|i x lm] "IH" using map_ind.
    { rewrite map_to_list_empty. done. }
    iDestruct (big_sepM_insert with "Hlm") as "[Hi Hlm]"; eauto.
    rewrite map_to_list_insert; eauto.
    rewrite fmap_cons /=.
    iSplitL "Hi".
    { iExists _. iFrame. }
    iApply "IH". iFrame.
  Qed.

  Global Instance big_sepML_persistent `(!∀ k v lv, Persistent (Φ k v lv)) :
    Persistent (big_sepML Φ m l).
  Proof.
    rewrite big_sepML_eq.
    typeclasses eauto.
  Qed.

  Global Instance big_sepML_absorbing `(!∀ k v lv, Absorbing (Φ k v lv)) :
    Absorbing (big_sepML Φ m l).
  Proof.
    rewrite big_sepML_eq.
    typeclasses eauto.
  Qed.

End maplist.

Section maplist2.
  Context `{Countable K} {V W LV : Type}.
  Implicit Types Φ : K → V → LV → PROP.
  Implicit Types v : V.
  Implicit Types w : W.
  Implicit Types mv : gmap K V.
  Implicit Types mw : gmap K W.
  Implicit Types l : list LV.

  Context `{BiAffine PROP}.

  Theorem big_sepML_map_val_exists_helper Φ mv l (R : K -> V -> W -> Prop)
      `{!∀ k v lv, Absorbing (Φ k v lv)} :
    big_sepML Φ mv l -∗
    □ ( ∀ k v lv,
      ⌜ mv !! k = Some v ⌝ -∗
      Φ k v lv -∗
      ⌜ ∃ w, R k v w ⌝ ) -∗
    ∃ mw,
      ⌜ dom (gset K) mw = dom (gset K) mv ⌝ ∗
      big_sepML (λ k w lv, ∃ v, ⌜ R k v w ⌝ ∗ Φ k v lv) mw l.
  Proof.
    iIntros "Hml HR".
    iInduction l as [|] "Hi" forall (mv).
    - iExists ∅.
      iDestruct (big_sepML_empty_m with "Hml") as "->".
      iSplit; last by iApply big_sepML_empty.
      repeat rewrite dom_empty_L; eauto.
    - iDestruct (big_sepML_delete_cons with "Hml") as (k v) "(%Hdelete_lookup & Hk & Hml)".
      iDestruct "HR" as "#HR".
      iSpecialize ("Hi" with "Hml [HR]").
      { iModIntro.
        iIntros. iApply "HR"; last by iFrame.
        apply lookup_delete_Some in H2; intuition eauto. }
      iDestruct "Hi" as (mw) "[%Hdel Hi]".
      iDestruct ("HR" with "[] Hk") as (w) "%HR"; eauto.
      iExists (<[k := w]> mw).
      iSplitR.
      { iPureIntro. rewrite dom_insert_L Hdel dom_delete_L.
        assert (k ∈ dom (gset K) mv).
        { apply elem_of_dom; eauto. }
        rewrite -union_difference_L; eauto.
        set_solver.
      }
      iDestruct (big_sepML_insert with "[$Hi Hk]") as "Hml".
      2: { iExists _. iFrame. done. }
      2: iFrame.
      apply (not_elem_of_dom (D:=gset K)). rewrite Hdel. set_solver.
  Qed.

  Theorem big_sepML_map_val_exists Φ mv l (R : K -> V -> W -> Prop)
      `{!∀ k v lv, Absorbing (Φ k v lv)} :
    big_sepML Φ mv l -∗
    □ ( ∀ k v lv,
      ⌜ mv !! k = Some v ⌝ -∗
      Φ k v lv -∗
      ⌜ ∃ w, R k v w ⌝ ) -∗
    ∃ mw,
      big_sepML (λ k w lv, ∃ v, ⌜ R k v w ⌝ ∗ Φ k v lv) mw l.
  Proof.
    iIntros "Hml HR".
    iDestruct (big_sepML_map_val_exists_helper with "Hml HR") as (mw) "[% H]".
    iExists _; iFrame.
  Qed.

  Theorem big_sepML_exists (Φw : K -> V -> LV -> W -> PROP) m l
      `{!∀ k v lv w, Absorbing (Φw k v lv w)} :
    big_sepML (λ k v lv, ∃ w, Φw k v lv w) m l -∗
    ∃ lw,
      ⌜ l = fst <$> lw ⌝ ∗
      big_sepML (λ k v lv, Φw k v (fst lv) (snd lv)) m lw.
  Proof.
    iIntros "Hml".
    iInduction l as [|] "Hi" forall (m).
    - iExists nil.
      iDestruct (big_sepML_empty_m with "Hml") as "->".
      iSplitR; first by done.
      iApply big_sepML_empty.
    - iDestruct (big_sepML_delete_cons with "Hml") as (k v) "(% & Hk & Hml)".
      iDestruct "Hk" as (w) "Hk".
      iSpecialize ("Hi" with "Hml").
      iDestruct "Hi" as (lw) "(% & Hi)".
      iExists ((a, w) :: lw).
      iSplitR; first by subst; eauto.
      replace m with (<[k := v]> (delete k m)) at 2.
      2: { rewrite insert_delete. rewrite insert_id; eauto. }
      iApply big_sepML_insert.
      { rewrite lookup_delete; eauto. }
      iFrame.
  Qed.

End maplist2.

Theorem big_sepL_impl A (f g: nat -> A -> PROP) (l: list A) :
  (forall i x, f i x -∗ g i x) ->
  ([∗ list] i↦x ∈ l, f i x) -∗
  ([∗ list] i↦x ∈ l, g i x).
Proof.
  intros Himpl.
  apply big_opL_gen_proper; auto.
  typeclasses eauto.
Qed.

Definition Conflicting {L V} (P0 P1 : L -> V -> PROP) :=
  ∀ a0 v0 a1 v1,
    P0 a0 v0 -∗ P1 a1 v1 -∗ ⌜ a0 ≠ a1 ⌝.

Lemma big_sepM_disjoint_pred {L V} {P0 P1 : L -> V -> PROP} `{!EqDecision L} `{!Countable L}
  `{!∀ l v, Absorbing (P0 l v)}
  `{!∀ l v, Absorbing (P1 l v)}
  `(Conflicting P0 P1)
  (m0 m1 : gmap L V) :
  ( ( [∗ map] a↦v ∈ m0, P0 a v ) -∗
    ( [∗ map] a↦v ∈ m1, P1 a v ) -∗
    ⌜ m0 ##ₘ m1 ⌝ ).
Proof.
  iIntros "H0 H1".
  iIntros (i).
  unfold option_relation.
  destruct (m0 !! i) eqn:He; destruct (m1 !! i) eqn:H1; try solve [ iPureIntro; auto ].
  iDestruct (big_sepM_lookup with "H0") as "H0"; eauto.
  iDestruct (big_sepM_lookup with "H1") as "H1"; eauto.
  iDestruct (Conflicting0 with "H0 H1") as %Hcc.
  congruence.
Qed.

End bi.

Notation "'[∗' 'maplist]' k ↦ x ; v ∈ m ; l , P" :=
  (big_sepML (λ k x v, P) m l)
  (at level 200, m, l at level 10, k, x, v at level 1, right associativity,
   format "[∗  maplist]  k ↦ x ; v  ∈  m ; l ,  P")
  : bi_scope.

Opaque big_sepML.

Section big_sepms_def.

  Context {PROP : bi}.
  Context `{Countable K}.

  Inductive bsm_maps : Type :=
  | bsm_cons : ∀ {T : Type} (m : gmap K T) (ms' : bsm_maps), bsm_maps
  | bsm_nil : bsm_maps
  .

  Fixpoint bsm_pred (ms : bsm_maps) : Type :=
    match ms with
    | @bsm_cons T _ ms' => T -> bsm_pred ms'
    | bsm_nil => PROP
    end.

  Fixpoint bsm_keys_match (keys : gset K) (ms : bsm_maps) : Prop :=
    match ms with
    | @bsm_cons T m ms' =>
      keys = dom (gset K) m ∧
      bsm_keys_match keys ms'
    | bsm_nil => True
    end.

  Fixpoint bsm_key_pred (k : K) (ms : bsm_maps) (P : bsm_pred ms) {struct ms} : PROP.
    destruct ms.
    - exact (∃ (v : T), ⌜ m !! k = Some v ⌝ ∗ bsm_key_pred k ms (P v))%I.
    - exact P.
  Defined.

  Definition big_sepMs (ms : bsm_maps) (P : K -> bsm_pred ms) : PROP :=
    ( ∃ (keys : gset K),
        ⌜ bsm_keys_match keys ms ⌝ ∗
        [∗ set] k ∈ keys, bsm_key_pred k ms (P k)
    )%I.

End big_sepms_def.

Declare Scope big_sepms_maps_scope.
Delimit Scope big_sepms_maps_scope with big_sepms_maps.
Notation "[ mx ]" :=
  (bsm_cons mx bsm_nil)
  : big_sepms_maps_scope.
Notation "[ mx ; my ; .. ; mz ]" :=
  (bsm_cons mx (bsm_cons my .. (bsm_cons mz bsm_nil) ..))
  : big_sepms_maps_scope.

Notation "'[∗' 'maps]' k ↦ x ; .. ; y ∈ ms , P" :=
  (big_sepMs ms%big_sepms_maps (fun k => (fun x => .. (fun y => P) .. )))
  (at level 200, ms at level 10, k at level 1,
   x closed binder, y closed binder,
   right associativity,
   format "[∗  maps]  k ↦ x ; .. ; y  ∈  ms ,  P")
  : bi_scope.

Section big_sepms.

  Context {PROP : bi}.
  Context `{Countable K}.
  Variable (A : Type).

  Theorem big_sepM_sepMs (m : gmap K A) (P : K -> A -> PROP):
    ( [∗ map] k ↦ v ∈ m, P k v ) -∗
    [∗ maps] k ↦ v ∈ [m], P k v.
  Proof.
  Abort.

End big_sepms.
