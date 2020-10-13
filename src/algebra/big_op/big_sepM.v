From iris.algebra Require Export big_op.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.

Set Default Proof Using "Type".

(*! Map filter *)
Section filter.
  Context `{Countable K}.
  Context {A B : Type}.

  Theorem map_filter_lookup_key_in (m : gmap K A) (P : K -> Prop)
      (_ : ∀ (ka : K * A), Decision (P ka.1)) i :
    P i ->
    filter (λ x, P x.1) m !! i = m !! i.
  Proof.
    destruct (m !! i) eqn:He; intros.
    - rewrite map_filter_lookup_Some; eauto.
    - rewrite map_filter_lookup_None; eauto.
  Qed.

  Theorem map_filter_lookup_key_notin (m : gmap K A) (P : K -> Prop)
      (_ : ∀ (ka : K * A), Decision (P ka.1)) i :
    ~ P i ->
    filter (λ x, P x.1) m !! i = None.
  Proof.
    rewrite map_filter_lookup_None; eauto.
  Qed.

  Lemma filter_same_keys_0' (m1 : gmap K A) (m2 : gmap K B) (P : K -> Prop)
                            `{Hdka : ∀ (ka : K * A), Decision (P ka.1)}
                            `{Hdkb : ∀ (kb : K * B), Decision (P kb.1)} :
    (∀ k, is_Some (m1 !! k) -> is_Some (m2 !! k)) ->
    ∀ k, is_Some (filter (λ x, P x.1) m1 !! k) ->
         is_Some (filter (λ x, P x.1) m2 !! k).
  Proof.
    intros.
    destruct H1.
    eapply map_filter_lookup_Some in H1. destruct H1.
    assert (is_Some (m2 !! k)).
    { apply H0. eauto. }
    destruct H3.
    eexists.
    eapply map_filter_lookup_Some. eauto.
  Qed.

  Lemma filter_same_keys_1' (m1 : gmap K A) (m2 : gmap K B) (P : K -> Prop)
                            `{Hdk : ∀ k, Decision (P k)}
                            `{Hdka : ∀ (ka : K * A), Decision (P ka.1)}
                            `{Hdkb : ∀ (kb : K * B), Decision (P kb.1)} :
    (∀ k, is_Some (filter (λ x, P x.1) m1 !! k) ->
          is_Some (filter (λ x, P x.1) m2 !! k)) ->
    (∀ k, is_Some (filter (λ x, ¬ P x.1) m1 !! k) ->
          is_Some (filter (λ x, ¬ P x.1) m2 !! k)) ->
    ∀ k, is_Some (m1 !! k) -> is_Some (m2 !! k).
  Proof.
    intros.
    destruct H2.
    destruct (decide (P k)).
    - edestruct H0.
      { eexists. eapply map_filter_lookup_Some. eauto. }
      eapply map_filter_lookup_Some in H3. intuition eauto.
    - edestruct H1.
      { eexists. eapply map_filter_lookup_Some. eauto. }
      eapply map_filter_lookup_Some in H3. intuition eauto.
  Qed.
End filter.

Lemma filter_same_keys_0 `{Countable K} `(m1 : gmap K A) `(m2 : gmap K B) (P : K -> Prop)
                         `{Hdka : ∀ (ka : K * A), Decision (P ka.1)}
                         `{Hdkb : ∀ (kb : K * B), Decision (P kb.1)} :
  (∀ k, is_Some (m1 !! k) <-> is_Some (m2 !! k)) ->
  ∀ k, is_Some (filter (λ x, P x.1) m1 !! k) <->
       is_Some (filter (λ x, P x.1) m2 !! k).
Proof.
  split.
  - apply filter_same_keys_0'. intros. eapply H0. eauto.
  - apply filter_same_keys_0'. intros. eapply H0. eauto.
Qed.

Lemma filter_same_keys_1 `{Countable K} `(m1 : gmap K A) `(m2 : gmap K B) (P : K -> Prop)
                         `{Hdk : ∀ k, Decision (P k)}
                         `{Hdka : ∀ (ka : K * A), Decision (P ka.1)}
                         `{Hdkb : ∀ (kb : K * B), Decision (P kb.1)} :
  (∀ k, is_Some (filter (λ x, P x.1) m1 !! k) <->
        is_Some (filter (λ x, P x.1) m2 !! k)) ->
  (∀ k, is_Some (filter (λ x, ¬ P x.1) m1 !! k) <->
        is_Some (filter (λ x, ¬ P x.1) m2 !! k)) ->
  ∀ k, is_Some (m1 !! k) <-> is_Some (m2 !! k).
Proof.
  split.
  - eapply filter_same_keys_1'; eauto.
    + intros; eapply H0; eauto.
    + intros; eapply H1; eauto.
  - eapply filter_same_keys_1'; eauto.
    + intros; eapply H0; eauto.
    + intros; eapply H1; eauto.
Qed.

(*! map_zip *)
Section map_zip.
  Context `{Countable K}.
  Context {A B: Type}.

  Theorem map_zip_empty_l (m2 : gmap K B) :
    map_zip (∅ : gmap K A) m2 = ∅.
  Proof.
    rewrite /map_zip.
    apply map_eq; intros.
    erewrite lookup_merge by reflexivity.
    rewrite !lookup_empty; eauto.
  Qed.

  Theorem map_zip_empty_r (m1 : gmap K A) :
    map_zip m1 (∅ : gmap K B) = ∅.
  Proof.
    rewrite /map_zip.
    apply map_eq; intros.
    erewrite lookup_merge by reflexivity.
    rewrite !lookup_empty; eauto.
    destruct (m1 !! i); eauto.
  Qed.

  Theorem map_zip_insert (m1 : gmap K A) (m2 : gmap K B) i v1 v2 :
    map_zip (<[i:=v1]> m1) (<[i:=v2]> m2) =
    <[i:=(v1, v2)]> (map_zip m1 m2).
  Proof.
    rewrite /map_zip.
    apply map_eq; intros.
    destruct (decide (i = i0)); subst.
    - erewrite lookup_merge by reflexivity.
      rewrite !lookup_insert. eauto.
    - erewrite lookup_merge by reflexivity.
      rewrite !lookup_insert_ne; eauto.
      erewrite lookup_merge by reflexivity.
      eauto.
  Qed.

  Theorem map_zip_lookup_none_1 (m1 : gmap K A) (m2 : gmap K B) i :
    m1 !! i = None ->
    map_zip m1 m2 !! i = None.
  Proof.
    intros; rewrite /map_zip.
    erewrite lookup_merge by reflexivity.
    rewrite H0; eauto.
  Qed.

  Theorem map_zip_lookup_none_2 (m1 : gmap K A) (m2 : gmap K B) i :
    m2 !! i = None ->
    map_zip m1 m2 !! i = None.
  Proof.
    intros; rewrite /map_zip.
    erewrite lookup_merge by reflexivity.
    destruct (m1 !! i); eauto; rewrite H0; eauto.
  Qed.

  Theorem map_zip_lookup_some (m1 : gmap K A) (m2 : gmap K B) i v1 v2:
    m1 !! i = Some v1 ->
    m2 !! i = Some v2 ->
    map_zip m1 m2 !! i = Some (v1, v2).
  Proof.
    intros; rewrite /map_zip.
    erewrite lookup_merge by reflexivity.
    rewrite H0 H1. eauto.
  Qed.

  Theorem map_zip_filter (m1 : gmap K A) (m2 : gmap K B) (P : K -> Prop)
    `{Hdk : ∀ k, Decision (P k)}
    `{Hdka : ∀ (ka : K * A), Decision (P ka.1)}
    `{Hdkb : ∀ (kb : K * B), Decision (P kb.1)}
    `{Hdkab : ∀ (kab : K * (A * B)), Decision (P kab.1)} :
    map_zip (filter (λ x, P x.1) m1) (filter (λ x, P x.1) m2) =
    filter (λ x, P x.1) (map_zip m1 m2).
  Proof.
    rewrite /map_zip.
    apply map_eq; intros.
    erewrite lookup_merge by reflexivity.
    destruct (decide (P i)).
    - rewrite !map_filter_lookup_key_in; eauto.
      erewrite lookup_merge by reflexivity; eauto.
    - rewrite !map_filter_lookup_key_notin; eauto.
  Qed.
End map_zip.

(*! big_sepM *)
Section bi.
Context {PROP : bi}.
Implicit Types P Q : PROP.
Implicit Types Ps Qs : list PROP.
Implicit Types A : Type.

Section map.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → PROP.

  Lemma big_sepM_mono_with_inv' P Φ Ψ m :
    (∀ k x, m !! k = Some x → P ∗ Φ k x ⊢ P ∗ Ψ k x) →
    P ∗ ([∗ map] k ↦ x ∈ m, Φ k x) ⊢ P ∗ [∗ map] k ↦ x ∈ m, Ψ k x.
  Proof.
    intros Hwand.
    induction m as [|i x m ? IH] using map_ind; auto using big_sepM_empty'.
    by rewrite big_opM_eq.
    rewrite ?big_sepM_insert //.
    iIntros "(HP&Hi&H)".
    iDestruct (Hwand with "[$]") as "(?&$)".
    { by rewrite lookup_insert. }
    iApply IH; eauto.
    { iIntros (k x' Hlookup). iApply Hwand.
      destruct (decide (i = k)).
      - subst. congruence.
      - rewrite lookup_insert_ne //.
    }
    iFrame.
  Qed.

  Lemma big_sepM_lookup_acc_mono Φ Ψ m k x :
    m !! k = Some x →
    (∀ k' x', m !! k' = Some x' → k' ≠ k → Φ k' x' ⊢ Ψ k' x') →
    ([∗ map] k' ↦ x' ∈ m, Φ k' x') ⊢ Φ k x ∗ (Ψ k x -∗ ([∗ map] k' ↦ x' ∈ m, Ψ k' x')).
  Proof.
    iIntros (Hk Hmono) "Hm".
    iPoseProof (big_sepM_delete _ _ _ _ Hk with "Hm") as "(HΦk&Hm)".
    iPoseProof (big_sepM_mono Φ Ψ with "Hm") as "Hm".
    {
      intros k' x' Hk'.
      apply lookup_delete_Some in Hk'.
      specialize (Hmono k' x').
      intuition.
    }
    iFrame.
    iIntros "HΨk".
    iPoseProof (big_sepM_insert with "[Hm HΨk]") as "Hm".
    2: {
      iFrame.
      iFrame.
    }
    {
      apply lookup_delete_None.
      eauto.
    }
    rewrite insert_delete insert_id //.
  Qed.

  Lemma big_sepM_filter Φ (R: K * A → Prop) {Hdec: ∀ k, Decision (R k)} m :
    ([∗ map] k ↦ x ∈ filter R m, Φ k x) ⊣⊢
    ([∗ map] k ↦ x ∈ m, if decide (R (k, x)) then Φ k x else emp).
  Proof.
    induction m as [|k v m ? IH] using map_ind.
    { by rewrite map_filter_empty !big_sepM_empty. }
    destruct (decide (R (k, v))).
    - rewrite map_filter_insert //.
      rewrite !big_sepM_insert //.
      * by rewrite decide_True // IH.
      * apply map_filter_lookup_None; eauto.
    - rewrite map_filter_insert_not' //; last by congruence.
      rewrite !big_sepM_insert // decide_False // IH. rewrite left_id. eauto.
  Qed.

  Lemma big_sepM_mono_with_inv P Φ Ψ m :
    (∀ k x, m !! k = Some x → P ∗ Φ k x ⊢ P ∗ Ψ k x) →
    P -∗ ([∗ map] k ↦ x ∈ m, Φ k x) -∗ P ∗ [∗ map] k ↦ x ∈ m, Ψ k x.
  Proof.
    iIntros (?) "HP H". iApply (big_sepM_mono_with_inv' with "[HP H]"); eauto.
    iFrame.
  Qed.

  Lemma big_sepM_mono_with_pers (P: PROP) `{!BiAffine PROP} `{Persistent PROP P} Φ Ψ m :
    (∀ k x, m !! k = Some x → P -∗ Φ k x -∗ Ψ k x) →
    P -∗ ([∗ map] k ↦ x ∈ m, Φ k x) -∗ [∗ map] k ↦ x ∈ m, Ψ k x.
  Proof.
    iIntros (Himpl) "#HP H". iDestruct (big_sepM_mono_with_inv with "HP H") as "(_&$)"; eauto.
    iIntros (???) "(#HP&Φ)". iFrame "HP". by iApply Himpl.
  Qed.

  Lemma big_sepM_insert_delete Φ m i x :
    ([∗ map] k↦y ∈ <[i:=x]> m, Φ k y) ⊣⊢ Φ i x ∗ [∗ map] k↦y ∈ delete i m, Φ k y.
  Proof. rewrite -insert_delete big_sepM_insert ?lookup_delete //. Qed.

  Lemma big_sepM_mono_wand `{!BiAffine PROP} Φ Ψ m (I : PROP) :
    □ ( ∀ k x, ⌜ m !! k = Some x ⌝ -∗
      I ∗ Φ k x -∗ I ∗ Ψ k x ) -∗
    I ∗ ([∗ map] k↦x ∈ m, Φ k x) -∗
    I ∗ ([∗ map] k↦x ∈ m, Ψ k x).
  Proof.
    iIntros "#Hwand [HI Hm]".
    iInduction m as [|i x m] "IH" using map_ind.
    - iFrame. iApply big_sepM_empty. done.
    - iDestruct (big_sepM_insert with "Hm") as "[Hi Hm]"; eauto.
      iDestruct ("Hwand" with "[] [$HI $Hi]") as "[HI Hi]".
      { rewrite lookup_insert. eauto. }
      iDestruct ("IH" with "[Hwand] HI Hm") as "[HI Hm]".
      { iModIntro. iIntros (k x0 Hkx0) "[HI Hk]".
        destruct (decide (k = i)); subst; try congruence.
        iApply ("Hwand" with "[]").
        { rewrite lookup_insert_ne; eauto. }
        iFrame.
      }
      iFrame. iApply big_sepM_insert; eauto. iFrame.
  Qed.

  Lemma big_sepM_mono_fupd `{!BiAffine PROP} `{!BiFUpd PROP} Φ Ψ m (I : PROP) E :
   □ ( ∀ k x, ⌜ m !! k = Some x ⌝ →
      I ∗ Φ k x ={E}=∗ I ∗ Ψ k x ) -∗
    I ∗ ([∗ map] k↦x ∈ m, Φ k x) ={E}=∗
    I ∗ ([∗ map] k↦x ∈ m, Ψ k x).
  Proof.
    iIntros "#Hfupd [HI Hm]".
    iInduction m as [|i x m] "IH" using map_ind.
    - iModIntro. iFrame. iApply big_sepM_empty. done.
    - iDestruct (big_sepM_insert with "Hm") as "[Hi Hm]"; eauto.
      iMod ("Hfupd" with "[] [$HI $Hi]") as "[HI Hi]".
      { rewrite lookup_insert. eauto. }
      iMod ("IH" with "[Hfupd] HI Hm") as "[HI Hm]".
      { iModIntro. iIntros (k x0 Hkx0) "[HI Hk]".
        destruct (decide (k = i)); subst; try congruence.
        iApply "Hfupd".
        { rewrite lookup_insert_ne; eauto. }
        iFrame.
      }
      iFrame. iApply big_sepM_insert; eauto. iFrame. done.
  Qed.

  (** * IntoPure/FromPure instances for big_sepM *)
  Global Instance big_sepM_IntoPure
           (Φ: K → A → PROP) (P: K → A → Prop)
           {ΦP: ∀ k v, IntoPure (Φ k v) (P k v)}
           (m: gmap K A) :
    IntoPure ([∗ map] k↦x ∈ m, Φ k x) (map_Forall P m).
  Proof.
    induction m using map_ind; simpl.
    - hnf; iIntros "_ !%".
      apply map_Forall_empty.
    - hnf; iIntros "HP".
      rewrite -> big_sepM_insert by auto.
      iDestruct (into_pure with "HP") as %?.
      iPureIntro.
      rewrite -> map_Forall_insert by auto.
      auto.
  Qed.

  Lemma big_sepM_from_Forall
        (Φ: K → A → PROP) (P: K → A → Prop)
        (m: gmap K A) :
    (∀ k v, P k v → ⊢ Φ k v) →
    map_Forall P m →
    ⊢ [∗ map] k↦x ∈ m, Φ k x.
  Proof.
    intros HfromP.
    induction m using map_ind; simpl; intros.
    - iApply big_sepM_empty; auto.
    - rewrite -> big_sepM_insert by auto.
      rewrite -> map_Forall_insert in H1 by auto.
      intuition.
      iSplitL.
      + iApply HfromP; auto.
      + auto.
  Qed.

  Global Instance big_sepM_FromPure_affine
            (Φ: K → A → PROP) (P: K → A → Prop)
            {ΦP: ∀ k v, FromPure true (Φ k v) (P k v)}
            (m: gmap K A) :
    FromPure true ([∗ map] k↦x ∈ m, Φ k x) (map_Forall P m).
  Proof.
    hnf; simpl.
    iIntros "%".
    iApply big_sepM_from_Forall; eauto.
  Qed.

  Global Instance big_sepM_FromPure
            `{BiAffine PROP}
            (Φ: K → A → PROP) (P: K → A → Prop)
            {ΦP: ∀ k v, FromPure false (Φ k v) (P k v)}
            (m: gmap K A) :
    FromPure false ([∗ map] k↦x ∈ m, Φ k x) (map_Forall P m).
  Proof.
    hnf; simpl.
    iIntros "%".
    iApply big_sepM_from_Forall; eauto.
  Qed.

  Lemma big_sepM_lookup_holds
        `{BiAffine PROP} (m: gmap K A) :
    ⊢@{PROP} [∗ map] k↦v ∈ m, ⌜m !! k = Some v⌝.
  Proof.
    iPureIntro.
    apply map_Forall_lookup; auto.
  Qed.
End map.

Section map2.
  Context `{Countable K} {A B : Type}.
  Implicit Types Φ Ψ : K → A → B → PROP.

  Lemma big_sepM2_lookup_1_some
      Φ (m1 : gmap K A) (m2 : gmap K B) (i : K) (x1 : A)
      (_ : forall x2 : B, Absorbing (Φ i x1 x2)) :
    m1 !! i = Some x1 ->
      ⊢ ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) -∗
          ⌜∃ x2, m2 !! i = Some x2⌝.
  Proof.
    intros.
    iIntros "H".
    iDestruct (big_sepM2_lookup_1 with "H") as (x2) "[% _]"; eauto.
  Qed.

  Lemma big_sepM2_lookup_2_some
      Φ (m1 : gmap K A) (m2 : gmap K B) (i : K) (x2 : B)
      (_ : forall x1 : A, Absorbing (Φ i x1 x2)) :
    m2 !! i = Some x2 ->
      ⊢ ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) -∗
          ⌜∃ x1, m1 !! i = Some x1⌝.
  Proof.
    intros.
    iIntros "H".
    iDestruct (big_sepM2_lookup_2 with "H") as (x1) "[% _]"; eauto.
  Qed.

  Lemma big_sepM2_lookup_1_none
      Φ (m1 : gmap K A) (m2 : gmap K B) (i : K)
      (_ : forall (x1 : A) (x2 : B), Absorbing (Φ i x1 x2)) :
    m1 !! i = None ->
      ⊢ ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) -∗
          ⌜m2 !! i = None⌝.
  Proof.
    case_eq (m2 !! i); auto.
    iIntros (? ? ?) "H".
    iDestruct (big_sepM2_lookup_2 with "H") as (x2) "[% _]"; eauto; congruence.
  Qed.

  Lemma big_sepM2_lookup_2_none
      Φ (m1 : gmap K A) (m2 : gmap K B) (i : K)
      (_ : forall (x1 : A) (x2 : B), Absorbing (Φ i x1 x2)) :
    m2 !! i = None ->
      ⊢ ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) -∗
          ⌜m1 !! i = None⌝.
  Proof.
    case_eq (m1 !! i); auto.
    iIntros (? ? ?) "H".
    iDestruct (big_sepM2_lookup_1 with "H") as (x1) "[% _]"; eauto; congruence.
  Qed.

  Lemma big_sepM2_sepM_1
      Φ (m1 : gmap K A) (m2 : gmap K B)
      (_ : forall i x1 x2, Absorbing (Φ i x1 x2)) :
    ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) -∗
      ( [∗ map] k↦y1 ∈ m1, ∃ y2, ⌜ m2 !! k = Some y2 ⌝ ∗ Φ k y1 y2 ).
  Proof.
    iIntros "H".
    rewrite <- (list_to_map_to_list m1).
    pose proof (NoDup_fst_map_to_list m1); revert H1.
    generalize (map_to_list m1); intros l H1.
    iInduction l as [|] "Hi" forall (m2).
    - iDestruct (big_sepM2_empty_r with "H") as %->.
      simpl.
      iDestruct (big_sepM2_empty with "H") as "H".
      iApply big_sepM_empty; iFrame.
    - simpl.
      iDestruct (big_sepM2_lookup_1_some with "H") as %H2.
      { apply lookup_insert. }
      destruct H2.
      rewrite <- insert_delete at 1.
      replace m2 with (<[a.1 := x]> m2).
      2: {
        rewrite insert_id //.
      }
      iDestruct (big_sepM2_insert_delete with "H") as "[Ha H]".
      inversion H1; clear H1; subst.
      iApply big_sepM_insert.
      { apply not_elem_of_list_to_map_1; eauto. }
      iSplitL "Ha".
      { iExists _. iFrame. rewrite insert_id; done. }
      rewrite delete_idemp.
      iSpecialize ("Hi" $! H6).
      rewrite delete_notin.
      2: { apply not_elem_of_list_to_map_1; eauto. }
      iDestruct ("Hi" with "H") as "H".
      iApply (big_sepM_mono with "H").
      iIntros (k x0 Hk) "H".
      iDestruct "H" as (y2) "[% H]".
      iExists _; iFrame.
      iPureIntro.
      assert (a.1 ≠ k).
      { intro He; subst.
        rewrite lookup_delete in H1; congruence. }
      rewrite -> lookup_insert_ne by eauto.
      rewrite -> lookup_delete_ne in H1 by eauto.
      eauto.
  Qed.

  Lemma big_sepM2_sepM_2
      Φ (m1 : gmap K A) (m2 : gmap K B)
      (_ : forall i x1 x2, Absorbing (Φ i x1 x2)) :
    ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) -∗
      ( [∗ map] k↦y2 ∈ m2, ∃ y1, ⌜ m1 !! k = Some y1 ⌝ ∗ Φ k y1 y2 ).
  Proof.
    iIntros "H".
    rewrite <- (list_to_map_to_list m2).
    pose proof (NoDup_fst_map_to_list m2); revert H1.
    generalize (map_to_list m2); intros l H1.
    iInduction l as [|] "Hi" forall (m1).
    - iDestruct (big_sepM2_empty_l with "H") as %->.
      simpl.
      iDestruct (big_sepM2_empty with "H") as "H".
      iApply big_sepM_empty; iFrame.
    - simpl.
      iDestruct (big_sepM2_lookup_2_some with "H") as %H2.
      { apply lookup_insert. }
      destruct H2.
      rewrite <- insert_delete at 1.
      replace m1 with (<[a.1 := x]> m1).
      2: {
        rewrite insert_id //.
      }
      iDestruct (big_sepM2_insert_delete with "H") as "[Ha H]".
      inversion H1; clear H1; subst.
      iApply big_sepM_insert.
      { apply not_elem_of_list_to_map_1; eauto. }
      iSplitL "Ha".
      { iExists _. iFrame. rewrite insert_id; done. }
      rewrite delete_idemp.
      iSpecialize ("Hi" $! H6).
      rewrite (delete_notin (list_to_map l)).
      2: { apply not_elem_of_list_to_map_1; eauto. }
      iDestruct ("Hi" with "H") as "H".
      iApply (big_sepM_mono with "H").
      iIntros (k x0 Hk) "H".
      iDestruct "H" as (y1) "[% H]".
      iExists _; iFrame.
      iPureIntro.
      assert (a.1 ≠ k).
      { intro He; subst.
        rewrite lookup_delete in H1; congruence. }
      rewrite -> lookup_insert_ne by eauto.
      rewrite -> lookup_delete_ne in H1 by eauto.
      eauto.
  Qed.

  Lemma big_sepM_sepM2 Φ (m1 : gmap K A)
      (_ : forall i x1 x2, Absorbing (Φ i x1 x2)) :
    ( [∗ map] k↦y1 ∈ m1, ∃ y2, Φ k y1 y2 ) -∗
    ∃ m2, ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ).
  Proof.
    iIntros "Hm".
    iInduction m1 as [|i x m] "IH" using map_ind.
    - iExists ∅. iApply big_sepM2_empty. done.
    - iDestruct (big_sepM_insert with "Hm") as "[Hi Hm]"; eauto.
      iDestruct "Hi" as (y2) "Hi".
      iDestruct ("IH" with "Hm") as (m2) "Hm".
      iExists (<[i := y2]> m2).
      iDestruct (big_sepM2_lookup_1_none with "Hm") as "%Hm2i"; eauto.
      iApply big_sepM2_insert; eauto.
      iFrame.
  Qed.

  Lemma big_sepM_sepM2_merge (Φ : K -> A -> PROP) (Ψ : K -> B -> PROP)
    (m1 : gmap K A) (m2 : gmap K B) :
    dom (gset K) m1 = dom (gset K) m2 ->
    ( [∗ map] k↦y1 ∈ m1, Φ k y1 ) ∗
    ( [∗ map] k↦y2 ∈ m2, Ψ k y2 ) -∗
    [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 ∗ Ψ k y2.
  Proof.
    iIntros (Hdom) "[Hm1 Hm2]".
    iInduction m1 as [|i x m] "IH" using map_ind forall (m2 Hdom).
    - rewrite dom_empty_L in Hdom. symmetry in Hdom. apply dom_empty_inv_L in Hdom.
      subst. iApply big_sepM2_empty. done.
    - destruct (m2 !! i) eqn:He.
      2: {
        apply (not_elem_of_dom (D:=gset K)) in He.
        rewrite -Hdom in He.
        exfalso. apply He.
        apply elem_of_dom. rewrite lookup_insert. eauto.
      }
      iDestruct (big_sepM_insert with "Hm1") as "[Hi1 Hm1]"; eauto.
      replace (m2) with (<[i:=b]> (delete i m2)).
      2: {
        rewrite insert_delete. rewrite insert_id; eauto.
      }
      iDestruct (big_sepM_insert with "Hm2") as "[Hi2 Hm2]"; eauto.
      { rewrite lookup_delete; eauto. }
      iApply big_sepM2_insert; eauto.
      { rewrite lookup_delete; eauto. }
      iFrame.
      iSpecialize ("IH" $! (delete i m2) _ with "Hm1 Hm2"). iApply "IH".
  Unshelve.
    rewrite dom_delete_L -Hdom dom_insert_L.
    assert (i ∉ dom (gset K) m).
    { apply not_elem_of_dom. eauto. }
    set_solver.
  Qed.

  Lemma big_sepM2_sepM_merge Φ (Ψ : K -> A -> PROP) (m1 : gmap K A) (m2 : gmap K B)
      (_ : forall i x1 x2, Absorbing (Φ i x1 x2)) :
    ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) ∗
    ( [∗ map] k↦y1 ∈ m1, Ψ k y1 ) -∗
    ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ∗ Ψ k y1 ).
  Proof.
    iIntros "[Hm2 Hm]".
    iInduction m1 as [|i x m] "IH" using map_ind forall (m2).
    - iDestruct (big_sepM2_empty_r with "Hm2") as "%He". subst. iApply big_sepM2_empty. done.
    - iDestruct (big_sepM_insert with "Hm") as "[Hi Hm]"; eauto.
      iDestruct (big_sepM2_lookup_1_some _ _ _ i with "Hm2") as (x2) "%Hm2i"; eauto.
      { rewrite lookup_insert; eauto. }
      replace (m2) with (<[i:=x2]> (delete i m2)).
      2: { rewrite insert_delete insert_id //. }
      iDestruct (big_sepM2_insert with "Hm2") as "[Hii Hm2]"; eauto.
      { rewrite lookup_delete; eauto. }
      iDestruct ("IH" with "Hm2 Hm") as "Hm2".
      iApply big_sepM2_insert; eauto.
      { rewrite lookup_delete; eauto. }
      iFrame.
  Qed.

  Lemma big_sepM2_filter Φ (P : K -> Prop) (m1 : gmap K A) (m2 : gmap K B)
                         `{! ∀ k, Decision (P k)} :
    ⊢
    ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) ∗-∗
    ( ( [∗ map] k↦y1;y2 ∈ filter (λ x, P x.1) m1;filter (λ x, P x.1) m2, Φ k y1 y2 ) ∗
      ( [∗ map] k↦y1;y2 ∈ filter (λ x, ~P x.1) m1;filter (λ x, ~P x.1) m2, Φ k y1 y2 ) ).
  Proof.
    rewrite big_sepM2_eq /big_sepM2_def.
    iSplit.
    - iIntros "[% Hm]".
      erewrite <- (map_union_filter _ (map_zip m1 m2)).
      iDestruct (big_sepM_union with "Hm") as "[Hmp Hmnp]".
      { eapply map_disjoint_filter. }
      iSplitL "Hmp".
      + iSplit.
        { iPureIntro; eapply filter_same_keys_0; eauto. }
        rewrite map_zip_filter. iFrame.
      + iSplit.
        { iPureIntro.
          eapply (filter_same_keys_0 _ _ (λ k, ¬ P k)). eauto. }
        rewrite (map_zip_filter _ _ (λ k, ¬ P k)). iFrame.
    - iIntros "[[% Hm1] [% Hm2]]".
      iSplit.
      { iPureIntro. eapply filter_same_keys_1; eauto. }
      rewrite map_zip_filter.
      rewrite (map_zip_filter _ _ (λ k, ¬ P k)).
      iDestruct (big_sepM_union with "[$Hm1 $Hm2]") as "Hm".
      { eapply map_disjoint_filter. }
      rewrite map_union_filter. iFrame.
  Unshelve.
    all: typeclasses eauto.
  Qed.

End map2.
End bi.
