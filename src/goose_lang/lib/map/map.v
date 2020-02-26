From iris.proofmode Require Import coq_tactics reduction.
From Perennial.goose_lang Require Import notation proofmode.
From Perennial.goose_lang.lib Require Import typed_mem.
From Perennial.goose_lang.lib Require Export map.impl.
Import uPred.

Set Default Proof Using "Type".

Section heap.
Context `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ}.
Context {ext_ty: ext_types ext}.
Implicit Types v : val.
Implicit Types vs : list val.
Implicit Types z : Z.
Implicit Types t : ty.
Implicit Types stk : stuckness.
Implicit Types off : nat.

(* The model of a map is [gmap u64 val * val] (the second value is the default).

The abstraction relation (actually abstraction function) between a val mv and a
model m is m = map_val mv.

The models are canonical due to extensionality of gmaps, but the concrete
representation tracks all insertions (including duplicates). *)

Fixpoint map_val (v: val) : option (gmap u64 val * val) :=
  match v with
  | MapConsV k v m =>
    match map_val m with
    | Some (m, def) => Some (<[ k := v ]> m, def)
    | None => None
    end
  | MapNilV def => Some (∅, def)
  | _ => None
  end.

Definition val_of_map (m_def: gmap u64 val * val) : val :=
  let (m, def) := m_def in
  fold_right (λ '(k, v) mv, MapConsV k v mv)
             (MapNilV def)
             (map_to_list m).

Theorem map_val_id : forall v m_def,
    map_val v = Some m_def ->
    val_of_map m_def = v.
Proof.
  induction v; intros [m def]; try solve [ inversion 1 ]; simpl; intros H.
  - inversion H; subst; clear H.
    rewrite map_to_list_empty; simpl; auto.
  - destruct v; try congruence.
    destruct v1; try congruence.
    destruct v1_1; try congruence.
    destruct l; try congruence.
    destruct_with_eqn (map_val v2); try congruence.
    specialize (IHv p).
    destruct p as [m' def'].
    inversion H; subst; clear H.
    (* oops, the normal val induction principle is too weak to prove this *)
Abort.

Definition map_get (m_def: gmap u64 val * val) (k: u64) : (val*bool) :=
  let (m, def) := m_def in
  let r := default def (m !! k) in
  let ok := bool_decide (is_Some (m !! k)) in
  (r, ok).

Definition map_insert (m_def: gmap u64 val * val) (k: u64) (v: val) : gmap u64 val * val :=
  let (m, def) := m_def in
  (<[ k := v ]> m, def).

Definition map_del (m_def: gmap u64 val * val) (k: u64) : gmap u64 val * val :=
  let (m, def) := m_def in
  (delete k m, def).


Lemma map_get_empty def k : map_get (∅, def) k = (def, false).
Proof.
  reflexivity.
Qed.

Lemma map_get_insert k v m def :
  map_get (<[k:=v]> m, def) k = (v, true).
Proof.
  rewrite /map_get.
  rewrite lookup_insert //.
Qed.

Lemma map_get_insert_ne k k' v m def :
  k ≠ k' ->
  map_get (<[k:=v]> m, def) k' = map_get (m, def) k'.
Proof.
  intros Hne.
  rewrite /map_get.
  rewrite lookup_insert_ne //.
Qed.

Lemma map_get_true k v m def :
  map_get (m, def) k = (v, true) ->
  m !! k = Some v.
Proof.
  rewrite /map_get.
  destruct (m !! k); rewrite /=; congruence.
Qed.

Lemma map_get_false k v m def :
  map_get (m, def) k = (v, false) ->
  m !! k = None.
Proof.
  rewrite /map_get.
  destruct (m !! k); rewrite /=; congruence.
Qed.

Lemma map_val_split mv m :
  map_val mv = Some m ->
  {∃ def, mv = MapNilV def ∧ m = (∅, def)} +
  {∃ k v mv' m', mv = MapConsV k v mv' ∧ map_val mv' = Some m' ∧ m = (<[k:=v]> (fst m'), snd m')}.
Proof.
  intros H.
  destruct mv; inversion H; subst; [ left | right ].
  - exists mv; auto.
  - destruct mv; try solve [ inversion H1 ].
    destruct mv1; try solve [ inversion H1 ].
    destruct mv1_1; try solve [ inversion H1 ].
    destruct l; try solve [ inversion H1 ].
    destruct_with_eqn (map_val mv2); try solve [ inversion H1 ].
    destruct p; inversion H1; subst; clear H1.
    eexists _, _, _, _; intuition eauto.
Qed.

Definition is_map (mref:loc) (m: gmap u64 val * val): iProp Σ :=
  ∃ mv, ⌜map_val mv = Some m⌝ ∗ mref ↦ mv.

Theorem map_zero_val t :
  flatten_struct (zero_val (mapValT t)) = [MapNilV (zero_val t)].
Proof. reflexivity. Qed.

Definition wp_NewMap stk E t :
  {{{ True }}}
    NewMap t @ stk; E
  {{{ mref, RET #mref;
      is_map mref (∅, zero_val t) }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_apply wp_alloc_untyped.
  { rewrite map_zero_val; auto. }
  iIntros (mref) "Hm".
  iApply "HΦ".
  iExists _; iSplitR; auto.
  done.
Qed.

Definition wp_MapGet stk E mref (m: gmap u64 val * val) k :
  {{{ is_map mref m }}}
    MapGet #mref #k @ stk; E
  {{{ v ok, RET (v, #ok); ⌜map_get m k = (v, ok)⌝ ∗
                          is_map mref m }}}.
Proof.
  iIntros (Φ) "Hmref HΦ".
  iDestruct "Hmref" as (mv H) "Hmref".
  wp_call.
  wp_untyped_load.
  wp_pure (_ _).
  iAssert (∀ v ok, ⌜map_get m k = (v, ok)⌝ -∗ Φ (v, #ok)%V)%I with "[Hmref HΦ]" as "HΦ".
  { iIntros (v ok) "%".
    iApply ("HΦ" with "[Hmref]").
    iSplitR; auto.
    iExists mv; by iFrame. }
  iLöb as "IH" forall (m mv H).
  wp_call.
  destruct (map_val_split _ _ H).
  - (* nil *)
    destruct e as [def ?]; intuition subst.
    wp_pures.
    iApply "HΦ".
    rewrite map_get_empty; auto.
  - destruct e as [k' [v [mv' [m' ?]]]]; intuition subst.
    wp_pures.
    wp_if_destruct.
    + wp_pures.
      iApply "HΦ".
      rewrite map_get_insert //.
    + iApply "IH".
      * eauto.
      * iIntros (v' ok) "%".
        iApply "HΦ".
        rewrite map_get_insert_ne //; try congruence.
        destruct m'; eauto.
Qed.

Definition wp_MapInsert stk E mref (m: gmap u64 val * val) k v' :
  {{{ is_map mref m }}}
    MapInsert #mref #k v' @ stk; E
  {{{ RET #(); is_map mref (map_insert m k v') }}}.
Proof.
  iIntros (Φ) "Hmref HΦ".
  iDestruct "Hmref" as (mv ?) "Hmref".
  wp_call.
  wp_untyped_load.
  wp_apply (wp_store with "Hmref"); iIntros "Hmref".
  iApply ("HΦ" with "[Hmref]").
  iExists _; iFrame.
  iPureIntro.
  simpl.
  rewrite H.
  destruct m; simpl; auto.
Qed.

Definition wp_MapDelete' stk E mv (m: gmap u64 val * val) k :
  {{{ ⌜map_val mv = Some m⌝ }}}
    MapDelete' mv #k @ stk; E
  {{{ mv', RET mv'; ⌜map_val mv' = Some (map_del m k)⌝ }}}.
Proof.
  destruct m.
  iIntros (Φ H) "HΦ".
  rewrite /MapDelete'.
  wp_lam. wp_let.
  wp_pure (Rec _ _ _).
  iLöb as "IH" forall (g v mv H Φ).
  apply map_val_split in H; intuition; repeat match goal with
    | H : ∃ _, _ |- _ => destruct H
    end; intuition; try congruence; subst.
  - wp_pures.
    iApply "HΦ".
    rewrite /=.
    inversion H1; subst.
    rewrite delete_empty. done.
  - destruct x2.
    wp_pures.
    rewrite bool_decide_decide.
    destruct (decide (#k = #x)); wp_if.
    + inversion e; clear e; subst.
      iApply "IH".
      { eauto. }
      iIntros (mv' Hmv').
      iApply "HΦ"; iPureIntro.
      rewrite Hmv' H2 /map_del /=.
      rewrite delete_insert_delete.
      auto.
    + iSpecialize ("IH" $! _ _ _ H).
      wp_bind (App _ _).
      iApply "IH".
      iIntros (mv' Hmv').
      wp_pures.
      iApply "HΦ"; iPureIntro.
      rewrite H2.
      rewrite /= Hmv' /map_del.
      f_equal.
      rewrite delete_insert_ne; congruence.
Qed.

Definition wp_MapDelete stk E mref (m: gmap u64 val * val) k :
  {{{ is_map mref m }}}
    MapDelete #mref #k @ stk; E
  {{{ RET #(); is_map mref (map_del m k) }}}.
Proof.
  iIntros (Φ) "Hmref HΦ".
  iDestruct "Hmref" as (mv ?) "Hmref".
  wp_call.
  wp_untyped_load.
  wp_apply wp_MapDelete'; eauto.
  iIntros (mv' Hmv').
  wp_apply (wp_store with "Hmref").
  iIntros "Hmref".
  iApply "HΦ". iExists _. iFrame. eauto.
Qed.

(* TODO: specify MapIter *)

End heap.
