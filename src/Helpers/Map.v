From stdpp Require Import gmap.
From Coq Require Import ssreflect.

Section map.

  Context (K V:Type).
  Context `{Countable K}.
  Notation gmap := (gmap K V).
  Implicit Types (m:gmap).

  Theorem delete_insert_union m1 m2 k v :
    m1 !! k = Some v ->
    delete k m1 ∪ <[k := v]> m2 = m1 ∪ m2.
  Proof.
    intros.
    rewrite -insert_delete.
    rewrite -insert_union_r; first by apply lookup_delete.
    erewrite <- (insert_id (m1 ∪ m2)) by ( apply lookup_union_Some_l; eauto ).
    rewrite <- (insert_delete (m1 ∪ m2)).
    rewrite delete_union.
    eauto.
  Qed.

End map.

(** turn a list into a gmap from its indices to values *)
Definition list_to_imap {A} (l: list A) : gmap nat A :=
  list_to_map (imap (λ i x, (i, x)) l).

Theorem imap_NoDup {A B} (f: nat → A → B) (l: list A) :
  (∀ i1 x1 i2 x2,
      i1 ≠ i2 →
      l !! i1 = Some x1 →
      l !! i2 = Some x2 →
      f i1 x1 ≠ f i2 x2) →
  NoDup (imap f l).
Proof.
  revert f.
  induction l as [|x l]; simpl; intros f Hfneq.
  - constructor.
  - constructor.
    + intros Helem%elem_of_lookup_imap_1.
      destruct Helem as (i'&x'&[Heq Hlookup]).
      apply Hfneq in Heq; eauto.
    + apply IHl; intros.
      eapply Hfneq; eauto.
Qed.

Theorem lookup_list_to_imap_Some {A} l (i: nat) (x: A) :
  l !! i = Some x <-> list_to_imap l !! i = Some x.
Proof.
  rewrite /list_to_imap.
  revert i.
  induction l; simpl; intros.
  - auto.
  - destruct i; simpl.
    + rewrite lookup_insert //.
    + rewrite -> lookup_insert_ne by lia.
      rewrite IHl.
      split.
      * intros Helem%elem_of_list_to_map_2%elem_of_lookup_imap_1.
        destruct Helem as (i'&x'&[Heq Hlookup]).
        inversion Heq; subst; clear Heq.
        apply elem_of_list_to_map_1.
        { rewrite fmap_imap.
          simpl.
          apply imap_NoDup; intros; simpl.
          auto. }
        change (S i', x') with (((λ (i : nat) (x : A), (i, x)) ∘ S) i' x').
        eapply elem_of_lookup_imap_2; eauto.
      * intros Helem%elem_of_list_to_map_2%elem_of_lookup_imap_1.
        destruct Helem as (i'&x'&[Heq Hlookup]).
        inversion Heq; subst; clear Heq.
        apply elem_of_list_to_map_1.
        { rewrite fmap_imap.
          simpl.
          apply imap_NoDup; intros; simpl.
          auto. }
        eapply elem_of_lookup_imap_2; eauto.
Qed.

(** a theorem that essentially fully characterizes [list_to_imap l] in terms of
    lookups (one the one hand gmap lookups, on the other list lookup) *)
Theorem lookup_list_to_imap {A} (l: list A) (i: nat) :
  list_to_imap l !! i = l !! i.
Proof.
  destruct (l !! i) eqn:Hl.
  - apply lookup_list_to_imap_Some in Hl; auto.
  - destruct (list_to_imap l !! i) eqn:Himapl; auto.
    apply lookup_list_to_imap_Some in Himapl; congruence.
Qed.

Theorem list_to_imap_app1 {A} (l: list A) (y: A) :
  list_to_imap (l ++ [y]) = <[length l := y]> (list_to_imap l).
Proof.
  apply map_eq_iff; intros.
  rewrite lookup_list_to_imap.
  destruct (decide (i < length l)%nat);
    [ | destruct (decide (i = length l)); subst ].
  - rewrite -> lookup_app_l by lia.
    rewrite -> lookup_insert_ne by lia.
    rewrite lookup_list_to_imap //.
  - rewrite -> lookup_app_r by lia.
    replace (length l - length l)%nat with 0%nat by lia.
    rewrite /= lookup_insert //.
  - rewrite -> lookup_insert_ne by lia.
    rewrite lookup_list_to_imap.
    rewrite -> lookup_app_r by lia.
    replace (i - length l)%nat with (S (i - length l - 1))%nat by lia; simpl.
    rewrite lookup_nil.
    rewrite -> lookup_ge_None_2 by lia.
    auto.
Qed.

Lemma map_difference_delete `{Countable K} {V} (a b : gmap K V) (k : K) (v : V) :
  a !! k = Some v ->
  a ∖ delete k b = <[k := v]> (a ∖ b).
Proof.
  intros.
  eapply map_eq.
  intros.
  destruct (decide (k = i)); subst.
  { rewrite lookup_insert.
    eapply lookup_difference_Some; intuition eauto.
    rewrite lookup_delete; eauto. }
  rewrite lookup_insert_ne; eauto.
  destruct ((a ∖ b) !! i) eqn:He.
  { apply lookup_difference_Some in He.
    apply lookup_difference_Some.
    intuition eauto. rewrite lookup_delete_ne; eauto. }
  apply lookup_difference_None in He.
  apply lookup_difference_None.
  intuition eauto. rewrite lookup_delete_ne; eauto.
Qed.

Lemma map_difference_empty `{Countable K} {V} (m : gmap K V) :
  m ∖ ∅ = m.
Proof.
  apply map_eq; intros.
  destruct (m !! i) eqn:He.
  - eapply lookup_difference_Some; intuition eauto.
  - eapply lookup_difference_None; intuition eauto.
Qed.
