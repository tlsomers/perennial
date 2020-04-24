From iris.proofmode Require Import tactics environments intro_patterns.
From iris.proofmode Require ltac_tactics.
From iris.base_logic.lib Require Import iprop.

From iris_string_ident Require ltac2_string_ident.

(* NamedProps implements [named name P], which is equivalent to P but knows to
   name itself [name] when iIntro'd. The syntax looks like [name ∷ P], in
   analogy to in Gallina where you might write [forall (Hfoo: 3 < 4), ...] for a
   hypothesis that would be introduced as `Hfoo` using automatic names.

  To use this library, write your definitions with [name ∷ P] for each conjunct.
  Then, use [iNamed "H"] to destruct an invariant "H" into its conjuncts, using
  their specified names. [iNamed] also introduces existentials with the names
  for the Coq binders.

  The names in a [named] are not actually names but full-blown Iris intro
  patterns. This means you can write [#H] to automatically introduce to the
  persistent context, [%H] to name a pure fact (using string_to_ident), or even
  something crazy like ["[<- H]"] to destruct the hypothesis and rewrite by the
  first conjunct. *)

Section named.
  Context {PROP:bi}.

  Definition named (name: string) (P: PROP): PROP := P.

  Theorem to_named name P : P -∗ named name P.
  Proof. auto. Qed.
  Theorem from_named name P : named name P -∗ P.
  Proof. auto. Qed.
End named.

Ltac to_pm_ident H :=
  lazymatch type of H with
  | string => constr:(INamed H)
  | ident => constr:(H)
  end.

Ltac string_to_ident s :=
  let ident_fun := constr:(ltac:(ltac_tactics.string_to_ident_hook s)) in
  lazymatch ident_fun with
  | λ (x:_), _ => x
  end.

Ltac iNameHyp H :=
  let i := to_pm_ident H in
  lazymatch goal with
  | |- context[Esnoc _ i (named ?name ?P)] =>
    let Htmp := iFresh in
    iRename i into Htmp;
    let pat := intro_pat.parse_one name in
    lazymatch pat with
    | IPure (IGallinaNamed ?name) =>
      let id := string_to_ident name in
      let id := fresh id in
      iPure Htmp as id
    | _ => iDestruct (from_named with Htmp) as pat
    end;
    (* TODO: we do this renaming so we can clear the original hypothesis, but
    this only happens when it isn't consumed (when P is persistent); ideally we
    would do this whole manipulation with something lower-level that always
    replaced the hypothesis, but also supported an intro pattern for the result.
    Otherwise this may have significant performance cost with large
    environments. *)
    try iClear Htmp
  | |- context[Esnoc _ i _] =>
    fail "iNameHyp: hypothesis" H "is not a named"
  | _ => fail 1 "iNameHyp: hypothesis" H "not found"
  end.

Ltac named :=
  repeat match goal with
         | |- context[Esnoc _ ?i (named ?name ?P)] =>
           iDestruct (from_named with i) as name
         end.

(* this is a super-simple but maybe non-performant implementation *)
Ltac iNamedDestruct H :=
  let rec go H :=
      first [iNameHyp H
            | let Htmp1 := iFresh in
              let Htmp2 := iFresh in
              let pat := constr:(IList [[IIdent Htmp1; IIdent Htmp2]]) in
              iDestruct H as pat;
              iNameHyp Htmp1; go Htmp2
            | idtac ]
  in go H.

Local Ltac iDeex_go i x H :=
  let x' := fresh x in
  iDestructHyp i as (x') H.

Ltac iDeexHyp H :=
  let i := to_pm_ident H in
  let rec go _ := lazymatch goal with
                  (* check this separately because red on bi_exist produces an unseal *)
                  | |- context[Esnoc _ i (bi_exist (fun x => _))] =>
                    first [ iDeex_go i x H | fail "iDeexHyp: could not deex" H ]
                  | |- context[Esnoc _ i ?P] =>
                    let P := (eval red in P) in
                    lazymatch P with
                    | bi_exist (fun x => _) =>
                      first [ iDeex_go i x H | fail "iDeexHyp: could not deex" H ]
                    | _ => fail "iDeexHyp:" H "is not an ∃"
                    end
                  end in
  go tt; repeat go tt.

Ltac iDeex :=
  repeat match goal with
         | |- context[Esnoc _ ?i (bi_exist (fun x => _))] =>
           iDeex_go
         end.

Ltac iNamed H :=
  try iDeexHyp H;
  iNamedDestruct H.

Ltac prove_named :=
  repeat rewrite -to_named.

Notation "name ∷ P" := (named name P) (at level 79).

(* TODO: maybe we should move tests out *)
Module tests.
  Section tests.
    Context {Σ:gFunctors}.
    Implicit Types (P Q R : iProp Σ).
    Implicit Types (Ψ: nat -> iProp Σ).
    Implicit Types (φ: Prop).

    Example test_name_named_1 P Q :
      ⊢ named "H1" P -∗
        named "H2" Q -∗
        P ∗ Q.
    Proof.
      iIntros "? ?".
      named.
      iSplitL "H1"; [ iExact "H1" | iExact "H2" ].
    Qed.

    Example test_name_named_2 P Q :
      ⊢ named "H1" P -∗
        named "H2" Q -∗
        P ∗ Q%I.
    Proof.
      iIntros "H₁ H₂".
      iNameHyp "H₁".
      iNameHyp "H₂".
      iSplitL "H1"; [ iExact "H1" | iExact "H2" ].
    Qed.

    Example test_pure_pattern_freshen φ φ' P :
      named "%H" ⌜φ⌝ -∗
      named "%H" ⌜φ'⌝ -∗
      P -∗
      ⌜φ ∧ φ'⌝ ∗ P.
    Proof.
      iIntros "H1 H2 $".
      iNameHyp "H1".
      iNameHyp "H2".
      iPureIntro; exact (conj H H0).
    Qed.

    Example test_destruct_named P Q :
      ⊢ named "H1" P ∗
        named "H2" Q ∗
        named "H3" P ∗
        named "H4" Q
        -∗
        P ∗ Q ∗ P ∗ Q.
    Proof.
      iIntros "H".
      iNamedDestruct "H".
      iFrame.
    Qed.

    Example test_destruct_pat (foo: Prop) P Q :
      ⊢ named "[%Hfoo HP]" (⌜foo⌝ ∗ P) ∗
        named "HQ" Q ∗
        named "HP2" P
        -∗
        ⌜foo⌝ ∗ P ∗ Q ∗ P.
    Proof.
      iIntros "H".
      iNamedDestruct "H".
      iFrame "HP HQ HP2".
      iPureIntro; exact Hfoo.
    Qed.

    Example test_frame_named P Q :
      ⊢ P -∗ Q -∗ named "HP" P ∗ named "HQ" Q.
    Proof.
      iIntros "HP HQ".
      iFrame "HQ HP".
    Qed.

    Example test_frame_named_sep P Q :
      ⊢ P -∗ Q -∗ named "HPQ" (P ∗ Q).
    Proof.
      iIntros "HP HQ".
      iFrame.
    Qed.

    Example test_remove_named_in_goal P Q :
      ⊢ P -∗ Q -∗ named "HP" P ∗ named "HQ" Q.
    Proof.
      iIntros "HP HQ".
      prove_named.
      iFrame.
    Qed.

    Example test_exist_destruct Ψ Q :
      ⊢ (∃ x, named "HP" (Ψ x) ∗ named "HQ" Q) -∗ (∃ x, Ψ x) ∗ Q.
    Proof.
      iIntros "H".
      iNamed "H".
      iSplitL "HP"; [ iExists x | ]; iFrame.
    Qed.

    Definition rep_invariant Ψ Q : iProp Σ :=
      (∃ x, named "HP" (Ψ x) ∗ named "HQ" Q).

    Example test_exist_destruct_under_definition (P: nat -> iProp Σ) Q :
      ⊢ rep_invariant P Q -∗ (∃ x, P x) ∗ Q.
    Proof.
      iIntros "H".
      iNamed "H".
      iSplitL "HP"; [ iExists x | ]; iFrame.
    Qed.

    Example test_exist_destruct_no_naming Ψ Q :
      ⊢ (∃ x, Ψ x) -∗ (∃ x, Ψ x).
    Proof.
      iIntros "H".
      iNamed "H".
      iExists x; iFrame "H".
    Qed.

    Example test_multiple_exist_destruct Ψ Q :
      ⊢ (∃ x y z, Ψ (x + y + z)) -∗ (∃ x, Ψ x).
    Proof.
      iIntros "H".
      iNamed "H".
      iExists (x+y+z); iFrame "H".
    Qed.

    Example test_iNamed_destruct_pat (φ: Prop) P Q :
      ⊢ named "[%Hfoo HP]" (⌜φ⌝ ∗ P) ∗
        named "HQ" Q ∗
        named "HP2" P
        -∗
        ⌜φ⌝ ∗ P ∗ Q ∗ P.
    Proof.
      iIntros "H".
      iNamed "H".
      iFrame "HP HQ HP2".
      iPureIntro; exact Hfoo.
    Qed.

    Example test_named_into_pure φ Q :
      named "N" ⌜φ⌝ ∗ Q -∗ Q.
    Proof.
      iIntros "[%HP HQ]".
      iFrame.
    Qed.

    Example test_named_from_pure φ Q :
      φ ->
      Q -∗ Q ∗ named "N" ⌜φ⌝.
    Proof.
      iIntros (HP) "HQ".
      iFrame.
      iPureIntro.
      done.
    Qed.

    Example test_named_not_found P :
      named "HP" P -∗ P.
    Proof.
      iIntros "HP".
      Fail iNamed "foo". (* hypothesis "foo" not found *)
      iNamed "HP".
      iExact "HP".
    Qed.

    Example test_exists_freshen x Ψ :
      named "HP" (Ψ x) -∗ named "HP2" (∃ x, Ψ x) -∗
      named "HP" (∃ x, Ψ x).
    Proof.
      iIntros "? ?"; named.
      iDeexHyp "HP2".
      iExists x0; iFrame.
    Qed.

  End tests.
End tests.
