From iris.proofmode Require Import reduction monpred.
From Perennial.Helpers Require Import ipm NamedProps.

From Perennial.goose_lang Require Import lifting.

Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.

(* We use heapGS here since all our proofs are heapGS-parameterized;
providing a lone gooseLocalGS is not terribly useful. *)

Definition post_crash {Σ} `{hG: !heapGS Σ} (P: heapGS Σ → iProp Σ) : iProp Σ :=
  (∀ σ σ' hL', ffi_crash_rel Σ (goose_ffiLocalGS (hL := goose_localGS)) σ (goose_ffiLocalGS (hL := hL')) σ' ==∗
               ffi_crash_rel Σ (goose_ffiLocalGS (hL := goose_localGS)) σ (goose_ffiLocalGS (hL := hL')) σ' ∗
               (P (HeapGS _ _ hL'))).

Class IntoCrash {Σ} `{!heapGS Σ} (P: iProp Σ) (Q: heapGS Σ → iProp Σ) :=
  into_crash : P ⊢ post_crash (Σ := Σ) (λ hG', Q hG').

Section post_crash_prop.
Context `{hL: !heapGS Σ}.
Implicit Types Φ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.

Lemma post_crash_intro Q:
  (⊢ Q) →
  (⊢ post_crash (λ _, Q)).
Proof. iIntros (Hmono). iIntros (???) "Hrel". iModIntro. iFrame "Hrel". iApply Hmono. Qed.

Lemma post_crash_mono P Q:
  (∀ hL, P hL ⊢ Q hL) →
  post_crash P ⊢ post_crash Q.
Proof.
  iIntros (Hmono) "HP". iIntros (???) "Hrel".
  iMod ("HP" with "[$]") as "(H&HP)".
  iFrame. iApply Hmono. iApply "HP"; eauto.
Qed.

Lemma post_crash_sep P Q:
  post_crash P ∗ post_crash Q ⊢ post_crash (λ hL, P hL ∗ Q hL).
Proof.
  iIntros "(HP&HQ)". iIntros (???) "Hrel".
  iMod ("HP" with "[$]") as "(H&$)".
  iMod ("HQ" with "[$]") as "(H&$)".
  by iFrame.
Qed.

Lemma post_crash_or P Q:
  post_crash P ∨ post_crash Q ⊢ post_crash (λ hL, P hL ∨ Q hL).
Proof.
  iIntros "[HP|HQ]"; iIntros (???) "Hrel".
  - iMod ("HP" with "[$]") as "($&$)". by iModIntro.
  - iMod ("HQ" with "[$]") as "($&$)". by iModIntro.
Qed.

(*
Lemma post_crash_and P Q:
  post_crash P ∧ post_crash Q -∗ post_crash (λ hL, P hL ∧ Q hL).
Proof.
  iIntros "HPQ"; iIntros (???) "Hrel".
  iSplit.
  - iDestruct "HPQ" as "(HP&_)". by iApply "HP".
  - iDestruct "HPQ" as "(_&HQ)". by iApply "HQ".
Qed.
*)

Lemma post_crash_pure (P: Prop) :
  P → ⊢ post_crash (λ _, ⌜ P ⌝).
Proof.
  iIntros (????); eauto.
Qed.

Lemma post_crash_nodep (P: iProp Σ) :
  P -∗ post_crash (λ _, P).
Proof. iIntros "HP". iIntros (???); eauto. iIntros "$". by iFrame. Qed.

Lemma post_crash_exists {A} P Q:
  (∀ (x: A), P hL x -∗ post_crash (λ hL, Q hL x)) -∗
  (∃ x, P hL x) -∗ post_crash (λ hL, ∃ x, Q hL x).
Proof.
  iIntros "Hall HP". iIntros (???) "Hrel".
  iDestruct "HP" as (x) "HP".
  iDestruct ("Hall" with "[$]") as "H".
  iMod ("H" with "[$]") as "($&H)".
  iExists x. by iFrame.
Qed.

(*
Lemma post_crash_forall {A} P Q:
  (∀ (x: A), P hL x -∗ post_crash (λ hL, Q hL x)) -∗
  (∀ x, P hL x) -∗ post_crash (λ hL, ∀ x, Q hL x).
Proof.
  iIntros "Hall HP". iIntros (???) "#Hrel".
  iIntros (?). iApply ("Hall" with "[HP] [$]"). iApply "HP".
Qed.
*)

Lemma post_crash_exists_intro {A} P (x: A):
  (∀ (x: A), P hL x -∗ post_crash (λ hL, P hL x)) -∗
  P hL x -∗ post_crash (λ hL, ∃ x, P hL x).
Proof.
  iIntros "Hall HP". iIntros (???) "Hrel".
  iMod ("Hall" with "[$] [$]") as "($&H)".
  iModIntro. iExists x. iFrame.
Qed.

Global Instance from_exist_post_crash {A} (Φ: heapGS Σ → iProp Σ) (Ψ: heapGS Σ → A → iProp Σ)
  {Himpl: ∀ hG, FromExist (Φ hG) (λ x, Ψ hG x)} :
  FromExist (post_crash (λ hG, Φ hG)) (λ x, post_crash (λ hG, Ψ hG x)).
Proof.
  hnf; iIntros "H".
  iDestruct "H" as (x) "H".
  rewrite /post_crash.
  iIntros (σ σ' hL') "Hrel".
  iMod ("H" with "Hrel") as "($&H)".
  iModIntro. iExists x; iFrame.
Qed.

Lemma post_crash_named P name:
  named name (post_crash (λ hL, P hL)) ⊢
  post_crash (λ hL, named name (P hL)).
Proof. rewrite //=. Qed.

End post_crash_prop.

Section IntoCrash.

  Context `{hL: !heapGS Σ}.
  Global Instance sep_into_crash P P' Q Q':
    IntoCrash P P' →
    IntoCrash Q Q' →
    IntoCrash (P ∗ Q)%I (λ hL, P' hL ∗ Q' hL)%I.
  Proof.
    iIntros (H1 H2). rewrite /IntoCrash.
    rewrite (@into_crash _ _ P).
    rewrite (@into_crash _ _ Q).
    rewrite post_crash_sep //.
  Qed.

  Global Instance or_into_crash P P' Q Q':
    IntoCrash P P' →
    IntoCrash Q Q' →
    IntoCrash (P ∨ Q)%I (λ hL, P' hL ∨ Q' hL)%I.
  Proof.
    iIntros (H1 H2). rewrite /IntoCrash.
    rewrite (@into_crash _ _ P).
    rewrite (@into_crash _ _ Q).
    rewrite post_crash_or //.
  Qed.

  (*
  Global Instance and_into_crash P P' Q Q':
    IntoCrash P P' →
    IntoCrash Q Q' →
    IntoCrash (P ∧ Q)%I (λ hL, P' hL ∧ Q' hL)%I.
  Proof.
    iIntros (H1 H2). rewrite /IntoCrash.
    rewrite (@into_crash _ _ P).
    rewrite (@into_crash _ _ Q).
    rewrite post_crash_and //.
  Qed.
   *)

  (* XXX: probably should rephrase in terms of IntoPure *)
  Global Instance pure_into_crash (P: Prop) :
    IntoCrash (⌜ P ⌝%I) (λ _, ⌜ P ⌝%I).
  Proof. rewrite /IntoCrash. iIntros "%". by iApply post_crash_pure. Qed.

  Global Instance exist_into_crash {A} Φ Ψ:
    (∀ x : A, IntoCrash (Φ x) (λ hL, Ψ hL x)) →
    IntoCrash (∃ x, Φ x)%I (λ hL, (∃ x, Ψ hL x)%I).
  Proof.
    rewrite /IntoCrash.
    iIntros (?) "H". iDestruct "H" as (?) "HΦ". iPoseProof (H with "[$]") as "HΦ".
    iApply (post_crash_mono with "HΦ"). eauto.
  Qed.

  (*
  Global Instance forall_into_crash {A} Φ Ψ:
    (∀ x : A, IntoCrash (Φ x) (λ hL, Ψ hL x)) →
    IntoCrash (∀ x, Φ x)%I (λ hL, (∀ x, Ψ hL x)%I).
  Proof.
    rewrite /IntoCrash.
    iIntros (?) "H". iApply post_crash_forall; last eauto. iIntros (?). iApply H.
  Qed.
   *)

  (*
  Global Instance post_crash_into_crash P:
    IntoCrash (post_crash P) P.
  Proof. rewrite /IntoCrash. by iApply post_crash_mono. Qed.
   *)

  Lemma into_crash_proper P P' Q Q':
    IntoCrash P Q →
    (P ⊣⊢ P') →
    (∀ hL, Q hL ⊣⊢ Q' hL) →
    IntoCrash P' Q'.
  Proof.
    rewrite /IntoCrash.
    iIntros (HD Hwand1 Hwand2) "HP".
    iApply post_crash_mono; last first.
    { iApply HD. iApply Hwand1. eauto. }
    intros. simpl. by rewrite Hwand2.
  Qed.

  Global Instance big_sepL_into_crash:
    ∀ (A : Type) Φ (Ψ : heapGS Σ → nat → A → iProp Σ) (l : list A),
    (∀ (k : nat) (x : A), IntoCrash (Φ k x) (λ hL, Ψ hL k x)) →
    IntoCrash ([∗ list] k↦x ∈ l, Φ k x)%I (λ hL, [∗ list] k↦x ∈ l, Ψ hL k x)%I.
  Proof.
    intros.
    cut (∀ n, IntoCrash ([∗ list] k↦x ∈ l, Φ (n + k)%nat x)%I
                        (λ hL, [∗ list] k↦x ∈ l, Ψ hL (n + k)%nat x)%I).
    { intros Hres. specialize (Hres O). eauto. }
    induction l => n.
    - rewrite //=. apply _.
    - rewrite //=. apply sep_into_crash; eauto.
      eapply into_crash_proper; first eapply (IHl (S n)).
      * intros. setoid_rewrite Nat.add_succ_r. setoid_rewrite <-Nat.add_succ_l. eauto.
      * intros. setoid_rewrite Nat.add_succ_r. setoid_rewrite <-Nat.add_succ_l. eauto.
  Qed.

  Global Instance big_sepM_into_crash `{Countable K} :
    ∀ (A : Type) Φ (Ψ : heapGS Σ → K → A → iProp Σ) (m : gmap K A),
    (∀ (k : K) (x : A), IntoCrash (Φ k x) (λ hL, Ψ hL k x)) →
    IntoCrash ([∗ map] k↦x ∈ m, Φ k x)%I (λ hL, [∗ map] k↦x ∈ m, Ψ hL k x)%I.
  Proof.
    intros. induction m using map_ind.
    - eapply (into_crash_proper True%I _ (λ _, True%I)).
      { apply _. }
      * rewrite big_sepM_empty; eauto.
      * intros. rewrite big_sepM_empty; eauto.
    - eapply (into_crash_proper (Φ i x ∗ [∗ map] k↦x0 ∈ m, Φ k x0) _
                                (λ _, (Ψ _ i x ∗ [∗ map] k↦x0 ∈ m, Ψ _ k x0)%I)).
      { apply _. }
      * rewrite big_sepM_insert //=.
      * intros. rewrite big_sepM_insert //=.
  Qed.

  Global Instance big_sepS_into_crash `{Countable K} :
    ∀ Φ (Ψ : heapGS Σ → K → iProp Σ) (m : gset K),
    (∀ (k : K), IntoCrash (Φ k) (λ hL, Ψ hL k)) →
    IntoCrash ([∗ set] k ∈ m, Φ k)%I (λ hL, [∗ set] k ∈ m, Ψ hL k)%I.
  Proof.
    intros. induction m as [|i m ? IH] using set_ind_L => //=.
    - eapply (into_crash_proper True%I _ (λ _, True%I)).
      { apply _. }
      * rewrite big_sepS_empty; eauto.
      * intros. rewrite big_sepS_empty; eauto.
    - eapply (into_crash_proper (Φ i ∗ [∗ set] k ∈ m, Φ k) _
                                (λ _, (Ψ _ i ∗ [∗ set] k ∈ m, Ψ _ k)%I)).
      { apply _. }
      * rewrite big_sepS_insert //=.
      * intros. rewrite big_sepS_insert //=.
  Qed.

  Lemma into_crash_post_crash_frame_l P P' `{!IntoCrash P P'} Q:
    P -∗ post_crash Q -∗ post_crash (λ hL', P' hL' ∗ Q hL').
  Proof. iIntros "HP HQ". rewrite (@into_crash _ _ P). iApply post_crash_sep. iFrame. Qed.

  Lemma into_crash_post_crash_frame_r P P' `{!IntoCrash P P'} Q:
    post_crash Q -∗ P  -∗ post_crash (λ hL', Q hL' ∗ P' hL').
  Proof. iIntros "HP HQ". rewrite (@into_crash _ _ P). iApply post_crash_sep. iFrame. Qed.

End IntoCrash.
End goose_lang.

Lemma modus_ponens {Σ} (P Q: iProp Σ)  : P -∗ (P -∗ Q) -∗ Q.
Proof. iIntros "HP Hwand". by iApply "Hwand". Qed.

Ltac crash_env Γ :=
  match Γ with
    | environments.Enil => idtac
    | environments.Esnoc ?Γ' ?id (post_crash _) => crash_env Γ'
    | environments.Esnoc ?Γ' ?id ?A => first [ iEval (rewrite (into_crash (P:=A))) in id || iClear id ] ; crash_env Γ'
  end.

Ltac crash_ctx :=
  match goal with
  | [ |- environments.envs_entails ?Γ _] =>
    let spatial := pm_eval (environments.env_spatial Γ) in
    let intuit := pm_eval (environments.env_intuitionistic Γ) in
    crash_env spatial; crash_env intuit
  end.

Ltac iCrash :=
  crash_ctx;
  iApply (modus_ponens with "[-]"); [ iNamedAccu | ];
  rewrite ?post_crash_named ?post_crash_sep; iApply post_crash_mono;
  intros; simpl;
  let H := iFresh in iIntros H; iNamed H.

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.
Context {Σ: gFunctors}.
Section modality_alt.
  Context `{hL: !heapGS Σ}.
  Context `{Hi1: !IntoCrash P P'}.
  Context `{Hi2: !IntoCrash Q Q'}.
  Lemma test R :
    P -∗ Q -∗ R -∗ post_crash (λ hL', P' hL' ∗ Q' hL').
  Proof using All.
    iIntros "HP HQ HR". iCrash. iFrame.
  Qed.

End modality_alt.

End goose_lang.
