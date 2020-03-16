From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap excl.
From iris.base_logic.lib Require Export proph_map.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From Perennial.Helpers Require Import Transitions.
From Perennial.algebra Require Export na_heap.
From Perennial.goose_lang Require Export lang.
From Perennial.goose_lang Require Export tactics notation.
From Perennial.goose_lang Require Import typing.
Set Default Proof Using "Type".

Notation nonAtomic T := (naMode * T)%type.

(** Override the notations so that scopes and coercions work out *)
Notation "l ↦{ q } v" := (na_heap_mapsto (L:=loc) (V:=val) l q v%V)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" :=
  (na_heap_mapsto (L:=loc) (V:=val) l 1 v%V) (at level 20) : bi_scope.
Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.

(* An FFI layer will use certain CMRAs for its primitive rules.
   Besides needing to know that these CMRAs are included in Σ, there may
   be some implicit ghost names that are used to identify instances
   of these algebras. (For example, na_heap has an implicit name used for
   the ghost heap). These are bundled together in ffiG.

   On a crash, a new "generation" might use fresh names for these instances.
   Thus, an FFI needs to tell the framework how to unbundle ffiG and swap in a
   new set of names.
*)

Class ffi_interp (ffi: ffi_model) :=
  { ffiG: gFunctors -> Set;
    ffi_names : Set;
    ffi_get_names : ∀ Σ, ffiG Σ → ffi_names;
    ffi_update : ∀ Σ, ffiG Σ → ffi_names → ffiG Σ;
    ffi_update_get: ∀ Σ hF names, ffi_get_names Σ (ffi_update _ hF names) = names;
    ffi_get_update: ∀ Σ hF, ffi_update Σ hF (ffi_get_names _ hF) = hF;
    ffi_update_update: ∀ Σ hF names1 names2, ffi_update Σ (ffi_update Σ hF names1) names2
                                     = ffi_update Σ hF names2;
    ffi_ctx: ∀ `{ffiG Σ}, ffi_state -> iProp Σ;
    ffi_start: ∀ `{ffiG Σ}, ffi_state -> iProp Σ;
    ffi_restart: ∀ `{ffiG Σ}, ffi_state -> iProp Σ
  }.

Arguments ffi_ctx {ffi FfiInterp Σ} fG : rename.
Arguments ffi_start {ffi FfiInterp Σ} fG : rename.
Arguments ffi_restart {ffi FfiInterp Σ} fG : rename.

Section goose_lang.
Context `{ffi_semantics: ext_semantics}.
Context {ext_tys: ext_types ext}.
Context `{!ffi_interp ffi}.

Definition traceO := leibnizO (list event).
Definition OracleO := leibnizO (Oracle).

Record tr_names := {
  trace_name : gname;
  oracle_name : gname;
}.

Class traceG (Σ: gFunctors) := {
  trace_inG :> inG Σ (authR (optionUR (exclR traceO)));
  oracle_inG :> inG Σ (authR (optionUR (exclR OracleO)));
  trace_tr_names : tr_names;
}.

Class trace_preG (Σ: gFunctors) := {
  trace_preG_inG :> inG Σ (authR (optionUR (exclR traceO)));
  oracle_preG_inG :> inG Σ (authR (optionUR (exclR OracleO)));
}.

Definition traceG_update (Σ: gFunctors) (hT: traceG Σ) (names: tr_names) :=
  {| trace_inG := trace_inG; oracle_inG := oracle_inG; trace_tr_names := names |}.

Definition traceG_update_pre (Σ: gFunctors) (hT: trace_preG Σ) (names: tr_names) :=
  {| trace_inG := trace_preG_inG; oracle_inG := oracle_preG_inG; trace_tr_names := names |}.

Definition traceΣ : gFunctors :=
  #[GFunctor (authR (optionUR (exclR traceO)));
      GFunctor (authR (optionUR (exclR OracleO)))].

Global Instance subG_crashG {Σ} : subG traceΣ Σ → trace_preG Σ.
Proof. solve_inG. Qed.

Definition trace_auth `{hT: traceG Σ} (l: Trace) :=
  own (trace_name (trace_tr_names)) (● (Excl' (l: traceO))).
Definition trace_frag `{hT: traceG Σ} (l: Trace) :=
  own (trace_name (trace_tr_names)) (◯ (Excl' (l: traceO))).
Definition oracle_auth `{hT: traceG Σ} (o: Oracle) :=
  own (oracle_name (trace_tr_names)) (● (Excl' (o: OracleO))).
Definition oracle_frag `{hT: traceG Σ} (o: Oracle) :=
  own (oracle_name (trace_tr_names)) (◯ (Excl' (o: OracleO))).

Lemma trace_init `{hT: trace_preG Σ} (l: list event) (o: Oracle):
  ⊢ |==> ∃ H : traceG Σ, trace_auth l ∗ trace_frag l ∗ oracle_auth o ∗ oracle_frag o .
Proof.
  iMod (own_alloc (● (Excl' (l: traceO)) ⋅ ◯ (Excl' (l: traceO)))) as (γ) "[H1 H2]".
  { apply auth_both_valid; split; eauto. econstructor. }
  iMod (own_alloc (● (Excl' (o: OracleO)) ⋅ ◯ (Excl' (o: OracleO)))) as (γ') "[H1' H2']".
  { apply auth_both_valid; split; eauto. econstructor. }
  iModIntro. iExists {| trace_tr_names := {| trace_name := γ; oracle_name := γ' |} |}. iFrame.
Qed.

Lemma trace_name_init `{hT: trace_preG Σ} (l: list event) (o: Oracle):
  ⊢ |==> ∃ name : tr_names, let _ := traceG_update_pre _ _ name in
                           trace_auth l ∗ trace_frag l ∗ oracle_auth o ∗ oracle_frag o.
Proof.
  iMod (own_alloc (● (Excl' (l: traceO)) ⋅ ◯ (Excl' (l: traceO)))) as (γ) "[H1 H2]".
  { apply auth_both_valid; split; eauto. econstructor. }
  iMod (own_alloc (● (Excl' (o: OracleO)) ⋅ ◯ (Excl' (o: OracleO)))) as (γ') "[H1' H2']".
  { apply auth_both_valid; split; eauto. econstructor. }
  iModIntro. iExists {| trace_name := γ; oracle_name := γ' |}. iFrame.
Qed.

Lemma trace_reinit `(hT: traceG Σ) (l: list event) (o: Oracle):
  ⊢ |==> ∃ names : tr_names, let _ := traceG_update Σ hT names in
     trace_auth l ∗ trace_frag l ∗ oracle_auth o ∗ oracle_frag o.
Proof.
  iMod (own_alloc (● (Excl' (l: traceO)) ⋅ ◯ (Excl' (l: traceO)))) as (γ) "[H1 H2]".
  { apply auth_both_valid; split; eauto. econstructor. }
  iMod (own_alloc (● (Excl' (o: OracleO)) ⋅ ◯ (Excl' (o: OracleO)))) as (γ') "[H1' H2']".
  { apply auth_both_valid; split; eauto. econstructor. }
  iModIntro. iExists {| trace_name := γ; oracle_name := γ' |}. iFrame.
Qed.

Lemma trace_update `{hT: traceG Σ} (l: Trace) (x: event):
  trace_auth l -∗ trace_frag l ==∗ trace_auth (add_event x l) ∗ trace_frag (add_event x l).
Proof.
  iIntros "Hγ● Hγ◯".
  iMod (own_update_2 _ _ _ (● Excl' _ ⋅ ◯ Excl' _) with "Hγ● Hγ◯") as "[$$]".
  { by apply auth_update, option_local_update, exclusive_local_update. }
  done.
Qed.

Lemma trace_agree `{hT: traceG Σ} (l l': list event):
  trace_auth l -∗ trace_frag l' -∗ ⌜ l = l' ⌝.
Proof.
  iIntros "Hγ1 Hγ2".
  iDestruct (own_valid_2 with "Hγ1 Hγ2") as "H".
  iDestruct "H" as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid.
  done.
Qed.

Lemma oracle_agree `{hT: traceG Σ} (o o': Oracle):
  oracle_auth o -∗ oracle_frag o' -∗ ⌜ o = o' ⌝.
Proof.
  iIntros "Hγ1 Hγ2".
  iDestruct (own_valid_2 with "Hγ1 Hγ2") as "H".
  iDestruct "H" as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid.
  done.
Qed.

Class heapG Σ := HeapG {
  heapG_invG : invG Σ;
  heapG_ffiG : ffiG Σ;
  heapG_na_heapG :> na_heapG loc val Σ;
  heapG_proph_mapG :> proph_mapG proph_id (val * val) Σ;
  heapG_traceG :> traceG Σ;
}.


(* The word 'heap' is really overloaded... *)
Record heap_names := {
  heap_heap_names : na_heap_names;
  heap_proph_name : gname;
  heap_ffi_names : ffi_names;
  heap_trace_names : tr_names;
}.

Definition heap_update_names Σ (hG : heapG Σ) (names: heap_names) :=
  {| heapG_invG := heapG_invG;
     heapG_ffiG := ffi_update Σ (heapG_ffiG) (heap_ffi_names names);
     heapG_na_heapG := na_heapG_update (heapG_na_heapG) (heap_heap_names names);
     heapG_proph_mapG :=
       {| proph_map_inG := proph_map_inG;
          proph_map_name := (heap_proph_name names) |};
     heapG_traceG := traceG_update Σ (heapG_traceG) (heap_trace_names names)
 |}.

Definition heap_update Σ (hG : heapG Σ) (Hinv: invG Σ) (names: heap_names) :=
  {| heapG_invG := Hinv;
     heapG_ffiG := ffi_update Σ (heapG_ffiG) (heap_ffi_names names);
     heapG_na_heapG := na_heapG_update (heapG_na_heapG) (heap_heap_names names);
     heapG_proph_mapG :=
       {| proph_map_inG := proph_map_inG;
          proph_map_name := (heap_proph_name names) |};
     heapG_traceG := traceG_update Σ (heapG_traceG) (heap_trace_names names)
 |}.

Definition heap_get_names Σ (hG : heapG Σ) : heap_names :=
  {| heap_heap_names := na_heapG_get_names (heapG_na_heapG);
     heap_proph_name := proph_map_name (heapG_proph_mapG);
     heap_ffi_names := ffi_get_names Σ (heapG_ffiG);
     heap_trace_names := trace_tr_names;
 |}.

Lemma heap_get_update Σ hG :
  heap_update_names Σ hG (heap_get_names _ hG) = hG.
Proof.
  rewrite /heap_update_names/heap_get_names/na_heapG_update/na_heapG_get_names ffi_get_update //=.
  destruct hG as [?? [] [] []]; eauto.
Qed.

Definition tls (na: naMode) : lock_state :=
  match na with
  | Writing => WSt
  | Reading n => RSt n
  end.

Global Existing Instances heapG_na_heapG.

Global Instance heapG_irisG `{!heapG Σ}:
  irisG heap_lang Σ := {
  iris_invG := heapG_invG;
  state_interp σ κs _ :=
    (na_heap_ctx tls σ.(heap) ∗ proph_map_ctx κs σ.(used_proph_id) ∗ ffi_ctx heapG_ffiG σ.(world)
      ∗ trace_auth σ.(trace) ∗ oracle_auth σ.(oracle))%I;
  fork_post _ := True%I;
}.

Lemma heap_get_update' Σ hG :
  heap_update Σ hG (iris_invG) (heap_get_names _ hG) = hG.
Proof.
  rewrite /heap_update/heap_get_names/na_heapG_update/na_heapG_get_names ffi_get_update //=.
  destruct hG as [?? [] [] []]; eauto.
Qed.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : head_step ?e _ _ _ _ _ |- _ =>
    rewrite /head_step /= in H;
    monad_inv; repeat (simpl in H; monad_inv)
  end.

Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : core.
Local Hint Extern 0 (head_reducible_no_obs _ _) => eexists _, _, _; simpl : core.

(* [simpl apply] is too stupid, so we need extern hints here. *)
Local Hint Extern 1 (head_step _ _ _ _ _ _) => rewrite /head_step /= : core.
Local Hint Extern 1 (relation.bind _ _ _ _ _) => monad_simpl; simpl : core.
Local Hint Extern 1 (relation.runF _ _ _ _) => monad_simpl; simpl : core.
(* Local Hint Extern 0 (head_step (CmpXchg _ _ _) _ _ _ _ _) => eapply CmpXchgS : core. *)
Local Hint Extern 0 (head_step (AllocN _ _) _ _ _ _ _) => apply alloc_fresh : core.
Local Hint Extern 0 (head_step (ArbitraryInt) _ _ _ _ _) => apply arbitrary_int_step : core.
Local Hint Extern 0 (head_step NewProph _ _ _ _ _) => apply new_proph_id_fresh : core.
Local Hint Resolve to_of_val : core.

Global Instance into_val_val v : IntoVal (Val v) v.
Proof. done. Qed.
Global Instance as_val_val v : AsVal (Val v).
Proof. by eexists. Qed.

Theorem heap_head_atomic e :
  (forall σ κ e' σ' efs,
      relation.denote (head_trans e) σ σ' (κ, e', efs) -> is_Some (to_val e')) ->
  head_atomic StronglyAtomic e.
Proof.
  intros Hdenote.
  hnf; intros * H%Hdenote.
  auto.
Qed.

Theorem atomically_is_val Σ (tr: transition Σ val) σ σ' κ e' efs :
  relation.denote (atomically tr) σ σ' (κ, e', efs) ->
  is_Some (to_val e').
Proof.
  intros.
  inversion H; subst; clear H.
  inversion H1; subst; clear H1.
  inversion H; subst.
  eexists; eauto.
Qed.

Ltac inv_undefined :=
  match goal with
  | [ H: relation.denote (match ?e with | _ => _ end) _ _ _ |- _ ] =>
    destruct e; try (apply suchThat_false in H; contradiction)
  end.

Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
  [ apply heap_head_atomic; cbn [relation.denote head_trans]; intros * H;
    repeat inv_undefined;
    try solve [ apply atomically_is_val in H; auto ]
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].

Global Instance alloc_atomic s v w : Atomic s (AllocN (Val v) (Val w)).
Proof.
  solve_atomic.
Qed.

(* PrepareWrite and Store are individually atomic, but the two need to be
combined to actually write to the heap and that is not atomic. *)
Global Instance prepare_write_atomic s v : Atomic s (PrepareWrite (Val v)).
Proof. solve_atomic. Qed.
Global Instance load_atomic s v : Atomic s (Load (Val v)).
Proof. solve_atomic. Qed.
Global Instance finish_store_atomic s v1 v2 : Atomic s (FinishStore (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Global Instance cmpxchg_atomic s v0 v1 v2 : Atomic s (CmpXchg (Val v0) (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Global Instance fork_atomic s e : Atomic s (Fork e).
Proof. solve_atomic.
       simpl in H; monad_inv.
       eexists; eauto.
Qed.
Global Instance skip_atomic s  : Atomic s Skip.
Proof. solve_atomic.
       simpl in H; monad_inv.
       eexists; eauto.
Qed.
Global Instance new_proph_atomic s : Atomic s NewProph.
Proof. solve_atomic. Qed.
Global Instance binop_atomic s op v1 v2 : Atomic s (BinOp op (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Global Instance ext_atomic s op v : Atomic s (ExternalOp op (Val v)).
Proof. solve_atomic. Qed.
Global Instance input_atomic s v : Atomic s (Input (Val v)).
Proof. solve_atomic. Qed.
Global Instance output_atomic s v : Atomic s (Output (Val v)).
Proof. solve_atomic. Qed.

Global Instance proph_resolve_atomic s e v1 v2 :
  Atomic s e → Atomic s (Resolve e (Val v1) (Val v2)).
Proof.
  rename e into e1. intros H σ1 e2 κ σ2 efs [Ks e1' e2' Hfill -> step].
  simpl in *. induction Ks as [|K Ks _] using rev_ind; simpl in Hfill.
  - subst. rewrite /head_step /= in step.
    repeat inv_undefined.
    inversion_clear step.
    repeat inv_undefined.
    inversion_clear H1.
    inversion_clear H2.
    destruct s.
    + eexists; eauto.
    + eapply val_irreducible; simpl.
      eexists; eauto.
  - rewrite fill_app. rewrite fill_app in Hfill.
    assert (∀ v, Val v = fill Ks e1' → False) as fill_absurd.
    { intros v Hv. assert (to_val (fill Ks e1') = Some v) as Htv by by rewrite -Hv.
      apply to_val_fill_some in Htv. destruct Htv as [-> ->]. inversion step; contradiction. }
    destruct K; (inversion Hfill; clear Hfill; subst; try
      match goal with | H : Val ?v = fill Ks e1' |- _ => by apply fill_absurd in H end).
    refine (_ (H σ1 (fill (Ks ++ [K]) e2') _ σ2 efs _)).
    + destruct s; intro Hs; simpl in *.
      * destruct Hs as [v Hs]. apply to_val_fill_some in Hs. by destruct Hs, Ks.
      * apply irreducible_resolve. by rewrite fill_app in Hs.
    + econstructor 1 with (K := Ks ++ [K]); try done. simpl. by rewrite fill_app.
Qed.

Global Instance resolve_proph_atomic s v1 v2 : Atomic s (ResolveProph (Val v1) (Val v2)).
Proof. by apply proph_resolve_atomic, skip_atomic. Qed.

Local Ltac solve_exec_safe := intros; subst; do 3 eexists; cbn; repeat (monad_simpl; simpl).
Local Ltac solve_exec_puredet := rewrite /= /head_step /=; intros; repeat (monad_inv; simpl in * ); eauto.
Local Ltac solve_pure_exec :=
  subst; intros ?; apply nsteps_once, pure_head_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet].

(** The behavior of the various [wp_] tactics with regard to lambda differs in
the following way:

- [wp_pures] does *not* reduce lambdas/recs that are hidden behind a definition.
- [wp_rec] and [wp_lam] reduce lambdas/recs that are hidden behind a definition.

To realize this behavior, we define the class [AsRecV v f x erec], which takes a
value [v] as its input, and turns it into a [RecV f x erec] via the instance
[AsRecV_recv : AsRecV (RecV f x e) f x e]. We register this instance via
[Hint Extern] so that it is only used if [v] is syntactically a lambda/rec, and
not if [v] contains a lambda/rec that is hidden behind a definition.

To make sure that [wp_rec] and [wp_lam] do reduce lambdas/recs that are hidden
behind a definition, we activate [AsRecV_recv] by hand in these tactics. *)
Class AsRecV (v : val) (f x : binder) (erec : expr) :=
  as_recv : v = RecV f x erec.
Hint Mode AsRecV ! - - - : typeclass_instances.
Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

Global Instance pure_recc f x (erec : expr) :
  PureExec True 1 (Rec f x erec) (Val $ RecV f x erec).
Proof. solve_pure_exec. Qed.
Global Instance pure_pairc (v1 v2 : val) :
  PureExec True 1 (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
Proof. solve_pure_exec. Qed.
Global Instance pure_injlc (v : val) :
  PureExec True 1 (InjL $ Val v) (Val $ InjLV v).
Proof. solve_pure_exec. Qed.
Global Instance pure_injrc (v : val) :
  PureExec True 1 (InjR $ Val v) (Val $ InjRV v).
Proof. solve_pure_exec. Qed.

Global Instance pure_beta f x (erec : expr) (v1 v2 : val) `{!AsRecV v1 f x erec} :
  PureExec True 1 (App (Val v1) (Val v2)) (subst' x v2 (subst' f v1 erec)).
Proof. unfold AsRecV in *. solve_pure_exec. Qed.

Global Instance pure_unop op v v' :
  PureExec (un_op_eval op v = Some v') 1 (UnOp op (Val v)) (Val v').
Proof. solve_pure_exec. Qed.

Global Instance pure_binop op v1 v2 v' :
  PureExec (bin_op_eval op v1 v2 = Some v') 1 (BinOp op (Val v1) (Val v2)) (Val v') | 10.
Proof. solve_pure_exec. Qed.
(* Higher-priority instance for EqOp. *)
Global Instance pure_eqop v1 v2 :
  PureExec (vals_compare_safe v1 v2) 1
    (BinOp EqOp (Val v1) (Val v2))
    (Val $ LitV $ LitBool $ bool_decide (v1 = v2)) | 1.
Proof.
  intros Hcompare.
  cut (bin_op_eval EqOp v1 v2 = Some $ LitV $ LitBool $ bool_decide (v1 = v2)).
  { intros. revert Hcompare. solve_pure_exec. }
  rewrite /bin_op_eval /= decide_True //.
Qed.

Global Instance pure_if_true e1 e2 : PureExec True 1 (If (Val $ LitV $ LitBool true) e1 e2) e1.
Proof. solve_pure_exec. Qed.

Global Instance pure_if_false e1 e2 : PureExec True 1 (If (Val $ LitV  $ LitBool false) e1 e2) e2.
Proof. solve_pure_exec. Qed.

Global Instance pure_fst v1 v2 :
  PureExec True 1 (Fst (Val $ PairV v1 v2)) (Val v1).
Proof. solve_pure_exec. Qed.

Global Instance pure_snd v1 v2 :
  PureExec True 1 (Snd (Val $ PairV v1 v2)) (Val v2).
Proof. solve_pure_exec. Qed.

Global Instance pure_case_inl v e1 e2 :
  PureExec True 1 (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)).
Proof. solve_pure_exec. Qed.

Global Instance pure_case_inr v e1 e2 :
  PureExec True 1 (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)).
Proof. solve_pure_exec. Qed.

Section lifting.
Context `{!heapG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

Lemma wp_panic s msg E Φ :
  ▷ False -∗ WP Panic msg @ s; E {{ Φ }}.
Proof.
  iIntros ">[] HΦ".
Qed.

Lemma wp_ArbitraryInt stk E :
  {{{ True }}}
    ArbitraryInt @ stk; E
  {{{ (x:u64), RET #x; True }}}.
Proof.
  iIntros (Φ) "Htr HΦ". iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1 κ κs n) "(Hσ&?&?&?&?) !>"; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step. iFrame.
  iModIntro. by iApply "HΦ".
Qed.

Lemma wp_output s E tr lit :
  {{{ trace_frag tr }}}
     Output (LitV lit) @ s; E
  {{{ RET (LitV LitUnit); trace_frag (add_event (Out_ev lit) tr)}}}.
Proof.
  iIntros (Φ) "Htr HΦ". iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1 κ κs n) "(Hσ&?&?&Htr_auth&?) !>"; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step. iFrame.
  iDestruct (trace_agree with "[$] [$]") as %?; subst.
  iMod (trace_update with "[$] [$]") as "(?&?)".
  iModIntro. iFrame; iSplitL; last done. by iApply "HΦ".
Qed.

Lemma wp_input s E tr sel Or :
  {{{ trace_frag tr ∗ oracle_frag Or }}}
     Input (LitV sel) @ s; E
  {{{ RET (LitV (LitInt (Or tr sel))); trace_frag (add_event (In_ev sel (LitInt (Or tr sel))) tr)}}}.
Proof.
  iIntros (Φ) "(Htr&Hor) HΦ". iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1 κ κs n) "(Hσ&?&?&Htr_auth&Hor_auth) !>"; iSplit.
  { iPureIntro. unshelve (by eauto); apply (U64 0). }
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iDestruct (trace_agree with "[$] [$]") as %?; subst.
  iDestruct (oracle_agree with "[$] [$]") as %?; subst.
  iFrame. iMod (trace_update with "[$] [$]") as "(?&?)".
  iModIntro. iFrame; iSplitL; last done. by iApply "HΦ".
Qed.

(** Fork: Not using Texan triples to avoid some unnecessary [True] *)
Lemma wp_fork s E e Φ :
  ▷ WP e @ s; ⊤ {{ _, True }} -∗ ▷ Φ (LitV LitUnit) -∗ WP Fork e @ s; E {{ Φ }}.
Proof.
  iIntros "He HΦ". iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1 κ κs n) "Hσ !>"; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step. by iFrame.
Qed.

(** Heap *)
(** The "proper" [allocN] are derived in [array]. *)

Theorem heap_array_app V l (vs1 vs2: list V) :
  heap_array l (vs1 ++ vs2) = heap_array l vs1 ∪ heap_array (l +ₗ (length vs1)) vs2.
Proof.
  revert l.
  induction vs1; simpl; intros.
  - rewrite left_id loc_add_0 //.
  - rewrite IHvs1.
    rewrite loc_add_assoc.
    replace (1 + strings.length vs1) with (Z.of_nat (S (strings.length vs1))) by lia.
    (* true, but only due to disjointness *)
    admit.
Abort.

Theorem concat_replicate_S A n (vs: list A) :
  concat_replicate (S n) vs = vs ++ concat_replicate n vs.
Proof.
  reflexivity.
Qed.

Theorem concat_replicate_length A n (vs: list A) :
  length (concat_replicate n vs) = (n * length vs)%nat.
Proof.
  induction n; simpl; auto.
  rewrite concat_replicate_S app_length IHn //.
Qed.

Lemma heap_array_to_seq_mapsto l vs :
  ([∗ map] l' ↦ vm ∈ heap_array l vs, l' ↦ vm) -∗
  [∗ list] j ↦ v ∈ vs, (l +ₗ j) ↦ v.
Proof.
  iIntros "Hvs". iInduction vs as [|vs] "IH" forall (l); simpl.
  { done. }
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&?&Hjl&_)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Definition big_opL_add_spec (M: ofeT) (o: M -> M -> M) {mon:monoid.Monoid o} f start off k n :=
  Proper (equiv ==> equiv ==> equiv) o ->
  big_opL o (fun i x => f (i + k)%nat x) (seq (start + off) n) ≡
  big_opL o (fun i x => f i (x + off)%nat) (seq (start + k)%nat n).

(*
Eval compute in (fun M o {mon:monoid.Monoid o} f off => big_opL_add_spec M o f 2%nat off 4%nat).
*)

Theorem big_opL_add (M: ofeT) (o: M -> M -> M) {mon:monoid.Monoid o} f start off k n :
  Proper (equiv ==> equiv ==> equiv) o ->
  big_opL o (fun i x => f (k + i)%nat x) (seq (start + off) n) ≡
  big_opL o (fun i x => f (k + i)%nat (x + off)%nat) (seq start n).
Proof.
  intros.
  revert start k off.
  induction n; simpl; auto; intros.
  apply H; auto.
  setoid_rewrite Nat.add_succ_r.
  rewrite <- (IHn (S start) (S k)).
  simpl; auto.
Qed.

Theorem big_sepL_offset {b:bi} f off n :
  big_opL (@bi_sep b) (fun i x => f i x) (seq off n) ≡
  big_opL bi_sep (fun i x => f i (x + off)%nat) (seq 0%nat n).
Proof.
  apply (big_opL_add _ _ _ 0%nat _ 0%nat _ _).
Qed.

Lemma Zmul_nat_add1_r (x k:nat) :
  (x + 1)%nat * k = k + x * k.
Proof. lia. Qed.

Lemma heap_array_replicate_to_nested_mapsto l vs (n : nat) :
  ([∗ map] l' ↦ vm ∈ heap_array l (concat_replicate n vs), l' ↦ vm) -∗
  [∗ list] i ∈ seq 0 n, [∗ list] j ↦ v ∈ vs, (l +ₗ ((i : nat) * Z.of_nat (length vs)) +ₗ j)%nat ↦ v.
Proof.
  iIntros "Hmap".
  iDestruct (heap_array_to_seq_mapsto with "Hmap") as "Hvs".
  iInduction n as [|n] "IH" forall (l); simpl.
  { done. }
  rewrite concat_replicate_S.
  iDestruct (big_sepL_app with "Hvs") as "[Hvs Hconcat]".
  iSplitL "Hvs".
  - rewrite loc_add_0.
    iFrame.
  - setoid_rewrite Nat2Z.inj_add.
    setoid_rewrite <- loc_add_assoc.
    iDestruct ("IH" with "Hconcat") as "Hseq".
    rewrite (big_sepL_offset _ 1%nat).
    setoid_rewrite Zmul_nat_add1_r.
    setoid_rewrite <- loc_add_assoc.
    iExact "Hseq".
Qed.

Definition mapsto_vals l q vs : iProp Σ :=
  ([∗ list] j↦vj ∈ vs, (l +ₗ j) ↦{q} vj)%I.

Lemma wp_allocN_seq s E v (n: u64) :
  (0 < int.val n)%Z →
  {{{ True }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  {{{ l, RET LitV (LitLoc l); [∗ list] i ∈ seq 0 (int.nat n),
                              (mapsto_vals (l +ₗ (length (flatten_struct v) * Z.of_nat i)) 1 (flatten_struct v)) }}}.
Proof.
  iIntros (Hn Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs k) "[Hσ Hκs] !>"; iSplit; first by auto with lia.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (na_heap_alloc_gen
          _ _ (fmap Free (heap_array
               l (concat_replicate (int.nat n) (flatten_struct v)))) with "Hσ")
    as "(Hσ & Hl)".
  { rewrite heap_array_fmap. apply heap_array_map_disjoint.
    rewrite map_length concat_replicate_length. auto with lia. }
  { intros ??. rewrite lookup_fmap.
    destruct (heap_array l _ !! _) => //=.
    inversion 1; subst => //=; congruence. }
  iModIntro; iSplit; first done.
  rewrite heap_array_fmap. iFrame.
  iApply "HΦ".
  unfold mapsto_vals.
  rewrite -heap_array_fmap.
  rewrite big_sepM_fmap.
  iDestruct (heap_array_replicate_to_nested_mapsto with "Hl") as "Hl".
  iApply (big_sepL_mono with "Hl").
  iIntros (k0 j _) "H".
  setoid_rewrite Z.mul_comm at 1.
  { by iFrame. }
Qed.

Lemma wp_alloc_untyped stk E v v0 :
  flatten_struct v = [v0] ->
  {{{ True }}} ref (Val v) @ stk; E
  {{{ l, RET LitV (LitLoc l); l ↦ v0 }}}.
Proof.
  assert (0 < int.val (U64 1)) by (change (int.val 1) with 1; lia).
  iIntros (Hn Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs k) "[Hσ Hκs] !>"; iSplit; first by auto with lia.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (na_heap_alloc_gen
          _ _ (fmap Free (heap_array
               l [v0])) with "Hσ")
    as "(Hσ & Hm)".
  { rewrite heap_array_fmap. apply heap_array_map_disjoint.
    rewrite Z.mul_1_l Hn /= in H0.
    simpl; auto with lia. }
  { intros ??. rewrite lookup_fmap.
    destruct (heap_array l _ !! _) => //=.
    inversion 1; subst => //=; congruence. }
  iModIntro; iSplit; first done.
  change (int.nat 1) with 1%nat; simpl.
  iFrame "Hκs".
  rewrite -heap_array_fmap.
  replace (flatten_struct v); simpl.
  iFrame "Hσ". iApply "HΦ".
  rewrite right_id big_sepM_fmap big_sepM_singleton; iFrame.
Qed.

Lemma wp_load s E l q v :
  {{{ ▷ l ↦{q} v }}} Load (Val $ LitV $ LitLoc l) @ s; E {{{ RET v; l ↦{q} v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (na_heap_read with "Hσ Hl") as %([|]&?&Heq&Hlock).
  { simpl in Hlock. congruence. }
  iSplit; first by eauto 8.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Theorem is_Writing_Some A (mna: option (nonAtomic A)) a :
  mna = Some (Writing, a) ->
  is_Writing mna.
Proof.
  rewrite /is_Writing; eauto.
Qed.

Hint Resolve is_Writing_Some.

Lemma wp_prepare_write s E l v :
  {{{ ▷ l ↦ v }}} PrepareWrite (Val $ LitV (LitLoc l)) @ s; E
  {{{ RET LitV LitUnit; na_heap_mapsto_st WSt l 1 v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs]".
  iMod (na_heap_write_prepare _ _ _ _ Writing with "Hσ Hl") as (lk1 (Hlookup&Hlock)) "(?&?)"; first done.
  destruct lk1; inversion Hlock; subst. iModIntro.
  iSplit; first by eauto 8. iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.

Lemma wp_finish_store s E l v v' :
  {{{ ▷ na_heap_mapsto_st WSt l 1 v' }}} FinishStore (Val $ LitV (LitLoc l)) (Val v) @ s; E
  {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs]".
  iMod (na_heap_write_finish_vs _ _ _ _ (Reading 0) with "Hl Hσ") as (lkw (?&Hlock)) "(Hσ&Hl)"; first done.
  destruct lkw; inversion Hlock; subst. iModIntro.
  iSplit; first by eauto. iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.

Lemma na_heap_valid_map (σ: gmap _ _) l q vs :
  na_heap_ctx tls σ -∗
              ([∗ map] l↦v ∈ heap_array l vs, l ↦{q} v) -∗
              ⌜forall i, (i < (length vs))%nat -> is_Some (σ !! (l +ₗ i))⌝.
Proof.
  iIntros "Hctx Hmap".
  iIntros (i Hi).
  apply lookup_lt_is_Some_2 in Hi.
  destruct Hi as [v ?].
  assert (heap_array l vs !! (l +ₗ i) = Some v).
  { apply heap_array_lookup.
    exists (Z.of_nat i).
    rewrite Nat2Z.id; intuition eauto.
    lia. }
  iDestruct (big_sepM_lookup _ _ _ _ H0 with "Hmap") as "H".
  iDestruct (na_heap_read with "Hctx H") as %(?&?&?&?).
  eauto.
Qed.

Lemma wp_cmpxchg_fail s E l q v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦{q} v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool false); l ↦{q} v' }}}.
Proof.
  iIntros (?? Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@na_heap_read with "Hσ Hl") as %(lk&?&?&?Hlock).
  destruct lk; inversion Hlock; subst.
  iSplit; first by eauto 8. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  rewrite bool_decide_false //.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_cmpxchg_suc s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦ v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool true); l ↦ v2 }}}.
Proof.
  iIntros (?? Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs]".
  iDestruct (@na_heap_read_1 with "Hσ Hl") as %(lk&?&?Hlock).
  destruct lk; inversion Hlock; subst.
  iMod (na_heap_write _ _ _ (Reading 0) with "Hσ Hl") as "(?&?)"; first done.
  iModIntro.
  iSplit; first by eauto 8. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  rewrite bool_decide_true //.
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.

Lemma wp_new_proph s E :
  {{{ True }}}
    NewProph @ s; E
  {{{ pvs p, RET (LitV (LitProphecy p)); proph p pvs }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "(Hσ&HR&Hffi) !>". iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep). inv_head_step.
  iMod (proph_map_new_proph p with "HR") as "[HR Hp]"; first done.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

(* In the following, strong atomicity is required due to the fact that [e] must
be able to make a head step for [Resolve e _ _] not to be (head) stuck. *)

Lemma resolve_reducible e σ (p : proph_id) v :
  Atomic StronglyAtomic e → reducible e σ →
  reducible (Resolve e (Val (LitV (LitProphecy p))) (Val v)) σ.
Proof.
  intros A (κ & e' & σ' & efs & H).
  exists (κ ++ [(p, (default v (to_val e'), v))]), e', σ', efs.
  eapply Ectx_step with (K:=[]); try done.
  assert (∃w, Val w = e') as [w <-].
  { unfold Atomic in A. apply (A σ e' κ σ' efs) in H. unfold is_Some in H.
    destruct H as [w H]. exists w. simpl in H. by apply (of_to_val _ _ H). }
  simpl.
  rewrite /head_step /=.
  econstructor.
  - by apply prim_step_to_val_is_head_step.
  - simpl.
    econstructor; auto.
Qed.

Lemma step_resolve e vp vt σ1 κ e2 σ2 efs :
  Atomic StronglyAtomic e →
  prim_step (Resolve e (Val vp) (Val vt)) σ1 κ e2 σ2 efs →
  head_step (Resolve e (Val vp) (Val vt)) σ1 κ e2 σ2 efs.
Proof.
  intros A [Ks e1' e2' Hfill -> step]. simpl in *.
  induction Ks as [|K Ks _] using rev_ind.
  + simpl in *. subst.
    inv_head_step. repeat inv_undefined.
    inversion_clear step. repeat inv_undefined.
    simpl in H0; monad_inv.
    rewrite /head_step /=.
    econstructor; eauto; simpl.
    econstructor; auto.
  + rewrite fill_app /= in Hfill. destruct K; inversion Hfill; subst; clear Hfill.
    - assert (fill_item K (fill Ks e1') = fill (Ks ++ [K]) e1') as Eq1;
        first by rewrite fill_app.
      assert (fill_item K (fill Ks e2') = fill (Ks ++ [K]) e2') as Eq2;
        first by rewrite fill_app.
      rewrite fill_app /=. rewrite Eq1 in A.
      assert (is_Some (to_val (fill (Ks ++ [K]) e2'))) as H.
      { apply (A σ1 _ κ σ2 efs). eapply Ectx_step with (K0 := Ks ++ [K]); done. }
      destruct H as [v H]. apply to_val_fill_some in H. by destruct H, Ks.
    - assert (to_val (fill Ks e1') = Some vp); first by rewrite -H1 //.
      apply to_val_fill_some in H. destruct H as [-> ->].
      rewrite /head_step /= in step; monad_inv.
    - assert (to_val (fill Ks e1') = Some vt); first by rewrite -H2 //.
      apply to_val_fill_some in H. destruct H as [-> ->].
      rewrite /head_step /= in step; monad_inv.
Qed.

Lemma wp_resolve s E e Φ (p : proph_id) v (pvs : list (val * val)) :
  Atomic StronglyAtomic e →
  to_val e = None →
  proph p pvs -∗
  WP e @ s; E {{ r, ∀ pvs', ⌜pvs = (r, v)::pvs'⌝ -∗ proph p pvs' -∗ Φ r }} -∗
  WP Resolve e (Val $ LitV $ LitProphecy p) (Val v) @ s; E {{ Φ }}.
Proof.
  (* TODO we should try to use a generic lifting lemma (and avoid [wp_unfold])
     here, since this breaks the WP abstraction. *)
  iIntros (A He) "Hp WPe". rewrite !wp_unfold /wp_pre /= He. simpl in *.
  iIntros (σ1 κ κs n) "(Hσ&Hκ&Hw)". destruct κ as [|[p' [w' v']] κ' _] using rev_ind.
  - iMod ("WPe" $! σ1 [] κs n with "[$Hσ $Hκ $Hw]") as "[Hs WPe]". iModIntro. iSplit.
    { iDestruct "Hs" as "%". iPureIntro. destruct s; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step). exfalso. apply step_resolve in step; last done.
    rewrite /head_step /= in step.
    inversion_clear step.
    repeat inv_undefined.
    simpl in H0; monad_inv.
    match goal with H: [] = ?κs ++ [_] |- _ => by destruct κs end.
  - rewrite -app_assoc.
    iMod ("WPe" $! σ1 _ _ n with "[$Hσ $Hκ $Hw]") as "[Hs WPe]". iModIntro. iSplit.
    { iDestruct "Hs" as %?. iPureIntro. destruct s; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step). apply step_resolve in step; last done.
    rewrite /head_step /= in step.
    inversion_clear step.
    repeat inv_undefined.
    simpl in H0; monad_inv.
    simplify_list_eq.
    rename v0 into w', s2 into σ2, l into efs.
    iMod ("WPe" $! (Val w') σ2 efs with "[%]") as "WPe".
    { by eexists [] _ _. }
    iModIntro. iNext. iMod "WPe" as "[[$ (Hκ&Hw)] WPe]".
    iMod (proph_map_resolve_proph p (w',v) κs with "[$Hκ $Hp]") as (vs' ->) "[$ HPost]".
    iModIntro. rewrite !wp_unfold /wp_pre /=. iDestruct "WPe" as "[HΦ $]".
    iFrame.
    iMod "HΦ". iModIntro. by iApply "HΦ".
Qed.

(** Lemmas for some particular expression inside the [Resolve]. *)
Lemma wp_resolve_proph s E (p : proph_id) (pvs : list (val * val)) v :
  {{{ proph p pvs }}}
    ResolveProph (Val $ LitV $ LitProphecy p) (Val v) @ s; E
  {{{ pvs', RET (LitV LitUnit); ⌜pvs = (LitV LitUnit, v)::pvs'⌝ ∗ proph p pvs' }}}.
Proof.
  iIntros (Φ) "Hp HΦ". iApply (wp_resolve with "Hp"); first done.
  iApply wp_pure_step_later=> //=. iApply wp_value.
  iIntros "!>" (vs') "HEq Hp". iApply "HΦ". iFrame.
Qed.

Lemma wp_resolve_cmpxchg_suc s E l (p : proph_id) (pvs : list (val * val)) v1 v2 v :
  vals_compare_safe v1 v1 →
  {{{ proph p pvs ∗ ▷ l ↦ v1 }}}
    Resolve (CmpXchg #l v1 v2) #p v @ s; E
  {{{ RET (v1, #true) ; ∃ pvs', ⌜pvs = ((v1, #true)%V, v)::pvs'⌝ ∗ proph p pvs' ∗ l ↦ v2 }}}.
Proof.
  iIntros (Hcmp Φ) "[Hp Hl] HΦ".
  iApply (wp_resolve with "Hp"); first done.
  assert (val_is_unboxed v1) as Hv1; first by destruct Hcmp.
  iApply (wp_cmpxchg_suc with "Hl"); [done..|]. iIntros "!> Hl".
  iIntros (pvs' ->) "Hp". iApply "HΦ". eauto with iFrame.
Qed.

Lemma wp_resolve_cmpxchg_fail s E l (p : proph_id) (pvs : list (val * val)) q v' v1 v2 v :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {{{ proph p pvs ∗ ▷ l ↦{q} v' }}}
    Resolve (CmpXchg #l v1 v2) #p v @ s; E
  {{{ RET (v', #false) ; ∃ pvs', ⌜pvs = ((v', #false)%V, v)::pvs'⌝ ∗ proph p pvs' ∗ l ↦{q} v' }}}.
Proof.
  iIntros (NEq Hcmp Φ) "[Hp Hl] HΦ".
  iApply (wp_resolve with "Hp"); first done.
  iApply (wp_cmpxchg_fail with "Hl"); [done..|]. iIntros "!> Hl".
  iIntros (pvs' ->) "Hp". iApply "HΦ". eauto with iFrame.
Qed.

End lifting.
End goose_lang.

Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

Arguments heapG_ffiG {_ _ _ _ hG}: rename.
