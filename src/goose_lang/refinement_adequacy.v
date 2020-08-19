From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From iris.base_logic.lib Require Import proph_map.
From iris.program_logic Require Export weakestpre adequacy.
From Perennial.algebra Require Import proph_map.
From Perennial.goose_lang Require Import proofmode notation.
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy spec_assert.
From Perennial.goose_lang Require Import typing adequacy refinement.
From Perennial.goose_lang Require Export recovery_adequacy spec_assert.

Set Default Proof Using "Type".

Class spec_ffi_interp_adequacy `{spec_ffi: @spec_ffi_interp ffi} `{EXT: !spec_ext_semantics ext ffi} :=
  { spec_ffi_interp_adequacy_field : @ffi_interp_adequacy _ (spec_ffi_interp_field)
                                                          (spec_ext_op_field)
                                                          (spec_ext_semantics_field) }.

Class refinement_heapPreG `{ext: spec_ext_op} `{@spec_ffi_interp_adequacy ffi spec_ffi ext EXT} Σ := HeapPreG {
  refinement_heap_preG_heap :> na_heapPreG loc (@val spec_ext_op_field) Σ;
  refinement_heap_preG_ffi : @ffi_preG (@spec_ffi_model_field ffi)
                                       (@spec_ffi_interp_field _ spec_ffi)
                                       _ _ (spec_ffi_interp_adequacy_field) Σ;
  refinement_heap_preG_trace :> trace_preG Σ;
  refinement_heap_preG_frac :> frac_countG Σ;
}.

Existing Instances spec_ext_op_field spec_ext_semantics_field spec_ffi_model_field spec_ffi_interp_field spec_ffi_interp_adequacy_field.
Definition refinement_heapΣ `{ext: spec_ext_op} `{@spec_ffi_interp_adequacy ffi spec_ffi ext EXT} : gFunctors := #[invΣ; na_heapΣ loc val; ffiΣ; proph_mapΣ proph_id (val * val); traceΣ; frac_countΣ].
Instance subG_refinement_heapPreG `{ext: spec_ext_op} `{@spec_ffi_interp_adequacy ffi spec_ffi ext EXT} {Σ} :
  subG refinement_heapΣ Σ → refinement_heapPreG Σ.
Proof. solve_inG_deep. Qed.

Section refinement.
Context {ext: ext_op}.
Context {ffi: ffi_model}.
Context {ffi_semantics: ext_semantics ext ffi}.
Context `{interp: !ffi_interp ffi}.
Context `{interp_adeq: !ffi_interp_adequacy}.

Context {spec_ext: spec_ext_op}.
Context {spec_ffi: spec_ffi_model}.
Context {spec_ffi_semantics: spec_ext_semantics spec_ext spec_ffi}.
Context `{spec_interp: @spec_ffi_interp spec_ffi}.
Context `{spec_adeq: !spec_ffi_interp_adequacy}.

Context `{Hhpre: @heapPreG ext ffi ffi_semantics interp _ Σ}.
Context `{Hcpre: @cfgPreG spec_lang Σ}.
Context `{Hrpre: @refinement_heapPreG spec_ext spec_ffi spec_interp _ spec_adeq Σ}.

Existing Instances spec_ffi_model_field spec_ext_op_field spec_ext_semantics_field spec_ffi_interp_field
         spec_ffi_interp_adequacy_field.

Lemma goose_spec_init1 {hG: heapG Σ} r tp0 σ0 tp σ s tr or:
  ffi_initP σ.(world) →
  null_non_alloc σ.(heap) →
  σ.(trace) = tr →
  σ.(oracle) = or →
  erased_rsteps (CS := spec_crash_lang) r (tp0, σ0) (tp, σ) s →
  crash_safe (CS := spec_crash_lang) r (tp0, σ0) →
  ⊢ trace_frag tr -∗ oracle_frag or -∗
   |={⊤}=> ∃ _ : refinement_heapG Σ, spec_ctx' r (tp0, σ0) ∗ source_pool_map (tpool_to_map tp)
                                               ∗ ffi_start (refinement_spec_ffiG) σ.(world)
                                               ∗ trace_ctx.
Proof using Hrpre Hcpre.
  iIntros (???? Hsteps Hsafe) "Htr Hor".
  iMod (source_cfg_init1 r tp0 σ0 tp σ) as (Hcfg) "(Hsource_ctx&Hpool&Hstate)"; eauto.
  iMod (na_heap_init tls σ.(heap)) as (Hrheap) "Hrh".
  iMod (ffi_name_init _ (refinement_heap_preG_ffi) σ.(world)) as (HffiG) "(Hrw&Hrs)"; first auto.
  iMod (trace_init σ.(trace) σ.(oracle)) as (HtraceG) "(?&Htr'&?&Hor')".
  set (HrhG := (refinement_HeapG _ (ffi_update_pre _ (refinement_heap_preG_ffi) HffiG) HtraceG Hcfg Hrheap) _).
  iExists HrhG.
  rewrite /spec_ctx'. iFrame.
  iMod (inv_alloc (spec_stateN) _
                  (∃ σ0 : language.state goose_lang, (source_state σ0 ∗ spec_assert.spec_interp σ0))
       with "[-Htr' Hor' Htr Hor]")%I as "$".
  { iNext. iExists _. iFrame. iPureIntro; eauto. }
  rewrite /trace_ctx.
  iMod (inv_alloc (spec_traceN) _ trace_inv with "[-]") as "$".
  { iNext. subst. rewrite /trace_inv. iExists _, _, _, _. iFrame; eauto. }
  done.
Qed.

Lemma goose_spec_init2 {hG: heapG Σ} r tp σ tr or:
  ffi_initP σ.(world) →
  null_non_alloc σ.(heap) →
  σ.(trace) = tr →
  σ.(oracle) = or →
  crash_safe (CS := spec_crash_lang) r (tp, σ) →
  ⊢ trace_frag tr -∗ oracle_frag or -∗
   |={⊤}=> ∃ _ : refinement_heapG Σ, spec_ctx' r (tp, σ) ∗ source_pool_map (tpool_to_map tp)
                                               ∗ ffi_start (refinement_spec_ffiG) σ.(world)
                                               ∗ trace_ctx.
Proof using Hrpre Hcpre.
  intros; eapply goose_spec_init1; eauto.
  { do 2 econstructor. }
Qed.

Lemma goose_spec_crash_init {hG: heapG Σ} {hRG: refinement_heapG Σ} r tp0 σ0 tp σ σ_post_crash s tr or:
  σ_post_crash.(trace) = tr →
  σ_post_crash.(oracle) = or →
  erased_rsteps (CS := spec_crash_lang) r (tp0, σ0) (tp, σ) s →
  crash_safe (CS := spec_crash_lang) r (tp0, σ0) →
  crash_prim_step spec_crash_lang σ σ_post_crash →
  ⊢ trace_frag tr -∗ oracle_frag or -∗ ffi_ctx refinement_spec_ffiG (world σ) -∗
   |={⊤}=> ∃ hRG' : refinement_heapG Σ, spec_ctx' r (tp0, σ0) ∗ source_pool_map (tpool_to_map [r])
             ∗ ffi_crash_rel Σ (@refinement_spec_ffiG _ _ _ _ _ hRG) (world σ)
                               (refinement_spec_ffiG) (world σ_post_crash)
             ∗ ffi_restart (refinement_spec_ffiG) (world σ_post_crash)
             ∗ trace_ctx.
Proof using Hrpre Hcpre.
  iIntros (?? Hsteps Hsafe Hcrash) "Htr Hor Hffi".
  iMod (source_cfg_init1 r tp0 σ0 [r] σ_post_crash) as (Hcfg) "(Hsource_ctx&Hpool&Hstate)"; eauto.
  { eapply erased_rsteps_r; eauto. econstructor. }
  iMod (na_heap_init tls σ_post_crash.(heap)) as (Hrheap) "Hrh".
  iMod (ffi_crash _ σ.(world) σ_post_crash.(world) with "Hffi")
    as (ffi_names) "(Hrw&Hcrash_rel&Hrs)".
  { inversion Hcrash. subst. eauto. }
  iMod (trace_init σ_post_crash.(trace) σ_post_crash.(oracle)) as (HtraceG) "(?&Htr'&?&Hor')".
  set (HrhG := (refinement_HeapG _ (ffi_update Σ (refinement_spec_ffiG) ffi_names) HtraceG Hcfg Hrheap) _).
  iExists HrhG.
  rewrite /spec_ctx'. iFrame.
  iMod (inv_alloc (spec_stateN) _
                  (∃ σ0 : language.state goose_lang, (source_state σ0 ∗ spec_assert.spec_interp σ0))
       with "[-Htr' Hor' Htr Hor]")%I as "$".
  { iNext. iExists σ_post_crash. iFrame.
    inversion Hcrash. subst. simpl. iPureIntro => ?. rewrite lookup_empty //. }
  rewrite /trace_ctx.
  iMod (inv_alloc (spec_traceN) _ trace_inv with "[-]") as "$".
  { iNext. subst. rewrite /trace_inv. iExists _, _, _, _. iFrame; eauto. }
  done.
Qed.

Lemma trace_inv_open {hG: heapG Σ} {hrG: refinement_heapG Σ}  rs es σs σ:
  spec_ctx' rs ([es], σs) -∗
  trace_ctx -∗
  trace_auth (trace σ) -∗
  oracle_auth (oracle σ) -∗
  |={⊤,∅}=> ⌜∃ (t2s : list expr) (σ2s : state) (stats : status),
            erased_rsteps (CS := spec_crash_lang) rs ([es], σs) (t2s, σ2s) stats ∧ trace σ2s = trace σ⌝.
Proof.
  iIntros "Hspec Htrace Htrace_auth Horacle_auth".
  rewrite /spec_ctx'.
  iDestruct "Hspec" as "(Hsource&Hspec_state)".
  iInv "Hsource" as "Hsource_open" "_".
  iInv "Hspec_state" as "Hspec_state_open" "_".
  iInv "Htrace" as ">Htrace_open" "_".
  rewrite /source_inv.
  iDestruct "Hsource_open" as (???) "(>Hsource_auth&>(%&%))".
  iDestruct "Hspec_state_open" as (?) "(>Hsource_state&Hspec_interp)".
  iDestruct "Hspec_interp" as "(?&?&>Hspec_trace_auth&>Hspec_oracle_auth&Hnull)".
  rewrite /trace_inv.
  iDestruct "Htrace_open" as (???? ??) "(Htrace_frag&Hspec_trace_frag&Horacle_frag&Htspec_oracle_frag)".
  iDestruct (source_state_reconcile with "[$] [$]") as %Heq0.
  iDestruct (trace_agree with "Htrace_auth [$]") as %Heq1.
  iDestruct (trace_agree with "Hspec_trace_auth [$]") as %Heq2.
  iDestruct (oracle_agree with "Horacle_auth [$]") as %Heq3.
  iDestruct (oracle_agree with "Hspec_oracle_auth [$]") as %Heq4.
  iApply fupd_mask_weaken; first by set_solver+.
  iExists _, _, _; iPureIntro; split.
  { eauto. }
  { subst. congruence. }
Qed.

Theorem heap_recv_refinement_adequacy `{crashPreG Σ} k es e rs r σs σ φ φr (Φinv: heapG Σ → iProp Σ) :
  null_non_alloc σs.(heap) →
  ffi_initP σ.(world) →
  ffi_initP σs.(world) →
  σ.(trace) = σs.(trace) →
  σ.(oracle) = σs.(oracle) →
  (∀ `{Hheap : !heapG Σ} `{Hc: !crashG Σ} {Href: refinement_heapG Σ}
    (* (HPF: ∃ Hi' Ht', Hheap = heap_update_pre _ _ Hi' (@pbundleT _ Σ Ht') *),
     ⊢ |={⊤}=>
       (spec_ctx' rs ([es], σs) -∗
        trace_ctx -∗
       □ (∀ hG, Φinv hG -∗
                       ∃ Href', spec_ctx' (hR := Href') rs ([es], σs) ∗ trace_ctx (hR := Href')) ∗
        (ffi_start (heapG_ffiG) σ.(world) -∗ ffi_start (refinement_spec_ffiG) σs.(world) -∗ O ⤇ es -∗ wpr NotStuck k ⊤ e r (λ v, ⌜φ v⌝) Φinv (λ _ v, ⌜φr v⌝)))) →
  trace_refines e r σ es rs σs.
Proof using Hrpre Hhpre Hcpre.
  intros ????? Hwp Hsafe.
  cut (recv_adequate (CS := goose_crash_lang) NotStuck e r σ (λ v _, φ v) (λ v _, φr v)
                     (λ σ2,
                      ∃ t2s σ2s stats,
                        erased_rsteps (CS:= spec_crash_lang) rs ([es], σs) (t2s, σ2s) stats ∧
                        σ2s.(trace) = σ2.(trace))); eauto.
  { intros Hrecv.
    split.
    - intros ?????. eapply recv_adequate_not_stuck; eauto.
    - intros tr Hobs. destruct Hobs as (?&?&?&Hexec&Htr).
      eapply (recv_adequate_inv _ _ _ _ _ _ _ Hrecv) in Hexec.
      subst. destruct Hexec as (t2s&σ2s&?&Hexecs&Htrs).
      exists (trace σ2s); split; eauto.
      * do 3 eexists; eauto.
      * rewrite Htrs. by exists []; rewrite app_nil_r.
  }
  eapply (heap_recv_adequacy _ _ _ _ _ _ _ _ _ Φinv); auto.
  iIntros (hG Hc) "???".
  iMod (goose_spec_init2 with "[$] [$]") as (HrG) "(#Hspec&Hpool&Hrs&#Htrace)"; try (by symmetry); eauto.
  iMod (Hwp hG Hc HrG with "[$] [$]") as "(#H1&Hwp)".
  iDestruct (source_pool_singleton with "Hpool") as "Hpool".
  iSpecialize ("Hwp" with "[$] [$] [$]"). iFrame.
  iModIntro. iSplit.
  - iModIntro. iIntros (???) "(Hheap_ctx&Hproh_ctx&Hffi_ctx&Htrace_auth&Horacle_auth)".
    iApply (trace_inv_open with "[$] [$] [$] [$]").
  - iModIntro. iIntros (?) "H".
    iDestruct ("H1" with "H") as (?) "(#Hspec_ctx&#Htrace_ctx)".
    iClear "H1". iModIntro.
    iIntros (???) "(Hheap_ctx&Hproh_ctx&Hffi_ctx&Htrace_auth&Horacle_auth)".
    iApply (@trace_inv_open with "[$] [$] [$] [$]").
Qed.

End refinement.

Section refinement_wpc.
Context {ext: ext_op}.
Context {ffi: ffi_model}.
Context {ffi_semantics: ext_semantics ext ffi}.
Context `{interp: !ffi_interp ffi}.
Context `{interp_adeq: !ffi_interp_adequacy}.

Context {spec_ext: spec_ext_op}.
Context {spec_ffi: spec_ffi_model}.
Context {spec_ffi_semantics: spec_ext_semantics spec_ext spec_ffi}.
Context `{spec_interp: @spec_ffi_interp spec_ffi}.
Context `{spec_adeq: !spec_ffi_interp_adequacy}.

Context `{Hhpre: @heapPreG ext ffi ffi_semantics interp _ Σ}.
Context `{Hcpre: @cfgPreG spec_lang Σ}.
Context `{Hrpre: @refinement_heapPreG spec_ext spec_ffi spec_interp _ spec_adeq Σ}.

Existing Instances spec_ffi_model_field spec_ext_op_field spec_ext_semantics_field spec_ffi_interp_field
         spec_ffi_interp_adequacy_field.


(* This is the core triple that must be proved. There are then two scenarios
   where it has to be shown to hold: from an initial state, and from post-crash
   (assuming Φc on the previous generation) *)

Definition wpc_obligation k E e es Φ Φc (hG: heapG Σ) (hC: crashG Σ) (hRG: refinement_heapG Σ) : iProp Σ :=
     (O ⤇ es -∗ spec_ctx -∗ trace_ctx -∗ WPC e @ NotStuck; k; E; (⊤ ∖ ↑sN) {{ Φ hG hC hRG }} {{ Φc hG hC hRG }})%I.

Implicit Types initP: @state ext ffi → @state (spec_ext_op_field) (spec_ffi_model_field) → Prop.

Definition wpc_init k E e es Φ Φc initP : iProp Σ :=
  (∀ (hG: heapG Σ) (hC: crashG Σ) (hRG: refinement_heapG Σ) σ σs,
      ⌜ initP σ σs ⌝ →
      ffi_start (heapG_ffiG) σ.(world) -∗
      ffi_start (refinement_spec_ffiG) σs.(world) -∗
      wpc_obligation k E e es Φ Φc hG hC hRG)%I.

(* XXX: ffi_restart seems unnecessary, given ffi_crash_rel *)
(* This is very complicated to allow the choice of simulated spec crash step
   to be able to depend on what state the impl crashed to. If spec crah steps
   or impl crash steps are deterministic, there is probably a much simpler defn. *)
Definition wpc_post_crash k E e es Φ Φc : iProp Σ :=
  (∀ (hG: heapG Σ) (hC: crashG Σ) (hRG: refinement_heapG Σ),
      Φc hG hC hRG -∗ ▷ ∀ (hG': heapG Σ), |={⊤}=>
      ∀ (hC': crashG Σ) σs,
      (∃ σ0 σ1, ffi_restart (heapG_ffiG) σ1.(world) ∗
      ffi_crash_rel Σ (heapG_ffiG (hG := hG)) σ0.(world) (heapG_ffiG (hG := hG')) σ1.(world)) -∗
      ffi_ctx (refinement_spec_ffiG) σs.(world) -∗
      ∃ σs' (HCRASH: crash_prim_step (spec_crash_lang) σs σs'),
      ffi_ctx (refinement_spec_ffiG) σs.(world) ∗
      ∀ (hRG': refinement_heapG Σ),
      ffi_crash_rel Σ
                      (refinement_spec_ffiG (hRG := hRG)) σs.(world)
                      (refinement_spec_ffiG (hRG := hRG')) σs'.(world) -∗
      ffi_restart (refinement_spec_ffiG) σs'.(world) -∗
      wpc_obligation k E e es Φ Φc hG' hC' hRG')%I.

Lemma difference_difference_remainder_L (E1 E2: coPset) :
  E1 ⊆ E2 → (E2 ∖ (E2 ∖ E1)) = E1.
Proof.
  intros Hsub. rewrite (union_difference_L E1 E2 Hsub). set_solver.
Qed.

Lemma wpc_trace_inv_open k es σs e Hheap Hc Href Φ Φc:
  spec_ctx' es ([es], σs) -∗
  trace_ctx -∗
  WPC e @ k; ⊤;⊤ ∖ ↑sN {{ v, Φ Hheap Hc Href v }}{{Φc Hheap Hc Href}} -∗
  WPC e @ k; ⊤;⊤ {{ _, True }}{{∃ (Hi : invG Σ) (hC : crashG Σ) (hRef : refinement_heapG Σ)
                        (es' : list expr) (σs' : state) (stat : status),
                        ⌜erased_rsteps (CS := spec_crash_lang) es ([es], σs) (es', σs') stat⌝
                        ∗ ⌜crash_safe (CS := spec_crash_lang) es ([es], σs)⌝
                          ∗ ▷ ffi_ctx refinement_spec_ffiG (world σs')
                            ∗ trace_frag (trace σs')
                              ∗ oracle_frag (oracle σs')
                                ∗ Φc (heap_update Σ Hheap Hi (heap_get_names Σ Hheap)) hC hRef}}.
Proof.
  iIntros "#Hspec #Htrace H".
  iApply (@wpc_strong_mono with "H"); eauto.
  iSplit; first eauto.
  iIntros.
  replace (k-k)%nat with O by lia. rewrite //=.
  rewrite difference_difference_remainder_L; last by set_solver.
  iDestruct "Hspec" as "(Hsource&Hstate)".
  iModIntro.
  iInv "Hsource" as ">H" "_".
  iDestruct "H" as (? es' σs') "(H1&H2)".
  iDestruct "H2" as %(Hexec&Hsafe).
  iInv "Hstate" as "Hinterp" "_".
  iDestruct "Hinterp" as (σs'') "(>Hspec_state_frag&Hspec_interp)".
  iDestruct "Hspec_interp" as "(?&?&>Hspec_trace_auth&>Hspec_oracle_auth&?)".
  iInv "Htrace" as ">Htrace_open" "_".
  iDestruct "Htrace_open" as (???? ??) "(Htrace_frag&Hspec_trace_frag&Horacle_frag&Htspec_oracle_frag)".
  iDestruct (source_state_reconcile with "[$] [$]") as %Heq0'.
  iDestruct (trace_agree with "Hspec_trace_auth [$]") as %Heq1'.
  iDestruct (oracle_agree with "Hspec_oracle_auth [$]") as %Heq2'.
  simpl in Hsafe.
  subst. iIntros.
  iMod (fupd_level_intro_mask' _ ∅) as "_".
  { set_solver. }
  do 2 iModIntro.
  iExists _, _, _, _, _, _.
  iSplitR; first by eauto.
  iSplitR; first by eauto.
  rewrite heap_get_update'.
  iFrame.
Qed.

Lemma trace_equiv_preserve_crash σ σ' σs σs':
  trace σs = trace σ →
  crash_prim_step goose_crash_lang σ σ' →
  crash_prim_step spec_crash_lang σs σs' →
  trace σs' = trace σ'.
Proof.
  intros Heq1 Hcrash Hcrash_spec.
  inversion Hcrash; subst.
  inversion Hcrash_spec; subst.
  rewrite //= /add_crash Heq1 //=.
Qed.

Lemma oracle_equiv_preserve_crash σ σ' σs σs':
  oracle σs = oracle σ →
  crash_prim_step goose_crash_lang σ σ' →
  crash_prim_step spec_crash_lang σs σs' →
  oracle σs' = oracle σ'.
Proof.
  intros Heq1 Hcrash Hcrash_spec.
  inversion Hcrash; subst.
  inversion Hcrash_spec; subst.
  rewrite //= Heq1 //=.
Qed.

Definition initP_wf initP :=
  ∀ (σ: @state ext ffi) (σs: @state (@spec_ext_op_field spec_ext) (@spec_ffi_model_field spec_ffi)),
    initP σ σs → null_non_alloc σs.(heap) ∧ ffi_initP σ.(world) ∧ ffi_initP σs.(world).

Theorem heap_wpc_refinement_adequacy `{crashPreG Σ} k es e
        σs σ Φ Φc initP:
  σ.(trace) = σs.(trace) →
  σ.(oracle) = σs.(oracle) →
  initP σ σs →
  initP_wf initP →
  (⊢ wpc_init k ⊤ e es Φ Φc initP) →
  (⊢ wpc_post_crash k ⊤ e es Φ Φc) →
  trace_refines e e σ es es σs.
Proof using Hrpre Hhpre Hcpre.
  Set Printing Implicit.
  intros Heq1 Heq2 Hinit Hinit_wf Hwp_init Hwp_crash.
  eapply heap_recv_refinement_adequacy with
      (k0 := k)
      (φ := λ _, True) (φr := λ _, True)
      (Φinv := λ hG,
               (* (∀  Hheap  (HPF: ∃ Hi' Ht', Hheap = heap_update_pre _ _ Hi' (@pbundleT _ _ Ht') ) *)
               (
                         ∃ Href' : refinement_heapG Σ, spec_ctx' es ([es], σs)
                                                                 ∗ trace_ctx)%I); eauto.
  { eapply Hinit_wf; eauto. }
  { eapply Hinit_wf; eauto. }
  { eapply Hinit_wf; eauto. }
  iIntros (Hheap Hc Href).
  iModIntro. iIntros "#Hspec #Htrace".
  iSplit.
  { iModIntro. iIntros (?) "H". iApply "H". }
  iIntros "Hstart Hstart_spec Hj".
  iApply (recovery_weakestpre.idempotence_wpr _ _ ⊤ ⊤ _ _ (λ _ _, _) _ _ (λ Hi0 t,
   ∃ Hi hC hRef, let hG := heap_update Σ Hheap Hi pbundleT in
                 ∃ es' σs' stat, ⌜ erased_rsteps es ([es], σs) (es', σs') stat ⌝ ∗
                                 ⌜ crash_safe es ([es], σs) ⌝ ∗
                                ▷ ffi_ctx (refinement_spec_ffiG) σs'.(world) ∗
                                trace_frag (trace σs') ∗ oracle_frag (oracle σs')
                (* spec_ctx' es ([es], σs) ∗ trace_ctx *) ∗  Φc hG hC hRef)%I with "[-]")%I.
  { eauto. }
  - rewrite /wpc_init/wpc_obligation in Hwp_init.
    iPoseProof (Hwp_init with "[//] [$] [$] [$] [] [$]") as "H".
    { rewrite /spec_ctx/spec_ctx'.
      iDestruct "Hspec" as "(H1&$)".
      iExists _, _. iFrame "H1".
    }
    rewrite /perennial_irisG. simpl.
    rewrite heap_get_update'.
    iApply (wpc_trace_inv_open with "Hspec Htrace H").
  - iModIntro. iClear "Hspec Htrace".
    iIntros (Hi ?? σ_pre_crash σ_post_crash Hcrash κs ?).
    iIntros "H". iDestruct "H" as (Hi_old ?? es' σs' stat Hexec Hsafe)
                                    "(Hspec_ffi&Htrace_frag&Horacle_frag&HΦc)".
    iIntros "(_&_&Hffi_old&Htrace_auth&Horacle_auth)".
    iDestruct (trace_agree with "Htrace_auth [$]") as %Heq1'.
    iDestruct (oracle_agree with "Horacle_auth [$]") as %Heq2'.
    iModIntro.
    iPoseProof (@Hwp_crash $! _ _ _ with "HΦc") as "H".
    iNext. iIntros.
    iMod (na_heap.na_heap_reinit _ tls σ_post_crash.(heap)) as (name_na_heap) "Hh".
    iMod (proph_map.proph_map_reinit _ κs σ_post_crash.(used_proph_id)) as (name_proph_map) "Hp".
    iMod (ffi_crash _ σ_pre_crash.(world) σ_post_crash.(world) with "Hffi_old") as (ffi_names) "(Hw&Hcrel&Hc)".
    { inversion Hcrash; subst; eauto. }
    iMod (trace_reinit _ σ_post_crash.(trace) σ_post_crash.(oracle)) as (name_trace) "(Htr&Htrfrag&Hor&Hofrag)".
    set (hnames := {| heap_heap_names := name_na_heap;
                      heap_proph_name := name_proph_map;
                      heap_ffi_names := ffi_names;
                      heap_trace_names := name_trace |}).
    set (hG := (heap_update _ _ _ hnames)).
    iMod ("H" $! hG) as "H". iSpecialize ("H" with "[Hc Hcrel] [$]").
    {  simpl. iExists _, _. rewrite ffi_update_update. iFrame. }
    iDestruct "H" as (σs_post_crash Hspec_crash) "(Hspec_ffi&Hwpc)".
    iClear "Htrace_auth Horacle_auth Htrace_frag Horacle_frag".
    iMod (goose_spec_crash_init _ _ σs _ σs' σs_post_crash _ (trace σ_post_crash) (oracle σ_post_crash)
            with "[$] [$] Hspec_ffi") as (HrG) "(#Hspec&Hpool&Hcrash_rel&Hrs&#Htrace)"; eauto.
    { eapply trace_equiv_preserve_crash; eauto. }
    { eapply oracle_equiv_preserve_crash; eauto. }
    iExists ({| pbundleT := hnames |}).
    iModIntro.
    rewrite /state_interp//=.
    rewrite ffi_update_update. iFrame.
    iSplit.
    * iClear "∗". eauto.
    * iDestruct (source_pool_singleton with "Hpool") as "Hpool".
      iDestruct ("Hwpc" with "[$] [$] [$] [] [$]") as "H".
      { rewrite /spec_ctx/spec_ctx'.
        iDestruct "Hspec" as "(H1&$)".
        iExists _, _. iFrame "H1".
      }
      iPoseProof (wpc_trace_inv_open k _ _ e _ Hc' _ Φ Φc with "Hspec Htrace H") as "H".
      rewrite /hG//=.
      rewrite /heap_update/heap_get_names//= ffi_update_update.
      rewrite /traceG_update//=.
      rewrite /gen_heap_names.gen_heapG_update//=.
      rewrite ?ffi_update_get //=.
Qed.

End refinement_wpc.
