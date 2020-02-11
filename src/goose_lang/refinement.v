From iris.program_logic Require Export language.
From Perennial.Helpers Require Import Transitions.
From Perennial.goose_lang Require Export lang.
From Perennial.goose_lang Require Import tactics notation map lifting.

(* Define the notion of trace refinement *)

Section go_refinement.
  (* Records defining spec language extensions *)
  Context {spec_op: ext_op}.
  Context {spec_ffi: ffi_model}.
  Context {spec_semantics: ext_semantics spec_op spec_ffi}.

  (* Records for the target language *)
  Context {impl_op: ext_op}.
  Context {impl_ffi: ffi_model}.
  Context {impl_semantics: ext_semantics impl_op impl_ffi}.

  Notation sexpr := (@expr spec_op).
  Notation sstate := (@state spec_op spec_ffi).
  Notation iexpr := (@expr impl_op).
  Notation istate := (@state impl_op impl_ffi).

  Canonical Structure spec_lang : language :=
    @heap_lang (spec_op) (spec_ffi) (spec_semantics).
  Canonical Structure spec_crash_lang : crash_semantics spec_lang :=
    @heap_crash_lang (spec_op) (spec_ffi) (spec_semantics).

  Canonical Structure impl_lang : language :=
    @heap_lang (impl_op) (impl_ffi) (impl_semantics).
  Canonical Structure impl_crash_lang : crash_semantics impl_lang :=
    @heap_crash_lang (impl_op) (impl_ffi) (impl_semantics).

  Definition trace_refines (e r: iexpr) (σ: istate) (e' r': sexpr) (σ': sstate) :=
    @crash_safe spec_lang spec_crash_lang r' ([e'], σ') →
    @crash_safe impl_lang impl_crash_lang r ([e], σ) ∧
    (∀ tr, trace_observable e r σ tr → ∃ tr', trace_observable e' r' σ' tr' ∧ trace_prefix tr tr').

End go_refinement.
