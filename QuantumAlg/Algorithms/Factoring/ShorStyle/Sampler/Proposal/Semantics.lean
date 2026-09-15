/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Proposal
import all QuantumAlg.Components.Classical.TerminalDecode.FoldSemantics
import all QuantumAlg.Components.Classical.FirstAccepted.Semantics

/-!
# Complete block equations for actual proposal scanning

These equations compose the genuine decoder, comparison instructions and
stored-condition selector. Every mathematical update records the path of
those same circuits, while retaining every incoming quantum-reference matrix
block. The finite fold follows the original proposal order at every width.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width count : Nat}

/-- The exact store obtained by the four native comparison instructions. -/
def comparisonStore (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (store : Store ctx) : Store ctx :=
  (((store.applyOp (extendOp scratch)).applyOp (positiveOp shared scratch)).applyOp
    (belowOp shared scratch)).applyOp (eligibleOp scratch)

/-- The actual comparison suffix preserves each complete quantum-reference block. -/
theorem proposalComparison_execute (shared : SharedRefs ctx width)
    (scratch : ScratchRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (comparisonBody shared scratch).execute Reference state =
      state.mapClassical (fun entry =>
        (comparisonStore shared scratch entry.1, (entry.2, ((), ((), ((), ())))))) := by
  simp only [comparisonBody, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- The decoder's exact store and path on the addressed packed proposal. -/
def decodedStep (sample : CInputRef ctx (.bits (count * width))) (proposal : Fin count)
    (scratch : ScratchRefs ctx width) (store : Store ctx) :
    Store ctx × (TerminalDecode.intoFromBitRefs .littleEndian
      (PackedSample.proposalRefs sample proposal) scratch.candidate).Path :=
  TerminalDecode.foldStep scratch.candidate
    (List.ofFn (fun index => PackedSample.proposalRefs sample proposal
      (TerminalDecode.sourceIndex .littleEndian index))) store

private theorem decoded_execute (sample : CInputRef ctx (.bits (count * width)))
    (proposal : Fin count) (scratch : ScratchRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (TerminalDecode.intoFromBitRefs .littleEndian
      (PackedSample.proposalRefs sample proposal) scratch.candidate).execute Reference state =
      state.mapClassical (fun entry =>
        ((decodedStep sample proposal scratch entry.1).1,
          (entry.2, (decodedStep sample proposal scratch entry.1).2))) := by
  refine (TerminalDecode.terminalDecode_fold_execute scratch.candidate _ Reference state).trans ?_
  congr 1

/-- The actual decoded proposal and four-instruction suffix with their joint path. -/
def prefixStep (sample : CInputRef ctx (.bits (count * width))) (proposal : Fin count)
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width) (store : Store ctx) :
    Store ctx × (prefixBody sample proposal shared scratch).Path :=
  let decoded := decodedStep sample proposal scratch store
  (comparisonStore shared scratch decoded.1, (decoded.2, ((), ((), ((), ())))))

/-- Prefix execution follows the actual decoder and comparison updates on every block. -/
theorem proposalPrefix_execute (sample : CInputRef ctx (.bits (count * width)))
    (proposal : Fin count) (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (prefixBody sample proposal shared scratch).execute Reference state =
      state.mapClassical (fun entry =>
        ((prefixStep sample proposal shared scratch entry.1).1,
          (entry.2, (prefixStep sample proposal shared scratch entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical _ (comparisonBody shared scratch)
    (decodedStep sample proposal scratch)
    (fun store => (comparisonStore shared scratch store, ((), ((), ((), ())))))
    (decoded_execute sample proposal scratch)
    (fun reference {_} _ initial => by
      refine (proposalComparison_execute shared scratch reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The true proposal-slot store and path, including the selector's stored branch. -/
def slotStep (sample : CInputRef ctx (.bits (count * width))) (proposal : Fin count)
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width) (store : Store ctx) :
    Store ctx × (slot sample proposal shared scratch).Path :=
  let prefixed := prefixStep sample proposal shared scratch store
  let selected := FirstAccepted.step (selectorInputs scratch) shared.selector prefixed.1
  (selected.1, (prefixed.2, selected.2))

/-- One real slot composes the exact prefix and first-accepted state equations. -/
theorem proposalSlot_execute (sample : CInputRef ctx (.bits (count * width)))
    (proposal : Fin count) (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (slot sample proposal shared scratch).execute Reference state =
      state.mapClassical (fun entry =>
        ((slotStep sample proposal shared scratch entry.1).1,
          (entry.2, (slotStep sample proposal shared scratch entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (prefixBody sample proposal shared scratch) _
    (prefixStep sample proposal shared scratch)
    (FirstAccepted.step (selectorInputs scratch) shared.selector)
    (proposalPrefix_execute sample proposal shared scratch)
    (FirstAccepted.firstAccepted_execute (selectorInputs scratch) shared.selector)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Store and real nested path of the ordered finite proposal fold. -/
def foldSteps (sample : CInputRef ctx (.bits (count * width)))
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width) :
    (proposals : List (Fin count)) → Store ctx →
      Store ctx × (foldSlots sample shared scratch proposals).Path
  | [], store => (store, ())
  | proposal :: remaining, store =>
      let selected := slotStep sample proposal shared scratch store
      let later := foldSteps sample shared scratch remaining selected.1
      (later.1, (selected.2, later.2))

/-- Every finite ordered scan has the exact state map of its actual source-addressed slots. -/
theorem proposalFold_execute (sample : CInputRef ctx (.bits (count * width)))
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (proposals : List (Fin count)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (foldSlots sample shared scratch proposals).execute Reference state =
      state.mapClassical (fun entry =>
        ((foldSteps sample shared scratch proposals entry.1).1,
          (entry.2, (foldSteps sample shared scratch proposals entry.1).2))) := by
  induction proposals generalizing Reference History with
  | nil =>
      refine (Circuit.execute_id_mapClassical Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _
  | cons proposal remaining ih =>
      refine (Circuit.execute_seq_mapClassical (slot sample proposal shared scratch)
        (foldSlots sample shared scratch remaining) (slotStep sample proposal shared scratch)
        (foldSteps sample shared scratch remaining)
        (proposalSlot_execute sample proposal shared scratch)
        (fun reference {_} _ initial => ih reference initial) Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal
