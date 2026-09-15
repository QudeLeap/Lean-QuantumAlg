/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Program
import all QuantumAlg.Core.Execution.Retained.Run

/-!
# Actual first-success selection after every requested batch

The actual batch chain runs first. Retained allocation then creates the one
selected-result cell, and the proved optional allocator consumes the original
chronological factor references. The execution record retains every source
block, original caller history and both real circuit paths.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetrySelection

open Execution
open ClassicalRoutines.FirstAccepted.Direct

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {source : RuntimeCtx .quantum} {N length : Nat}

/-- The real optional allocator reads all original factors and packs the selected result. -/
def body (inputs : Fin length → CInputRef source (LatticeBatchRecoveryOutput.OutputShape N)) :
    Circuit (context source N) (context source N) :=
  Optional.Allocation.into (fun index => liftInput source N (inputs index)) (resultRef source N)

/-- This record is supplied by the existing actual three-scope allocator. -/
def bodyStep (inputs : Fin length → CInputRef source (LatticeBatchRecoveryOutput.OutputShape N)) :
    Store (context source N) → Store (context source N) × (body inputs).Path :=
  Optional.Allocation.step (fun index => liftInput source N (inputs index)) (resultRef source N)

private theorem body_execute
    (inputs : Fin length → CInputRef source (LatticeBatchRecoveryOutput.OutputShape N))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context source N) Reference History) :
    (body inputs).execute Reference state = state.mapClassical (fun entry =>
      ((bodyStep inputs entry.1).1, (entry.2, (bodyStep inputs entry.1).2))) :=
  Optional.Allocation.into_execute _ _ Reference state

/-- Retain the selected result before the complete actual optional-selection allocator. -/
def tail (inputs : Fin length → CInputRef source (LatticeBatchRecoveryOutput.OutputShape N)) :
    Circuit source (context source N) :=
  .seq (.retain source (resultKey source) (LatticeBatchRecoveryOutput.OutputShape N)
    source.canonicalFreshKey_fresh) (body inputs)

/-- The complete tail record includes actual retained allocation and every selection path. -/
def step (inputs : Fin length → CInputRef source (LatticeBatchRecoveryOutput.OutputShape N))
    (before : Store source) : Store (context source N) × (tail inputs).Path :=
  let record := bodyStep inputs (before.pushRetained (resultKey source)
    (LatticeBatchRecoveryOutput.OutputShape N) source.canonicalFreshKey_fresh)
  (record.1, ((), record.2))

/-- Real allocation and selection map complete store/history/reference blocks. -/
theorem tail_execute
    (inputs : Fin length → CInputRef source (LatticeBatchRecoveryOutput.OutputShape N)) :
    Circuit.RetainedRecord (tail inputs) (step inputs) := by
  intro Reference History historyFinite state
  have equation := Circuit.execute_retain_seq_mapClassical source (resultKey source)
    (LatticeBatchRecoveryOutput.OutputShape N) source.canonicalFreshKey_fresh
    (body inputs) (bodyStep inputs) (body_execute inputs) Reference state
  unfold tail step
  refine equation.trans ?_
  congr 1
  exact Subsingleton.elim _ _

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- The original complete batch chain precedes selection of its actual chronological factors. -/
def code (input : Input N) (count : Nat) :
    Circuit base (context (NativeRetryChain.context base noQuantum N count) N) :=
  .seq (NativeRetryChain.code base noQuantum input count)
    (tail (NativeRetryChain.resultRefs base noQuantum N count))

/-- Output reads the selected physical cell and manifests every surviving live entry. -/
def run (input : Input N) (count : Nat) :
    AlgorithmRun base (context (NativeRetryChain.context base noQuantum N count) N)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  code := code base noQuantum input count
  output := Output.all (context (NativeRetryChain.context base noQuantum N count) N)
    (.read (.storage (resultRef (NativeRetryChain.context base noQuantum N count) N).toCStorageRef))

/-- Every old live entry and the new selected cell occurs in the complete output manifest. -/
theorem output_listing (input : Input N) (count : Nat) :
    (run base noQuantum input count).output.listing =
      (context (NativeRetryChain.context base noQuantum N count) N).keys := rfl

/-- The real tail appends its path while preserving the original chain record and caller history. -/
def selectionRecord (input : Input N) (count : Nat)
    (record : (NativeRetryChain.run base noQuantum input count).Record) :
    (run base noQuantum input count).Record :=
  let selected := step (NativeRetryChain.resultRefs base noQuantum N count) record.1
  (selected.1, (record.2.1, (record.2.2, selected.2)))

/-- The same original chain execution feeds the complete actual selection tail. -/
theorem code_execute (input : Input N) (count : Nat) :
    Circuit.RetainedTailRecord (NativeRetryChain.code base noQuantum input count)
      (tail (NativeRetryChain.resultRefs base noQuantum N count))
      (step (NativeRetryChain.resultRefs base noQuantum N count)) :=
  Circuit.RetainedRecord.after _ _ _ (tail_execute _)

/-- The actual complete run maps the chain record through the actual retained-tail record. -/
theorem run_execute (input : Input N) (count : Nat) :
    AlgorithmRun.RetainedRecord (NativeRetryChain.run base noQuantum input count)
      (run base noQuantum input count) (selectionRecord base noQuantum input count) := by
  unfold selectionRecord run code
  exact AlgorithmRun.RetainedRecord.ofTail (NativeRetryChain.run base noQuantum input count)
    (tail (NativeRetryChain.resultRefs base noQuantum N count))
    (Output.all (context (NativeRetryChain.context base noQuantum N count) N)
      (.read (.storage
        (resultRef (NativeRetryChain.context base noQuantum N count) N).toCStorageRef)))
    (step (NativeRetryChain.resultRefs base noQuantum N count)) (tail_execute _)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetrySelection
