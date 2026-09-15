/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Seed
import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Resources
import all QuantumAlg.Core.Execution.Borrowed.Preservation

/-!
# First-success values and complete actual execution maps

The mathematical result folds the original chronological optional values
from an empty seed. The proof relates it to the actual retained write while
preserving every original source read and arbitrary quantum-reference block.
Distribution equalities map the same actual chain, without an independent
sampling law or additional probabilistic assumption.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetrySelection

open Execution
open ClassicalRoutines.FirstAccepted.Direct

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {source : RuntimeCtx .quantum} {N length : Nat}

/-- The original chronological option values select their first populated entry. -/
def firstValue
    (values : (CShape.fixedVector length (LatticeBatchRecoveryOutput.OutputShape N)).Value) :
    (LatticeBatchRecoveryOutput.OutputShape N).Value :=
  (List.ofFn (fun index => values.get index)).foldl Optional.retainValue .optionNone

/-- The complete actual tail differs from retained allocation by exactly the selected write. -/
theorem tail_store
    (inputs : Fin length → CInputRef source (LatticeBatchRecoveryOutput.OutputShape N))
    (before : Store source) :
    (step inputs before).1 =
      (before.pushRetained (resultKey source) (LatticeBatchRecoveryOutput.OutputShape N)
        source.canonicalFreshKey_fresh).write (resultRef source N)
          (firstValue (before.read (.fixedVector inputs))) := by
  have actual := Optional.Allocation.into_store
    (fun index => liftInput source N (inputs index)) (resultRef source N)
    (before.pushRetained (resultKey source) (LatticeBatchRecoveryOutput.OutputShape N)
      source.canonicalFreshKey_fresh)
  have reads : (fun index =>
      (before.pushRetained (resultKey source) (LatticeBatchRecoveryOutput.OutputShape N)
        source.canonicalFreshKey_fresh).read (liftInput source N (inputs index))) =
      (fun index => before.read (inputs index)) :=
    funext (fun index => Store.read_pushRetained_underRetained before _ _ _ (inputs index))
  unfold Optional.Allocation.value at actual
  rw [reads] at actual
  exact actual

/-- The selected physical output is exactly the first success in the original source order. -/
theorem tail_output
    (inputs : Fin length → CInputRef source (LatticeBatchRecoveryOutput.OutputShape N))
    (before : Store source) :
    (step inputs before).1.read (.storage (resultRef source N).toCStorageRef) =
      firstValue (before.read (.fixedVector inputs)) := by
  rw [tail_store]
  exact Store.read_write_same _ _ _

/-- Every original structural source read survives allocation and the complete selection. -/
theorem tail_callerFrame
    (inputs : Fin length → CInputRef source (LatticeBatchRecoveryOutput.OutputShape N))
    (before : Store source) {shape : CShape} (other : CInputRef source shape) :
    (step inputs before).1.read (liftInput source N other) = before.read other := by
  rw [tail_store]
  exact (Store.read_write_of_not_mem_storageKeys _ _ _ _
    (result_avoids_input source N other)).trans
      (Store.read_pushRetained_underRetained before _ _ _ other)

/-- Complete retained-record preservation keeps the full joint quantum-reference marginal. -/
theorem tail_quantumMarginal
    (inputs : Fin length → CInputRef source (LatticeBatchRecoveryOutput.OutputShape N)) :
    Circuit.RetainedQuantumPreserved (tail inputs) :=
  Circuit.RetainedRecord.quantumPreserved _ _ (tail_execute inputs)

/-- Actual retained allocation and selection restore arbitrary borrowed interfaces jointly. -/
theorem tail_borrowedRestored
    (inputs : Fin length → CInputRef source (LatticeBatchRecoveryOutput.OutputShape N))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State source Reference History) :
    (tail inputs).BorrowedRestored Reference state ((tail inputs).execute Reference state) := by
  unfold tail
  apply Circuit.borrowedRestored_seq
  · exact Circuit.borrowedRestored_retain _ _ _ state
  · exact Optional.Allocation.into_borrowedRestored _ _ Reference _

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- The actual selected output is the structural first-success projection of the chain output. -/
theorem run_output (input : Input N) (count : Nat)
    (before : Store (NativeRetryChain.context base noQuantum N count)) :
    (run base noQuantum input count).output.eval
        (step (NativeRetryChain.resultRefs base noQuantum N count) before).1 =
      firstValue ((NativeRetryChain.run base noQuantum input count).output.eval before) :=
  tail_output _ before

/-- Selection preserves the actual chain's complete outgoing quantum-reference marginal. -/
theorem code_quantumMarginal (input : Input N) (count : Nat) :
    Circuit.RetainedTailQuantumPreserved (NativeRetryChain.code base noQuantum input count)
      (tail (NativeRetryChain.resultRefs base noQuantum N count)) :=
  Circuit.RetainedTailRecord.quantumPreserved _ _ _ (code_execute base noQuantum input count)

/-- The same actual chain and its selection tail restore the borrowed interface jointly. -/
theorem code_borrowedRestored (input : Input N) (count : Nat) (Reference : Register)
    {History : Type} [Fintype History] (state : State base Reference History) :
    (code base noQuantum input count).BorrowedRestored Reference state
      ((code base noQuantum input count).execute Reference state) := by
  unfold code
  apply Circuit.borrowedRestored_seq
  · exact NativeRetryChain.code_borrowedRestored base noQuantum input count Reference state
  · exact tail_borrowedRestored _ Reference _

/-- Actual complete record probabilities are the deterministic real selection-record map. -/
theorem executionDistribution (specification : Input N) (count : Nat)
    {Reference : Register} (input : Execution.Input base Reference) :
    (run base noQuantum specification count).executionDistribution input =
      ((NativeRetryChain.run base noQuantum specification count).executionDistribution input).map
        (selectionRecord base noQuantum specification count) := by
  have actual : (run base noQuantum specification count).executionDistribution input =
      (((NativeRetryChain.run base noQuantum specification count).execute
        Reference input.state).mapClassical (D := (run base noQuantum specification count).Record)
          (selectionRecord base noQuantum specification count)).toPMF
            (ExecutionState.mapClassical_normalized _
              ((NativeRetryChain.run base noQuantum specification count).execute_normalized input)
              (selectionRecord base noQuantum specification count)) := by
    apply PMF.ext
    intro record
    exact congrArg
      (fun state : ExecutionState (run base noQuantum specification count).Record
          (Register.prod (context (NativeRetryChain.context base noQuantum N count) N).register
            Reference) => ENNReal.ofReal (state.block record).mass)
      (run_execute base noQuantum specification count Reference input.state)
  exact actual.trans (ExecutionState.toPMF_mapClassical _
    ((NativeRetryChain.run base noQuantum specification count).execute_normalized input)
    (selectionRecord base noQuantum specification count))

/-- The selected output law is the first-success map of the same actual chain output law. -/
theorem outputDistribution (specification : Input N) (count : Nat)
    {Reference : Register} (input : Execution.Input base Reference) :
    (run base noQuantum specification count).outputDistribution input =
      ((NativeRetryChain.run base noQuantum specification count).outputDistribution input).map
        (firstValue (N := N)) := by
  have projected : (run base noQuantum specification count).result ∘
      selectionRecord base noQuantum specification count =
      firstValue ∘ (NativeRetryChain.run base noQuantum specification count).result := by
    funext record
    exact run_output base noQuantum specification count record.1
  unfold AlgorithmRun.outputDistribution
  rw [executionDistribution, PMF.map_comp, projected]
  exact (PMF.map_comp (NativeRetryChain.run base noQuantum specification count).result
    ((NativeRetryChain.run base noQuantum specification count).executionDistribution input)
    (firstValue (N := N))).symm

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetrySelection
