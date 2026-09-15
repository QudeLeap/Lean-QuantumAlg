/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Program
public import QuantumAlg.Core.Execution.State.Requirement

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.State
import all QuantumAlg.Core.Execution.Classical.Support
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Core.Execution.SelectionAll.Reference
import all QuantumAlg.Core.Execution.State.Requirement

/-!
# Complete output state for every finite batch count

Zero batches perform the actual empty-result allocation, preserving the entire
input quantum-reference density. Every positive count retains the original bank
seed jointly with the complete reference through the actual selected output.
Both requirements select all live quantum wires and read the real optional cell.
Impossible output blocks retain their zero mass without conditional division.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

section Empty

variable (base : RuntimeCtx .quantum) (N : Nat)

private theorem zero_outputState {Reference : Register}
    (input : Execution.Input base Reference) :
    ((NativeRetryEmpty.run base N).finalState Reference input.state).mapClassical
        (NativeRetryEmpty.run base N).output.eval =
      input.state.mapClassical
        (fun _ => (.optionNone : (LatticeBatchRecoveryOutput.OutputShape N).Value)) := by
  let record : Store base → (NativeRetryEmpty.run base N).Record := fun store =>
    (store.pushRetained base.canonicalFreshKey (LatticeBatchRecoveryOutput.OutputShape N)
      base.canonicalFreshKey_fresh, (store, ()))
  have actual : (NativeRetryEmpty.run base N).execute Reference input.state =
      input.state.mapClassical record := by
    refine (NativeRetryEmpty.run_execute base N input.state).trans ?_
    congr 1
    exact Subsingleton.elim _ _
  rw [AlgorithmRun.finalState_readout, actual,
    ExecutionState.executionState_mapClassical_comp]
  exact congrArg
    (fun read : Store base → (LatticeBatchRecoveryOutput.OutputShape N).Value =>
      input.state.mapClassical read)
    (funext fun store => NativeRetryEmpty.run_output base N store)

private theorem zero_output_statePromise {Reference : Register}
    (input : Execution.Input base Reference)
    (value : (LatticeBatchRecoveryOutput.OutputShape N).Value) :
    (StatePromise.mixed input.state.quantumMarginal
      ((ExecutionState.quantumMarginal_mass input.state).trans input.normalized)).Holds
      ((((NativeRetryEmpty.run base N).finalState Reference input.state).mapClassical
        (NativeRetryEmpty.run base N).output.eval).block value) := by
  rw [zero_outputState]
  by_cases empty : value = .optionNone
  · subst value
    rw [ExecutionState.executionState_mapClassical_const_block]
    change input.state.quantumMarginal.matrix =
      input.state.quantumMarginal.mass • input.state.quantumMarginal.matrix
    rw [(ExecutionState.quantumMarginal_mass input.state).trans input.normalized]
    simp only [one_smul]
  · have absent :
        (input.state.mapClassical
          (fun _ => (.optionNone : (LatticeBatchRecoveryOutput.OutputShape N).Value))).block value =
            DensityOperator.zero _ := by
      apply DensityOperator.ext
      rw [ExecutionState.mapClassical_block_matrix]
      simp only [Ne.symm empty, if_false, Finset.sum_const_zero, DensityOperator.zero_matrix]
    rw [absent]
    exact StatePromise.holds_zero _

private def zeroStateRequirement : StateRequirement base (NativeRetryEmpty.context base N) :=
  .jointReference Finset.univ
    (.read (.storage (NativeRetryEmpty.resultRef base N).toCStorageRef))
    (fun Reference input _ => .mixed
      (DensityOperator.observeSelectionWithReference
        (NativeRetryEmpty.context base N).quantumLayout Finset.univ Reference
        input.state.quantumMarginal)
      ((DensityOperator.observeSelectionWithReference_mass
        (NativeRetryEmpty.context base N).quantumLayout Finset.univ Reference
        input.state.quantumMarginal).trans
          ((ExecutionState.quantumMarginal_mass input.state).trans input.normalized)))

private theorem zero_stateRequirement_holds {Reference : Register}
    (input : Execution.Input base Reference) :
    (zeroStateRequirement base N).Holds input
      ((NativeRetryEmpty.run base N).finalState Reference input.state) :=
  fun value => StatePromise.mixed_fullSelection
    (NativeRetryEmpty.context base N).quantumLayout Reference input.state.quantumMarginal
    ((ExecutionState.quantumMarginal_mass input.state).trans input.normalized)
    _ (zero_output_statePromise base N input value)

end Empty

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- All actual quantum wires and their complete external reference have an independent target
at the real optional output, for every natural total batch count. -/
public def stateRequirement : (totalRounds : Nat) →
    StateRequirement base (context base noQuantum N totalRounds)
  | 0 => zeroStateRequirement base N
  | count + 1 => NativeRetrySelection.stateRequirement base noQuantum N count

/-- The same actual finite run meets its complete output-state requirement, including zero
batches and impossible optional results, without a caller seed or independence hypothesis. -/
theorem stateRequirement_holds (specification : Input N) (totalRounds : Nat)
    {Reference : Register} (input : Execution.Input base Reference) :
    (stateRequirement base noQuantum N totalRounds).Holds input
      ((run base noQuantum specification totalRounds).finalState Reference input.state) := by
  cases totalRounds with
  | zero => exact zero_stateRequirement_holds base N input
  | succ count =>
      exact NativeRetrySelection.stateRequirement_holds base noQuantum N count specification input

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry
