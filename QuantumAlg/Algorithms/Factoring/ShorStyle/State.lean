/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Distribution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Batch.Prepared.State
import all QuantumAlg.Core.Execution.Classical.Support
import all QuantumAlg.Core.Execution.SelectionAll.Reference
import all QuantumAlg.Core.Execution.State.Requirement

/-!
# Complete Shor output states after actual factor recovery

Every factor output groups the actual supported sampling records through the
real classical recovery code. Their common restored bank seed and complete
incoming reference density survive that grouping. The independent target
conditions on the actual final factor cell and selects every live quantum
wire; it neither drops failed outputs nor normalizes an impossible branch.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeEndpoint

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The independent source seed uses the unchanged actual bank coordinates after recovery. -/
def restoredSeed (N count : Nat) : (post N count).register.Index :=
  NativePreparedBatch.restoredSeed pre pre_quantumWires N count

/-- The joint target fixes the original bank seed and retains the full incoming reference. -/
def stateTarget (N count : Nat) {Reference : Register} (input : Execution.Input pre Reference) :
    DensityOperator (Register.prod (post N count).register Reference) :=
  BasisReference.target (restoredSeed N count) input.state.referenceMarginal

theorem stateTarget_normalized (N count : Nat) {Reference : Register}
    (input : Execution.Input pre Reference) : (stateTarget N count input).IsNormalized :=
  BasisReference.target_normalized (restoredSeed N count) input.state.referenceMarginal
    ((ExecutionState.referenceMarginal_mass input.state).trans input.normalized)

private theorem sampled_statePromise {N : Nat} (source : Input N) (count : Nat)
    {Reference : Register} (input : Execution.Input pre Reference)
    (value : (CShape.fixedVector count (NativeIteration.resultShape N)).Value) :
    (StatePromise.mixed (stateTarget N count input)
      (stateTarget_normalized N count input)).Holds
        ((ExecutionState.mapClassical
          ((NativePreparedBatch.run pre pre_quantumWires N count).execute Reference input.state)
          (NativePreparedBatch.run pre pre_quantumWires N count).result).block value) := by
  let entered : State pre Reference (Store pre) :=
    input.state.mapClassical (fun store => (store, store))
  have referenceSame : entered.referenceMarginal = input.state.referenceMarginal := by
    exact congrArg (fun density : DensityOperator (Register.prod pre.register Reference) =>
      DensityOperator.marginalLeft (density.reindex
        (S := Register.prod Reference pre.register)
        (Equiv.prodComm pre.register.Index Reference.Index)))
      (ExecutionState.mapClassical_quantumMarginal input.state (fun store => (store, store)))
  have actual := NativePreparedBatch.output_statePromise pre pre_quantumWires N count
    source entered ((input.state.mapClassical_mass _).trans input.normalized) value
  dsimp only [StatePromise.Holds] at actual
  rw [referenceSame] at actual
  exact actual

/-- Actual final factor blocks group the same complete sampling blocks by their source result. -/
theorem outputState_eq_recovery {N : Nat} (source : Input N) (count : Nat)
    {Reference : Register} (input : Execution.Input pre Reference) :
    ((run source count).finalState Reference input.state).mapClassical
      (run source count).output.eval =
        ExecutionState.mapClassical
          (ExecutionState.mapClassical
            ((NativePreparedBatch.run pre pre_quantumWires N count).execute Reference input.state)
            (NativePreparedBatch.run pre pre_quantumWires N count).result)
          (recoveredValue source count) := by
  let sampling := NativePreparedBatch.run pre pre_quantumWires N count
  let sampled := sampling.execute Reference input.state
  have actual := congrArg
    (fun state : ExecutionState (run source count).Record
      (Register.prod (post N count).register Reference) =>
        state.mapClassical (run source count).result)
    (execute_eq_map source count Reference input.state)
  have recovered := ExecutionState.executionState_mapClassical_comp sampled
    (recoveredRecord source count) (run source count).result
  have grouped := ExecutionState.executionState_mapClassical_comp sampled
    sampling.result (recoveredValue source count)
  have supported := ExecutionState.mapClassical_eq_of_support sampled
    ((run source count).result ∘ recoveredRecord source count)
    (recoveredValue source count ∘ sampling.result) (fun record positive =>
      recoveredRecord_result source count input record
        ((ExecutionState.mem_support_toPMF_iff sampled
          (sampling.execute_normalized input) record).mpr positive))
  exact (AlgorithmRun.finalState_readout (run source count) Reference input.state).trans
    (actual.trans (recovered.trans (supported.trans grouped.symm)))

/-- Every complete actual factor block keeps the original bank and reference target. -/
theorem output_statePromise {N : Nat} (source : Input N) (count : Nat)
    {Reference : Register} (input : Execution.Input pre Reference)
    (value : (outputShape N).Value) :
    (StatePromise.mixed (stateTarget N count input)
      (stateTarget_normalized N count input)).Holds
        ((((run source count).finalState Reference input.state).mapClassical
          (run source count).output.eval).block value) := by
  rw [outputState_eq_recovery source count input]
  exact ExecutionState.mapClassical_mixed _ (recoveredValue source count)
    (stateTarget N count input) (stateTarget_normalized N count input)
    (sampled_statePromise source count input) value

/-- All live wires are observed jointly with the original reference at the actual factor cell. -/
def stateRequirement (N count : Nat) : StateRequirement pre (post N count) :=
  .jointReference Finset.univ (.read (.storage (resultRef N count).toCStorageRef))
    (fun Reference input _ => .mixed
      (DensityOperator.observeSelectionWithReference (post N count).quantumLayout
        Finset.univ Reference (stateTarget N count input))
      ((DensityOperator.observeSelectionWithReference_mass (post N count).quantumLayout
        Finset.univ Reference (stateTarget N count input)).trans
          (stateTarget_normalized N count input)))

/-- The independently specified full joint requirement holds for the same actual native run. -/
theorem stateRequirement_holds {N : Nat} (source : Input N) (count : Nat)
    {Reference : Register} (input : Execution.Input pre Reference) :
    (stateRequirement N count).Holds input ((run source count).finalState Reference input.state) :=
  fun value => StatePromise.mixed_fullSelection (post N count).quantumLayout Reference
    (stateTarget N count input) (stateTarget_normalized N count input) _
    (output_statePromise source count input value)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeEndpoint
