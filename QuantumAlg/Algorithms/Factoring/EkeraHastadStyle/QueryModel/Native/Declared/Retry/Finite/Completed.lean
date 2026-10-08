/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Source
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Program
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Context
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout
public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.AllKeys
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Space
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.State.Completed

/-!
# Algorithm contract for independently completed EH batches

The positive execution performs the first completed batch followed by every
requested completed reused batch. Direct source and joint-state laws prove
its observable distribution and complete state requirement. Actual paths
pay the completed-batch event, duration and fixed-storage allowances.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- Positive-count algorithm whose run executes the independently completed
first batch and every later completed batch. -/
public def completedFiniteAlgorithm (input : Input N) (laterCount : Nat) :
    Algorithm (model input) base (context base noQuantum N (laterCount + 1))
      (LatticeBatchRecoveryOutput.OutputShape N) where
  run := Cleanup.completedRun base noQuantum N input laterCount

/-- With no good-key premise, the actual completed algorithm succeeds with
exactly one minus the independent source failure mass to the batch count. -/
theorem completedFiniteAlgorithm_successProbability (input : Input N) (laterCount : Nat)
    {Reference : Register}
    (original : Execution.OracleInput (model input).classicalOracles base Reference) :
    ((completedFiniteAlgorithm base noQuantum input laterCount).run.outputDistribution
      original).toOuterMeasure (AllKeys.accepts N) =
        1 - AllKeys.sourceFailure input ^ (laterCount + 1) := by
  change ((Cleanup.completedRun base noQuantum N input laterCount).outputDistribution
    original).toOuterMeasure (AllKeys.accepts N) = _
  rw [Cleanup.completed_outputDistribution]
  exact AllKeys.sourceDistribution_success input (laterCount + 1)

/-- All surviving classical storage and the complete owned bank remain in the
actual output manifest. -/
theorem completedFiniteAlgorithm_output_listing (input : Input N) (laterCount : Nat) :
    (completedFiniteAlgorithm base noQuantum input laterCount).run.output.listing =
      (context base noQuantum N (laterCount + 1)).keys := rfl

/-- The algorithm consumer uses the completed run's full original
bank/reference state requirement at its actual optional factor readout. -/
theorem completedFiniteAlgorithm_stateRequirement_holds (input : Input N)
    (laterCount : Nat) {Reference : Register}
    (original : Execution.OracleInput (model input).classicalOracles base Reference) :
    (Cleanup.stateRequirement base noQuantum N (laterCount + 1)).Holds original.caller
      ((completedFiniteAlgorithm base noQuantum input laterCount).run.finalState
        Reference original.state) := by
  exact Cleanup.completed_stateRequirement_holds
    base noQuantum N input laterCount original

/-- The completed schedule restores every borrowed role at its actual final
state, including arbitrary external reference and hidden service history. -/
theorem completedFiniteAlgorithm_restoresBorrowed (input : Input N)
    (laterCount : Nat) {Reference : Register}
    (original : Execution.OracleInput (model input).classicalOracles base Reference) :
    (completedFiniteAlgorithm base noQuantum input laterCount).run.RestoresBorrowed
      original := by
  have empty : base.borrowedQuantumWires = [] := by
    have subset := base.borrowedQuantumWires_sublist
    rw [noQuantum] at subset
    exact List.sublist_nil.mp subset
  apply AlgorithmRun.restoresBorrowed_of_circuit
  intro reference history _ state
  exact Circuit.borrowedRestored_of_noBorrowedQuantum
    (completedFiniteAlgorithm base noQuantum input laterCount).run.code
    empty reference state

/-- Every concrete completed path is charged for the first and all later
packing and physical resets. -/
theorem completedFiniteAlgorithm_resourcePool_le (input : Input N) (laterCount : Nat)
    (path : (completedFiniteAlgorithm base noQuantum input laterCount).run.code.Path) :
    (completedFiniteAlgorithm base noQuantum input laterCount).run.code.resourcePool path ≤
      Cleanup.completedEventBudget N input laterCount := by
  exact Cleanup.completed_resourcePool_le base noQuantum N input laterCount path

/-- The actual completed algorithm reuses the original positive-count
resident-space allowance at every path, independently of the batch count. -/
theorem completedFiniteAlgorithm_peakResidentSpace_le (input : Input N)
    (laterCount : Nat)
    (path : (completedFiniteAlgorithm base noQuantum input laterCount).run.code.Path) :
    (completedFiniteAlgorithm base noQuantum input laterCount).run.code.peakResidentSpace
      path ≤ Finite.additionalSpace N (laterCount + 1) + base.residentSpace := by
  exact Cleanup.completed_peakResidentSpace_le
    base noQuantum N input laterCount path

/-- The same actual paths retain all caller auxiliary roles under the fixed
positive-count allowance. -/
theorem completedFiniteAlgorithm_peakAuxiliarySpace_le (input : Input N)
    (laterCount : Nat)
    (path : (completedFiniteAlgorithm base noQuantum input laterCount).run.code.Path) :
    (completedFiniteAlgorithm base noQuantum input laterCount).run.code.peakAuxiliarySpace
      path ≤ Finite.additionalSpace N (laterCount + 1) + base.auxiliarySpace := by
  exact Cleanup.completed_peakAuxiliarySpace_le
    base noQuantum N input laterCount path

/-- Whole-run serial depth follows the same actual completed path. -/
theorem completedFiniteAlgorithm_depth_le (input : Input N) (laterCount : Nat)
    (duration : Resource.Event (model input) → Nat)
    (path : (completedFiniteAlgorithm base noQuantum input laterCount).run.code.Path) :
    (completedFiniteAlgorithm base noQuantum input laterCount).run.code.depth duration path ≤
      Cleanup.completedDurationBudget N input laterCount duration := by
  exact Cleanup.completed_depth_le base noQuantum N input laterCount duration path

/-- The independent all-input source problem with the actual completed-batch
event and serial-depth allowances. Its state and fixed-space requirements are
the original positive-count requirements. -/
public def completedProblem (input : Input N) (laterCount : Nat)
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Problem (model input) base (context base noQuantum N (laterCount + 1))
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  { AllKeys.problem base noQuantum input (laterCount + 1) duration unitQueries with
    resources :=
      { events := Cleanup.completedEventBudget N input laterCount
        resident := Finite.additionalSpace N (laterCount + 1) + base.residentSpace
        auxiliary := Finite.additionalSpace N (laterCount + 1) + base.auxiliarySpace }
    depth :=
      { duration := duration
        limit := Cleanup.completedDurationBudget N input laterCount duration
        classicalQuery_unit := fun coordinate => nomatch coordinate
        quantumQuery_unit := unitQueries } }

private theorem completed_relationalProbability (input : Input N) (laterCount : Nat)
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    {Reference : Register}
    (original : Execution.OracleInput (model input).classicalOracles base Reference) :
    ((completedFiniteAlgorithm base noQuantum input laterCount).relationalDistribution
      original).toOuterMeasure
        {pair | (completedProblem base noQuantum input laterCount duration unitQueries).accepts
          pair.1 pair.2} =
      1 - AllKeys.sourceFailure input ^ (laterCount + 1) := by
  have projection :
      ((completedFiniteAlgorithm base noQuantum input laterCount).relationalDistribution
        original).toOuterMeasure
          {pair | (completedProblem base noQuantum input laterCount duration unitQueries).accepts
            pair.1 pair.2} =
        ((completedFiniteAlgorithm base noQuantum input laterCount).run.outputDistribution
          original).toOuterMeasure (AllKeys.accepts N) := by
    simp only [Algorithm.relationalDistribution, completedProblem, AllKeys.problem,
      AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
      PMF.toOuterMeasure_map_apply]
    rfl
  exact projection.trans
    (completedFiniteAlgorithm_successProbability base noQuantum input laterCount original)

/-- For every original input and positive batch count, the actual independently
completed algorithm meets the all-input source law, full state, restoration,
event, fixed-space and serial-depth obligations on its own execution. -/
public theorem completedFiniteAlgorithm_solves (input : Input N) (laterCount : Nat)
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Algorithm.Solves (completedFiniteAlgorithm base noQuantum input laterCount)
      (completedProblem base noQuantum input laterCount duration unitQueries) := by
  constructor
  · intro Reference original _valid _initialized
    exact le_of_eq
      (completed_relationalProbability base noQuantum input laterCount duration
        unitQueries original).symm
  · intro Reference original _valid _initialized requirement present
    have same : requirement = Cleanup.stateRequirement base noQuantum N (laterCount + 1) :=
      List.mem_singleton.mp present
    subst requirement
    exact completedFiniteAlgorithm_stateRequirement_holds
      base noQuantum input laterCount original
  · intro Reference original _valid _initialized
    exact completedFiniteAlgorithm_restoresBorrowed
      base noQuantum input laterCount original
  · intro _Reference _original _valid _initialized path _supported
    exact completedFiniteAlgorithm_resourcePool_le base noQuantum input laterCount path
  · intro _Reference _original _valid _initialized path _supported
    exact completedFiniteAlgorithm_peakResidentSpace_le
      base noQuantum input laterCount path
  · intro _Reference _original _valid _initialized path _supported
    exact completedFiniteAlgorithm_peakAuxiliarySpace_le
      base noQuantum input laterCount path
  · intro _Reference _original _valid _initialized path _supported
    exact completedFiniteAlgorithm_depth_le
      base noQuantum input laterCount duration path

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
