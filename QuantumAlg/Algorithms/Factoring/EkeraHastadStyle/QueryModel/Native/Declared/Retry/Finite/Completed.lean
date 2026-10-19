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
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.QuantumTime

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
variable {environment : (model N).Environment}

/-- Positive-count algorithm whose run executes the independently completed
first batch and every later completed batch. -/
public def completedFiniteAlgorithm (input : Input N) (laterCount : Nat) :
    Algorithm (model N) base (context base noQuantum N (laterCount + 1))
      (LatticeBatchRecoveryOutput.OutputShape N) where
  run := Cleanup.completedRun base noQuantum N input laterCount

/-- With no good-key premise, the actual completed algorithm succeeds with
exactly one minus the independent source failure mass to the batch count. -/
lemma completedFiniteAlgorithm_successProbability (input : Input N) (laterCount : Nat)
    {Reference : Register}
    (original : Execution.OracleInput (model N).classicalOracles base Reference) :
    ((completedFiniteAlgorithm base noQuantum input laterCount).run.outputDistribution
      (sourceEnvironment input) original).toOuterMeasure (AllKeys.accepts N) =
        1 - AllKeys.sourceFailure input ^ (laterCount + 1) := by
  change ((Cleanup.completedRun base noQuantum N input laterCount).outputDistribution
    (sourceEnvironment input) original).toOuterMeasure (AllKeys.accepts N) = _
  rw [Cleanup.completed_outputDistribution]
  exact AllKeys.sourceDistribution_success input (laterCount + 1)

/-- All surviving classical storage and the complete owned bank remain in the
actual output manifest. -/
lemma completedFiniteAlgorithm_output_listing (input : Input N) (laterCount : Nat) :
    (completedFiniteAlgorithm base noQuantum input laterCount).run.output.listing =
      (context base noQuantum N (laterCount + 1)).keys := rfl

/-- The algorithm consumer uses the completed run's full original
bank/reference state requirement at its actual optional factor readout. -/
lemma completedFiniteAlgorithm_stateRequirement_holds (input : Input N)
    (laterCount : Nat) {Reference : Register}
    (original : Execution.OracleInput (model N).classicalOracles base Reference) :
    (Cleanup.stateRequirement base noQuantum N (laterCount + 1)).Holds original.caller
      ((completedFiniteAlgorithm base noQuantum input laterCount).run.finalState
        (sourceEnvironment input) Reference original.state) := by
  exact Cleanup.completed_stateRequirement_holds
    base noQuantum N input laterCount original

/-- The completed schedule restores every borrowed role at its actual final
state, including arbitrary external reference and hidden service history. -/
lemma completedFiniteAlgorithm_restoresBorrowed (input : Input N)
    (laterCount : Nat) {Reference : Register}
    (original : Execution.OracleInput (model N).classicalOracles base Reference) :
    (completedFiniteAlgorithm base noQuantum input laterCount).run.RestoresBorrowed environment
      original := by
  have empty : base.borrowedQuantumWires = [] := by
    have subset := base.borrowedQuantumWires_sublist
    rw [noQuantum] at subset
    exact List.sublist_nil.mp subset
  apply AlgorithmRun.restoresBorrowed_of_circuit
  intro reference history _ state
  exact Circuit.borrowedRestored_of_noBorrowedQuantum
    (completedFiniteAlgorithm base noQuantum input laterCount).run.code environment
    empty reference state

/-- Every concrete completed path is charged for the first and all later
packing and physical resets. -/
lemma completedFiniteAlgorithm_resourcePool_le (input : Input N) (laterCount : Nat)
    (path : (completedFiniteAlgorithm base noQuantum input laterCount).run.code.Path) :
    (completedFiniteAlgorithm base noQuantum input laterCount).run.code.resourcePool path ≤
      Cleanup.completedEventBudget N laterCount := by
  exact Cleanup.completed_resourcePool_le base noQuantum N input laterCount path

/-- The actual completed algorithm reuses the original positive-count
resident-space allowance at every path, independently of the batch count. -/
lemma completedFiniteAlgorithm_peakResidentSpace_le (input : Input N)
    (laterCount : Nat)
    (path : (completedFiniteAlgorithm base noQuantum input laterCount).run.code.Path) :
    (completedFiniteAlgorithm base noQuantum input laterCount).run.code.peakResidentSpace
      path ≤ Finite.additionalSpace N (laterCount + 1) + base.residentSpace := by
  exact Cleanup.completed_peakResidentSpace_le
    base noQuantum N input laterCount path

/-- The same actual paths retain all caller auxiliary roles under the fixed
positive-count allowance. -/
lemma completedFiniteAlgorithm_peakAuxiliarySpace_le (input : Input N)
    (laterCount : Nat)
    (path : (completedFiniteAlgorithm base noQuantum input laterCount).run.code.Path) :
    (completedFiniteAlgorithm base noQuantum input laterCount).run.code.peakAuxiliarySpace
      path ≤ Finite.additionalSpace N (laterCount + 1) + base.auxiliarySpace := by
  exact Cleanup.completed_peakAuxiliarySpace_le
    base noQuantum N input laterCount path

/-- Whole-run serial depth follows the same actual completed path. -/
lemma completedFiniteAlgorithm_depth_le (input : Input N) (laterCount : Nat)
    (duration : Resource.Event (model N) → Nat)
    (path : (completedFiniteAlgorithm base noQuantum input laterCount).run.code.Path) :
    (completedFiniteAlgorithm base noQuantum input laterCount).run.code.depth duration path ≤
      Cleanup.completedDurationBudget N laterCount duration := by
  exact Cleanup.completed_depth_le base noQuantum N input laterCount duration path

/-- The independent all-input source problem with the actual completed-batch
event and quantum-time allowances. Its state and fixed-space requirements are
the original positive-count requirements. -/
public def completedProblem (input : Input N) (laterCount : Nat) :
    Problem (model N) base (context base noQuantum N (laterCount + 1))
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  { AllKeys.problem base noQuantum input (laterCount + 1) with
    resources :=
      { events := Cleanup.completedEventBudget N laterCount
        resident := Finite.additionalSpace N (laterCount + 1) + base.residentSpace
        auxiliary := Finite.additionalSpace N (laterCount + 1) + base.auxiliarySpace }
    quantumTimeLimit := Cleanup.completedQuantumTimeBudget N laterCount }

private lemma completed_relationalProbability (input : Input N) (laterCount : Nat)
    {Reference : Register}
    (original : Execution.OracleInput (model N).classicalOracles base Reference) :
    ((completedFiniteAlgorithm base noQuantum input laterCount).relationalDistribution
      (sourceEnvironment input) original).toOuterMeasure
        {pair | (completedProblem base noQuantum input laterCount).accepts (sourceEnvironment
          input) () pair.1 pair.2} =
      1 - AllKeys.sourceFailure input ^ (laterCount + 1) := by
  have projection :
      ((completedFiniteAlgorithm base noQuantum input laterCount).relationalDistribution
        (sourceEnvironment input) original).toOuterMeasure
          {pair | (completedProblem base noQuantum input laterCount).accepts (sourceEnvironment
            input) () pair.1 pair.2} =
        ((completedFiniteAlgorithm base noQuantum input laterCount).run.outputDistribution
          (sourceEnvironment input) original).toOuterMeasure (AllKeys.accepts N) := by
    simp only [Algorithm.relationalDistribution, completedProblem, AllKeys.problem,
      AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
      PMF.toOuterMeasure_map_apply]
    rfl
  exact projection.trans
    (completedFiniteAlgorithm_successProbability base noQuantum input laterCount original)

/-- For every original input and positive batch count, the actual independently
completed algorithm meets the all-input source law, full state, restoration,
event, fixed-space and serial-depth obligations on its own execution. -/
public lemma completedFiniteAlgorithm_solves (input : Input N) (laterCount : Nat) :
    Algorithm.Solves (completedFiniteAlgorithm base noQuantum input laterCount)
      (completedProblem base noQuantum input laterCount) := by
  constructor
  · intro environment _witness Reference original valid _initialized
    have same : environment = sourceEnvironment input := valid
    subst environment
    exact le_of_eq
      (completed_relationalProbability base noQuantum input laterCount original).symm
  · intro environment _witness Reference original valid _initialized requirement present
    have sameEnvironment : environment = sourceEnvironment input := valid
    subst environment
    have same : requirement = Cleanup.stateRequirement base noQuantum N (laterCount + 1) :=
      List.mem_singleton.mp present
    subst requirement
    exact completedFiniteAlgorithm_stateRequirement_holds
      base noQuantum input laterCount original
  · intro environment _witness Reference original _valid _initialized
    exact completedFiniteAlgorithm_restoresBorrowed
      base noQuantum input laterCount original
  · intro _environment _witness _Reference _original _valid _initialized path _supported
    exact completedFiniteAlgorithm_resourcePool_le base noQuantum input laterCount path
  · intro _environment _witness _Reference _original _valid _initialized path _supported
    exact completedFiniteAlgorithm_peakResidentSpace_le
      base noQuantum input laterCount path
  · intro _environment _witness _Reference _original _valid _initialized path _supported
    exact completedFiniteAlgorithm_peakAuxiliarySpace_le
      base noQuantum input laterCount path
  · intro _environment _witness _Reference _original _valid _initialized path _supported
    exact Cleanup.declaredCompleted_quantumTime_le
      base noQuantum N input laterCount path

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
