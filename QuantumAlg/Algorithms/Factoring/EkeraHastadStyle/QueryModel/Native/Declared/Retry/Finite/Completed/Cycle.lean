/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed
public import QuantumAlg.Core.Execution.CycleSchedule
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.First

/-!
# The first independently completed EH batch as one certified cycle

The first actual sampled, recovered, packed and reset batch solves its own
all-input source problem. Its physical restart certificate supplies the
measured and reinitialized boundary needed before any subsequent cycle.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- One completed physical batch is one complete caller-requested cycle. -/
public def completedOneCycleProblem (input : Input N)
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    CycleProblem (model input) base (context base noQuantum N 1)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  outcome := completedProblem base noQuantum input 0 duration unitQueries
  plan := .cycle (completedProblem base noQuantum input 0 duration unitQueries)

/-- The first completed candidate has an actual complete-cycle schedule,
with its full output state and native resources certified on the same code. -/
public def completedOneCycleCertificate (input : Input N)
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Algorithm.CycleSolves (completedFiniteAlgorithm base noQuantum input 0)
      (completedOneCycleProblem base noQuantum input duration unitQueries) where
  correctness := completedFiniteAlgorithm_solves
    base noQuantum input 0 duration unitQueries
  schedule := .complete (completedFiniteAlgorithm base noQuantum input 0).run.code
    { output := (completedFiniteAlgorithm base noQuantum input 0).run.output
      certified := completedFiniteAlgorithm_solves
        base noQuantum input 0 duration unitQueries }
  entry := fun _ _ admitted => admitted

/-- One completed batch charges its entire actual measurement, recovery,
pack and reset dependency as its complete-cycle depth. -/
theorem completedOneCycleDepth_eq (input : Input N)
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    (clock : Resource.Event (model input) → Nat)
    (path : (completedFiniteAlgorithm base noQuantum input 0).run.code.Path) :
    (completedOneCycleCertificate base noQuantum input duration unitQueries).maximumCycleDepth
      clock path =
        (completedFiniteAlgorithm base noQuantum input 0).run.code.depth clock path := rfl

/-- The first independently certified cycle obeys its complete batch clock
allowance, while the whole-run serial depth remains separately accounted. -/
theorem completedOneCycleDepth_le (input : Input N)
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    (path : (completedFiniteAlgorithm base noQuantum input 0).run.code.Path) :
    (completedOneCycleCertificate base noQuantum input duration unitQueries).maximumCycleDepth
      duration path ≤ Cleanup.completedDurationBudget N input 0 duration := by
  rw [completedOneCycleDepth_eq base noQuantum input duration unitQueries duration path]
  exact completedFiniteAlgorithm_depth_le base noQuantum input 0 duration path

/-- The first completed batch ends with an actual measured, borrowed-restored
and fixed-seed boundary for every original input and external reference. -/
theorem completedOne_restartCleanup (input : Input N) :
    Circuit.RestartCleanup
      (Cleanup.completedCode base noQuantum N input 0) where
  measured := by
    intro path
    have first := firstCompleted_restartCleanup base noQuantum input
    obtain ⟨dimension, present⟩ := first.measured path.1
    exact ⟨dimension, List.mem_append.mpr (Or.inl present)⟩
  restores := by
    intro Reference History _ state
    have empty : base.borrowedQuantumWires = [] := by
      have subset := base.borrowedQuantumWires_sublist
      rw [noQuantum] at subset
      exact List.sublist_nil.mp subset
    exact Circuit.borrowedRestored_of_noBorrowedQuantum
      (Cleanup.completedCode base noQuantum N input 0) empty Reference state
  reinitialized := by
    refine ⟨(Retry.context base noQuantum N).quantumLayout.restrictSelectedBasis
      (Retry.context base noQuantum N).borrowedSelectionᶜ
      (Retry.context base noQuantum N).quantumLayout.zeroLabel, ?_⟩
    intro Reference History _ state label
    exact Cleanup.seeded_recordSeed _ _
      (Cleanup.completed_seeded base noQuantum N input 0 state) label
      (Retry.context base noQuantum N).borrowedSelectionᶜ

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
