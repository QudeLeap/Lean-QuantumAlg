/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Reused.Schedule
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Cycle
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.First

/-!
# All-original-input finite schedule of independently completed EH batches

The first completed batch and each further reused batch have separate
input-based protocols and actual paid resets. The schedule indexes the exact
`completedFiniteAlgorithm` circuit, while its independent outcome keeps the
full finite success, state and whole-run resource contract.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- The actual first code supplies the next batch's local selector domain.
The terminal `id` in `completedCode 0` changes only an erased path history. -/
theorem firstCompleted_nextInput_selectedSound {Reference : Register}
    (original : OracleInput (model input).classicalOracles base Reference) :
    selectedSound base noQuantum N input
      ((firstCompletedAlgorithm base noQuantum input).run.code.nextInput
          original).localState := by
  have full := completed_nextInput_selectedSound base noQuantum N input 0 original
  change selectedSound base noQuantum N input
    (((firstCompletedAlgorithm base noQuantum input).run.code.seq
      (Circuit.id (model := model input) (Retry.context base noQuantum N))).nextInput
        original).localState at full
  have same := Circuit.nextInput_seq_identity_state (model := model input)
    (Retry.context base noQuantum N) (firstCompletedAlgorithm base noQuantum input).run.code
      original
  have localSame :
      (((firstCompletedAlgorithm base noQuantum input).run.code.seq
        (Circuit.id (model := model input) (Retry.context base noQuantum N))).nextInput
          original).localState =
        ((firstCompletedAlgorithm base noQuantum input).run.code.nextInput
          original).localState := by
    apply ExecutionState.ext
    intro record
    change DensityOperator.marginalLeft
      ((((firstCompletedAlgorithm base noQuantum input).run.code.seq
        (Circuit.id (model := model input) (Retry.context base noQuantum N))).nextInput
          original).state.block record) =
        DensityOperator.marginalLeft
          (((firstCompletedAlgorithm base noQuantum input).run.code.nextInput
          original).state.block record)
    exact congrArg (fun state => DensityOperator.marginalLeft (state.block record)) same
  rw [localSame] at full
  exact full

/-- The independent caller plan requests one first completed batch followed
by precisely `laterCount` reused completed batches. -/
def completedCyclePlan (laterCount : Nat)
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    CyclePlan (model input) base (Retry.context base noQuantum N)
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  .seq (.cycle (AllKeys.problem base noQuantum input 1 duration unitQueries))
    (laterCompletedCyclePlan base noQuantum N input laterCount duration unitQueries)

/-- The all-input finite success and whole-run state/resource contract,
together with its independently fixed completed-batch plan. -/
def completedCycleProblem (laterCount : Nat)
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    CycleProblem (model input) base (Retry.context base noQuantum N)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  outcome := completedProblem base noQuantum input laterCount duration unitQueries
  plan := completedCyclePlan base noQuantum N input laterCount duration unitQueries

/-- Every actual completed batch is a separate certified cycle on the same
code whose final output obeys the finite source law `1 - q^(laterCount+1)`. -/
def completedCycleCertificate (laterCount : Nat)
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Algorithm.CycleSolves (completedFiniteAlgorithm base noQuantum input laterCount)
      (completedCycleProblem base noQuantum N input laterCount duration unitQueries) where
  correctness := completedFiniteAlgorithm_solves
    base noQuantum input laterCount duration unitQueries
  schedule :=
    .seq ((firstCompletedAlgorithm base noQuantum input).run.code)
      (laterCompletedCode base noQuantum N input laterCount)
      (.complete ((firstCompletedAlgorithm base noQuantum input).run.code)
        { output := (firstCompletedAlgorithm base noQuantum input).run.output
          certified := firstCompletedAlgorithm_solves base noQuantum input duration unitQueries })
      (laterCompletedCycleSchedule base noQuantum N input laterCount
        duration unitQueries)
      (by
        intro Reference original admitted
        cases laterCount with
        | zero => exact ⟨True.intro, True.intro⟩
        | succ count =>
            exact ⟨True.intro,
              firstCompleted_nextInput_selectedSound base noQuantum N input original⟩)
      (Or.inr ⟨firstCompleted_restartCleanup base noQuantum input⟩)
  entry := by
    intro Reference original admitted
    exact ⟨True.intro, True.intro⟩

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
