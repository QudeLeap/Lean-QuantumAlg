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
lemma firstCompleted_nextInput_selectedSound {Reference : Register}
    (original : OracleInput (model N).classicalOracles base Reference) :
    selectedSound base noQuantum N
      ((firstCompletedAlgorithm base noQuantum input).run.code.nextInput (sourceEnvironment
        input) original).localState := by
  have full := completed_nextInput_selectedSound base noQuantum N input 0 original
  change selectedSound base noQuantum N
    (((firstCompletedAlgorithm base noQuantum input).run.code.seq
      (Circuit.id (model := model N) (Retry.context base noQuantum N))).nextInput
        (sourceEnvironment input) original).localState at full
  have same := Circuit.nextInput_seq_identity_state (model := model N)
    (Retry.context base noQuantum N) (firstCompletedAlgorithm base noQuantum input).run.code
      (sourceEnvironment input)
      original
  have localSame :
      (((firstCompletedAlgorithm base noQuantum input).run.code.seq
        (Circuit.id (model := model N) (Retry.context base noQuantum N))).nextInput
          (sourceEnvironment input) original).localState =
        ((firstCompletedAlgorithm base noQuantum input).run.code.nextInput (sourceEnvironment
          input) original).localState := by
    apply ExecutionState.ext
    intro record
    change DensityOperator.marginalLeft
      ((((firstCompletedAlgorithm base noQuantum input).run.code.seq
        (Circuit.id (model := model N) (Retry.context base noQuantum N))).nextInput
          (sourceEnvironment input) original).state.block record) =
        DensityOperator.marginalLeft
          (((firstCompletedAlgorithm base noQuantum input).run.code.nextInput (sourceEnvironment
            input) original).state.block record)
    exact congrArg (fun state => DensityOperator.marginalLeft (state.block record)) same
  rw [localSame] at full
  exact full

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
