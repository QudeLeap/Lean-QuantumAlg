/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Transition
import all QuantumAlg.Util.PMF.FiniteWeights

/-!
# Actual EH retry transition over optional factors

The physical source, complete recovery and paid selector compose into the
original optional factor distribution. This is a consequence of the actual
source law and deterministic decoder, not an additional sampler premise.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- One actual later retry updates the previous selected factor with a fresh
factor from the complete decoded physical-batch distribution. -/
lemma next_factor_reference
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference
      ((model N).HiddenState × History))
    (normalized : state.IsNormalized)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((next base noQuantum N input).execute (sourceEnvironment input) Reference state)
      (fun entry _ => weight
        (Optional.selectedValue (selectionRefs base noQuantum N).selection entry.1))
      left right =
    ExecutionState.referenceFiberSum state
      (fun entry _ => ∑ factor : (LatticeBatchRecoveryOutput.OutputShape N).Value,
        ((((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
          factor).toReal : ℂ) *
          weight (Optional.retainValue
            (Optional.selectedValue (selectionRefs base noQuantum N).selection entry.1)
            factor))
      left right := by
  refine (next_selected_reference base noQuantum N input state normalized
    weight left right).trans ?_
  apply congrArg
    (fun observe : (Store (context base noQuantum N) ×
        ((model N).HiddenState × History)) →
        (context base noQuantum N).register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observe left right)
  funext entry basis
  have pushed := PMF.sum_map_toReal_mul
    (Batch.sourceDistribution input) (Batch.SourceRecovery.packedValue (N := N))
    (fun factor => weight (Optional.retainValue
      (Optional.selectedValue (selectionRefs base noQuantum N).selection entry.1)
      factor))
  rw [Batch.SourceRecovery.sourceDistribution_map_packedValue input] at pushed
  exact pushed.symm

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry
