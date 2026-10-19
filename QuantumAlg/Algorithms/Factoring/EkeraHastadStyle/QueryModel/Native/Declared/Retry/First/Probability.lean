/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.First
import all QuantumAlg.Util.PMF.FiniteWeights

/-!
# First complete physical EH attempt

The actual selector accepts the first paid batch recovery. Its candidate law
is the decoded batch distribution, including correlations with the caller and
an arbitrary external reference.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- The first actual batch and selector produce exactly one recovered factor. -/
lemma first_factor_reference
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model N).HiddenState × History))
    (normalized : state.IsNormalized)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((first base noQuantum N input).execute (sourceEnvironment input) Reference state)
      (fun entry _ => weight
        (Optional.selectedValue (selectionRefs base noQuantum N).selection entry.1))
      left right =
    ExecutionState.referenceFiberSum state
      (fun _ _ => ∑ factor : (LatticeBatchRecoveryOutput.OutputShape N).Value,
        ((((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
          factor).toReal : ℂ) * weight factor)
      left right := by
  refine (first_selected_reference base noQuantum N input state normalized
    weight left right).trans ?_
  apply congrArg
    (fun scalar : ℂ => ExecutionState.referenceFiberSum state (fun _ _ => scalar) left right)
  have pushed := PMF.sum_map_toReal_mul
    (Batch.sourceDistribution input) (Batch.SourceRecovery.packedValue (N := N)) weight
  rw [Batch.SourceRecovery.sourceDistribution_map_packedValue input] at pushed
  exact pushed.symm

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry
