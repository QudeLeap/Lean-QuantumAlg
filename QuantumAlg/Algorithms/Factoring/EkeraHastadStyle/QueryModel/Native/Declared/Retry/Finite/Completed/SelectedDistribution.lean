/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Distribution.Moments

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Repeated
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Recovery.Success
import all QuantumAlg.Core.Execution.Reference.Probability

/-!
# Source-law support of the retained selector after completed EH batches

The live selector, separately from the packed public factor cell, follows the
independent first-success distribution on every normalized original input.
Any populated selector in the executed output support is a sound factor.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- The actual retained selector, not just the packed result cell, has the
independent source's chronological first-success law after all completed batches. -/
lemma completed_selectedDistribution (laterCount : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model N).HiddenState × History))
    (normalized : state.IsNormalized) :
    (((completedCode base noQuantum N input laterCount).execute (sourceEnvironment input)
      Reference state).toPMF
      (((completedCode base noQuantum N input laterCount).execute_mass (sourceEnvironment input)
        Reference state).trans
        normalized)).map
        (fun record => Optional.selectedValue
          (Retry.selectionRefs base noQuantum N).selection record.1) =
      Optional.Distribution.selectedDistribution
        ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
        (laterCount + 1) := by
  let final := (completedCode base noQuantum N input laterCount).execute (sourceEnvironment
    input) Reference state
  have finalNormalized : final.IsNormalized :=
    ((completedCode base noQuantum N input laterCount).execute_mass (sourceEnvironment input)
      Reference state).trans
      normalized
  apply ExecutionState.toPMF_map_eq_of_referenceFiberSum state final
    normalized finalNormalized
    (fun record => Optional.selectedValue
      (Retry.selectionRefs base noQuantum N).selection record.1)
    (Optional.Distribution.selectedDistribution
      ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
      (laterCount + 1))
  intro selected left right
  let distribution : PMF (LatticeBatchRecoveryOutput.OutputShape N).Value :=
    (sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue
  have selectedMass :
      Optional.Distribution.moment distribution (laterCount + 1) .optionNone
        (fun value => if value = selected then 1 else 0) =
        ((Optional.Distribution.selectedDistribution distribution (laterCount + 1)
          selected).toReal : ℂ) :=
    (Optional.Distribution.moment_selected distribution (laterCount + 1)
      (fun value => if value = selected then 1 else 0)).trans
      (PMF.sum_toReal_indicator _ selected)
  exact (completed_selected_reference base noQuantum N input laterCount state normalized
    (fun value => if value = selected then 1 else 0) left right).trans
    (congrArg (fun scalar : ℂ =>
      ExecutionState.referenceFiberSum state (fun _ _ => scalar) left right)
      selectedMass)

/-- Every populated selector supported after any completed positive execution
is a nontrivial factor, independently of its hidden service and reference. -/
lemma completed_selected_some_sound (laterCount : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model N).HiddenState × History))
    (normalized : state.IsNormalized)
    (word : CShape.Word (modulusBits N))
    (supported : CShape.Value.optionSome word ∈
      ((((completedCode base noQuantum N input laterCount).execute (sourceEnvironment input)
        Reference state).toPMF
        (((completedCode base noQuantum N input laterCount).execute_mass (sourceEnvironment
          input) Reference state).trans
          normalized)).map
          (fun record => Optional.selectedValue
            (Retry.selectionRefs base noQuantum N).selection record.1)).support) :
    word.toNat ∣ N ∧ 1 < word.toNat ∧ word.toNat < N := by
  rw [completed_selectedDistribution base noQuantum N input laterCount state normalized]
    at supported
  have source := Optional.Distribution.selectedDistribution_some_support
    ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
    (laterCount + 1) word supported
  exact Batch.Recovery.sourceOutput_some_sound N input word source

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
