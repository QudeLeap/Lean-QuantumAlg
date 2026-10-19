/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import QuantumAlg.Core.Base.Classical.Value
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Recovery.Success
import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Distribution

/-!
# Independent finite source law for declared Ekerå–Håstad factoring

The mathematical first-success distribution retains every source-supported
factor and assigns empty output exactly the independent one-batch failure
mass to the requested count. These statements contain no retry executable.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace AllKeys

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

variable {N : Nat}

/-- Failure of one complete batch under its independently specified source law. -/
def sourceFailure (input : Input N) : ENNReal :=
  sampledBatchOutputPMF input none

/-- Only a recovered and checked nontrivial factor is accepted. -/
def accepts (N : Nat) : Set (LatticeBatchRecoveryOutput.OutputShape N).Value :=
  {output | ∃ word, output = .optionSome word ∧
    word.toNat ∣ N ∧ 1 < word.toNat ∧ word.toNat < N}

/-- Independent chronological selection of the requested source batches. -/
public def sourceDistribution (input : Input N) (count : Nat) :
    PMF (LatticeBatchRecoveryOutput.OutputShape N).Value :=
  Optional.Distribution.selectedDistribution
    ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue) count

/-- Every populated source outcome is a checked nontrivial divisor. -/
lemma sourceDistribution_some_sound (input : Input N) (count : Nat)
    (word : CShape.Word (modulusBits N))
    (supported : CShape.Value.optionSome word ∈ (sourceDistribution input count).support) :
    word.toNat ∣ N ∧ 1 < word.toNat ∧ word.toNat < N := by
  exact Batch.Recovery.sourceOutput_some_sound N input word
    (Optional.Distribution.selectedDistribution_some_support _ count word supported)

/-- The empty source outcome has the exact finite failure power, including zero. -/
lemma sourceDistribution_none (input : Input N) (count : Nat) :
    sourceDistribution input count .optionNone = sourceFailure input ^ count := by
  rw [sourceDistribution, Optional.Distribution.selectedDistribution_none,
    Batch.Recovery.packed_none]
  rfl

/-- Populated source output has the complementary probability at every count. -/
lemma sourceDistribution_populated (input : Input N) (count : Nat) :
    (sourceDistribution input count).toOuterMeasure
      {output | output ≠ CShape.Value.optionNone} = 1 - sourceFailure input ^ count := by
  rw [PMF.eventProbability_eq_one_sub_complement]
  have complement : {output : (LatticeBatchRecoveryOutput.OutputShape N).Value |
      ¬ output ≠ CShape.Value.optionNone} = {CShape.Value.optionNone} := by
    ext output
    simp only [not_not, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  rw [complement, PMF.toOuterMeasure_apply_singleton, sourceDistribution_none]

/-- Sound factors exhaust the populated support of the independent source law. -/
lemma sourceDistribution_success (input : Input N) (count : Nat) :
    (sourceDistribution input count).toOuterMeasure (accepts N) =
      1 - sourceFailure input ^ count := by
  calc
    _ = (sourceDistribution input count).toOuterMeasure
        {output | output ≠ CShape.Value.optionNone} := by
      apply PMF.toOuterMeasure_apply_eq_of_inter_support_eq
      ext output
      simp only [Set.mem_inter_iff]
      apply and_congr_left
      intro supported
      cases output with
      | optionNone => simp [accepts]
      | optionSome word =>
          have sound := sourceDistribution_some_sound input count word supported
          constructor
          · intro _ impossible
            cases impossible
          · intro _
            exact ⟨word, rfl, sound.1, sound.2.1, sound.2.2⟩
    _ = _ := sourceDistribution_populated input count

end

end AllKeys
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
