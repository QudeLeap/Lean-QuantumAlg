/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Reused.Distribution

/-!
# Accepted factors in a physically reused EH batch

The independent one-batch source succeeds with exactly one minus its empty
mass. Retaining an already sound factor can only improve that probability.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- The independent recovered source assigns accepted factors exactly the
complement of its empty outcome, for every original modulus. -/
lemma reused_sourceSuccess :
    (((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue).toOuterMeasure
      (AllKeys.accepts N)) = 1 - AllKeys.sourceFailure input := by
  let source : PMF (LatticeBatchRecoveryOutput.OutputShape N).Value :=
    (sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue
  have accepted (output : (LatticeBatchRecoveryOutput.OutputShape N).Value)
      (supported : output ∈ source.support) :
      output ∈ AllKeys.accepts N ↔ output ≠ CShape.Value.optionNone := by
    cases output with
    | optionNone => simp [AllKeys.accepts]
    | optionSome word =>
        have sound := Batch.Recovery.sourceOutput_some_sound N input word supported
        constructor
        · intro _ impossible
          cases impossible
        · intro _
          exact ⟨word, rfl, sound.1, sound.2.1, sound.2.2⟩
  calc
    source.toOuterMeasure (AllKeys.accepts N) =
        source.toOuterMeasure {output | output ≠ CShape.Value.optionNone} := by
          apply PMF.toOuterMeasure_apply_eq_of_inter_support_eq
          ext output
          simp only [Set.mem_inter_iff]
          apply and_congr_left
          intro supported
          exact accepted output supported
    _ = 1 - AllKeys.sourceFailure input := by
          rw [PMF.eventProbability_eq_one_sub_complement]
          have complement : {output : (LatticeBatchRecoveryOutput.OutputShape N).Value |
              ¬ output ≠ CShape.Value.optionNone} = {CShape.Value.optionNone} := by
            ext output
            simp only [not_not, Set.mem_ofPred_eq, Set.mem_singleton_iff]
          rw [complement, PMF.toOuterMeasure_apply_singleton]
          exact congrArg (fun mass : ENNReal => 1 - mass)
            (Batch.Recovery.packed_none input)

private lemma retain_accepted_floor {width : Nat}
    (source : PMF (CShape.option (.unsignedWord width)).Value)
    (accepted : Set (CShape.option (.unsignedWord width)).Value) (floor : ENNReal)
    (previous : (CShape.option (.unsignedWord width)).Value)
    (sourceBound : floor ≤ source.toOuterMeasure accepted)
    (priorAccepted : ∀ word, previous = .optionSome word →
      CShape.Value.optionSome word ∈ accepted) (unitBound : floor ≤ 1) :
    floor ≤ (source.map (Optional.retainValue previous)).toOuterMeasure accepted := by
  cases previous with
  | optionNone =>
      have retainNone :
          Optional.retainValue
            (CShape.Value.optionNone : (CShape.option (.unsignedWord width)).Value) = id := by
        funext value
        rfl
      rw [retainNone, PMF.map_id]
      exact sourceBound
  | optionSome word =>
      have retained : Optional.retainValue (CShape.Value.optionSome word) =
          Function.const _ (CShape.Value.optionSome word) := by
        funext value
        rfl
      rw [retained, PMF.map_const, PMF.toOuterMeasure_pure_apply]
      simpa only [if_pos (priorAccepted word rfl)] using unitBound

/-- A previously empty selector has the independent source success mass;
a populated sound selector remains accepted with probability one. -/
lemma reused_retainSuccess
    (previous : (LatticeBatchRecoveryOutput.OutputShape N).Value)
    (sound : ∀ word, previous = .optionSome word →
      word.toNat ∣ N ∧ 1 < word.toNat ∧ word.toNat < N) :
    1 - AllKeys.sourceFailure input ≤
      (((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue).map
        (Optional.retainValue previous)).toOuterMeasure (AllKeys.accepts N) := by
  refine retain_accepted_floor
    ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
    (AllKeys.accepts N) (1 - AllKeys.sourceFailure input) previous
    (reused_sourceSuccess N input).ge ?_ ?_
  · intro word selected
    have factor := sound word selected
    exact ⟨word, rfl, factor.1, factor.2.1, factor.2.2⟩
  · exact (tsub_le_self : (1 : ENNReal) - AllKeys.sourceFailure input ≤ 1)

set_option maxHeartbeats 600000 in
-- Checking the actual run output against the finite conditional bind needs
-- more elaboration work after the circuit and PMF lemmas have been isolated.
/-- For every admitted correlated caller/service/reference input, the actual
paid reused batch meets its independent one-batch factoring success floor. -/
lemma nextCompletedRun_successProbability {Reference : Register}
    (original : OracleInput (model N).classicalOracles
      (Retry.context base noQuantum N) Reference)
    (admitted : selectedSound base noQuantum N original.localState) :
    1 - AllKeys.sourceFailure input ≤
      ((nextCompletedRun base noQuantum N input).outputDistribution (sourceEnvironment input)
        original).toOuterMeasure
        (AllKeys.accepts N) := by
  let distribution := original.state.toPMF original.normalized
  let source : PMF (LatticeBatchRecoveryOutput.OutputShape N).Value :=
    (sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue
  let kernel (entry : Store (Retry.context base noQuantum N) ×
      (model N).HiddenState) :=
    source.map (Optional.retainValue
      (Optional.selectedValue (Retry.selectionRefs base noQuantum N).selection entry.1))
  have goodMass : distribution.toOuterMeasure
      {entry | ¬ entry ∉ distribution.support} = 1 := by
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).2
    intro entry supported
    exact not_not.mpr supported
  have branch (entry : Store (Retry.context base noQuantum N) ×
      (model N).HiddenState)
      (supported : ¬ entry ∉ distribution.support) :
      1 - AllKeys.sourceFailure input ≤
        (kernel entry).toOuterMeasure (AllKeys.accepts N) := by
    have positive : 0 < (original.state.block entry).mass :=
      (ExecutionState.mem_support_toPMF_iff original.state original.normalized entry).1
        (not_not.mp supported)
    have localPositive : 0 < (original.localState.block entry).mass := by
      simpa only [OracleInput.oracleInput_localState_block,
        DensityOperator.marginalLeft_mass] using positive
    have sound (word : CShape.Word (modulusBits N))
        (selected : Optional.selectedValue
          (Retry.selectionRefs base noQuantum N).selection entry.1 = .optionSome word) :
        word.toNat ∣ N ∧ 1 < word.toNat ∧ word.toNat < N :=
      admitted entry word localPositive selected
    exact reused_retainSuccess N input
      (Optional.selectedValue (Retry.selectionRefs base noQuantum N).selection entry.1)
      sound
  have bound := PMF.bind_eventProbability_ge_goodMass_mul distribution kernel
    (fun entry => entry ∉ distribution.support)
    (fun output => output ∈ AllKeys.accepts N)
    (1 - AllKeys.sourceFailure input) branch
  rw [nextCompletedRun_outputDistribution base noQuantum N input original]
  change 1 - AllKeys.sourceFailure input ≤
    (distribution.bind kernel).toOuterMeasure
      {output | output ∈ AllKeys.accepts N}
  simpa only [goodMass, one_mul] using bound

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
