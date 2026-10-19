/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Round.Distribution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Probability

/-!
# Original one-attempt success after real complete feedback

An existing sound success survives every later source outcome. An absent
latch admits the original good-source event, including the total even-modulus
branch. The actual full-reference transition transfers that unchanged floor
to complete sampling, recovery, feedback and physical reset.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The original rational one-attempt floor is a valid probability threshold. -/
lemma honestFloor_le_one {N : Nat} (input : Input N) :
    Probability.honestAttemptSuccessFloor N ≤ 1 := by
  change ENNReal.ofReal ((1 : ℝ) / (sourceSuccessDenominator N : ℝ)) ≤ 1
  apply ENNReal.ofReal_le_one.mpr
  have denominatorPositive : 0 < sourceSuccessDenominator N :=
    Nat.mul_pos (by norm_num) input.modulusBits_pos
  have oneLe : (1 : ℝ) ≤ (sourceSuccessDenominator N : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt denominatorPositive
  exact (div_le_one (lt_of_lt_of_le zero_lt_one oneLe)).mpr oneLe

private lemma declared_firstPresent {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (old later : CShape.Value (.option (.unsignedWord (modulusBits N))))
    (sound : SoundLatch model old) (declared : Probability.ReturnedDeclaredFactor model later) :
    Probability.ReturnedDeclaredFactor model (NativeFactorScan.firstPresent old later) := by
  cases old with
  | optionNone => exact declared
  | optionSome word => exact sound.resolve_right (fun impossible => by cases impossible)

/-- Original source success survives chronological selection with any sound incoming latch. -/
lemma completionKernel_success_floor {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (old : CShape.Value (.option (.unsignedWord (modulusBits N)))) (sound : SoundLatch model old) :
    Probability.honestAttemptSuccessFloor N ≤
      (completionKernel (Probability.Input.ofSemiprimeModel model) old).toOuterMeasure
        {value | Probability.ReturnedDeclaredFactor model value} := by
  classical
  let input := Probability.Input.ofSemiprimeModel model
  let accepted : Set (CShape.Value (.option (.unsignedWord (modulusBits N)))) :=
    {value | Probability.ReturnedDeclaredFactor model value}
  let select := fun outcome =>
    NativeFactorScan.firstPresent old (NativeFactorScan.sourceResult input outcome)
  change Probability.honestAttemptSuccessFloor N ≤
    ((sourceOutcomePMF input).map select).toOuterMeasure accepted
  rw [PMF.toOuterMeasure_map_apply]
  by_cases even : Even N
  · have every (outcome : SourceOutcome N) : select outcome ∈ accepted := by
      have complete := NativeFactorScan.sourceResults_of_even model even outcome []
      have single : NativeFactorScan.sourceResults input [outcome] =
          NativeFactorScan.sourceResult input outcome := by
        change NativeFactorScan.firstPresent (NativeFactorScan.sourceResult input outcome)
          .optionNone = _
        cases NativeFactorScan.sourceResult input outcome <;> rfl
      rw [single] at complete
      exact declared_firstPresent model old _ sound complete
    have total : (sourceOutcomePMF input).toOuterMeasure (select ⁻¹' accepted) = 1 :=
      (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (fun outcome _ => every outcome)
    rw [total]
    exact honestFloor_le_one input
  · refine (Probability.honestAttemptSuccessFloor_le_goodOutcomeProbability model even).trans ?_
    apply MeasureTheory.measure_mono
    intro outcome good
    exact declared_firstPresent model old _ sound (NativeFactorScan.sourceResult_good
      model outcome good)

/-- The full real round attains the original floor from every independently admitted sound input. -/
lemma Completion.latch_success (ctx : RuntimeCtx .quantum) {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (sameWires : ctx.quantumWires = (layout N).wires) (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (separated : NativeFactorScan.Separated cells result)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference
      ((executionModel N).HiddenState × History))
    (seeded : BasisSeeded.Holds ctx.quantumLayout.zeroLabel state)
    (normalized : state.IsNormalized)
    (admitted : ∀ record, 0 < (state.block record).mass →
      SoundLatch model (NativeFactorScan.latchValue cells record.1)) :
    Probability.honestAttemptSuccessFloor N ≤
      ((((Completion.code ctx N (Probability.Input.ofSemiprimeModel model)
        sameWires cells result).execute
          (environment (Probability.Input.ofSemiprimeModel model)) Reference state).toPMF
          (((Completion.code ctx N (Probability.Input.ofSemiprimeModel model)
            sameWires cells result).execute_mass
              (environment (Probability.Input.ofSemiprimeModel model)) Reference state).trans
                normalized)).map
              (fun entry => NativeFactorScan.latchValue (Completion.cells ctx N cells)
                entry.1)).toOuterMeasure
      {value | Probability.ReturnedDeclaredFactor model value} := by
  classical
  let input := Probability.Input.ofSemiprimeModel model
  rw [Completion.latch_toPMF ctx N input sameWires cells result separated state seeded normalized]
  let distribution := state.toPMF normalized
  let kernel := fun (entry : Store ctx × ((executionModel N).HiddenState × History)) =>
    completionKernel input (NativeFactorScan.latchValue cells entry.1)
  let exceptional := fun (entry : Store ctx × ((executionModel N).HiddenState × History)) =>
    ¬ SoundLatch model (NativeFactorScan.latchValue cells entry.1)
  have inherited := PMF.bind_eventProbability_ge_goodMass_mul distribution kernel exceptional
    (Probability.ReturnedDeclaredFactor model) (Probability.honestAttemptSuccessFloor N)
    (fun entry good => completionKernel_success_floor model _ (not_not.mp good))
  have total : distribution.toOuterMeasure {entry | ¬ exceptional entry} = 1 := by
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro entry present
    exact not_not.mpr (admitted entry
      ((ExecutionState.mem_support_toPMF_iff state normalized entry).mp present))
  simpa only [total, one_mul] using inherited

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
