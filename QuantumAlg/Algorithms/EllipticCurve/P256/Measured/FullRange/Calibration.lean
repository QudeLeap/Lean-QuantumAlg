/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.DomainParameters
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Full-range P-256 numerical calibration

These arithmetic inequalities calibrate the complete tail and exceptional
error expression.  An actual candidate-floor theorem must separately connect
that expression to the measured execution and nearest decoder.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.FullRange

/-- The full 520-step fixed-seed error is at most one part in five hundred. -/
lemma exceptionalError_le :
    4 * Real.sqrt ((1040 : ℝ) / ((DomainParameters.subgroupOrder - 1 : Nat) : ℝ)) ≤
      1 / 500 := by
  have root : Real.sqrt ((1040 : ℝ) /
      ((DomainParameters.subgroupOrder - 1 : Nat) : ℝ)) ≤ 1 / 2000 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num [DomainParameters.subgroupOrder]
  linarith

/-- The strict two-phase tail, excluded zero character and complete fixed-seed
error leave a single-round lower bound of four fifths. -/
lemma calibratedFloor_ge :
    (4 : ℝ) / 5 ≤ 55 / 64 - 1 / (DomainParameters.subgroupOrder : ℝ) -
      4 * Real.sqrt ((1040 : ℝ) / ((DomainParameters.subgroupOrder - 1 : Nat) : ℝ)) := by
  have error := exceptionalError_le
  have reserve : (4 : ℝ) / 5 ≤ 55 / 64 - 1 / (DomainParameters.subgroupOrder : ℝ) -
      1 / 500 := by norm_num [DomainParameters.subgroupOrder]
  linarith

/-- Three uniform conditional floors of four fifths give the exact rational
failure coefficient one over 125. -/
lemma threeRoundFailure_eq : (1 - (4 : ℝ) / 5) ^ 3 = 1 / 125 := by norm_num

/-- The three-round coefficient is strictly smaller than one percent. -/
lemma threeRoundFailure_lt_onePercent : (1 - (4 : ℝ) / 5) ^ 3 < 1 / 100 := by norm_num

end QuantumAlg.EllipticCurve.P256.Measured.FullRange
