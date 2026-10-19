/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Geometric failure bounds with real targets

The natural ceiling of a signed logarithm ratio permits zero repetitions at
target one. This is a numerical lemma independent of an execution model.
-/

namespace QuantumAlg.RealLog

/-- The direct logarithmic ceiling attains any positive real geometric target. -/
public lemma pow_natCeil_logRatio_le {failure target : Real}
    (positive : 0 < failure) (belowOne : failure < 1) (targetPositive : 0 < target) :
    failure ^ ⌈Real.log target / Real.log failure⌉₊ ≤ target := by
  apply (Real.log_le_log_iff (pow_pos positive _) targetPositive).mp
  rw [Real.log_pow]
  exact (div_le_iff_of_neg (Real.log_neg positive belowOne)).mp (Nat.le_ceil _)

/-- A unit failure target selects no repetition, without an artificial positive minimum. -/
public lemma natCeil_logRatio_one (failure : Real) :
    ⌈Real.log 1 / Real.log failure⌉₊ = 0 := by
  simp

/-- A strictly smaller positive target selects at least one repetition. -/
public lemma natCeil_logRatio_pos {failure target : Real}
    (positive : 0 < failure) (belowOne : failure < 1)
    (targetPositive : 0 < target) (targetBelowOne : target < 1) :
    0 < ⌈Real.log target / Real.log failure⌉₊ := by
  exact Nat.ceil_pos.mpr
    (div_pos_of_neg_of_neg (Real.log_neg targetPositive targetBelowOne)
      (Real.log_neg positive belowOne))

end QuantumAlg.RealLog
