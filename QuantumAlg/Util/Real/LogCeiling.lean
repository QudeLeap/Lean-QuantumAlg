/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import all Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Integer widths selected by real logarithms

Rounding a positive scale up before taking the integer ceiling logarithm
selects exactly the natural ceiling of the real logarithm.
-/

namespace QuantumAlg.RealLog

/-- Integer ceiling-log selection agrees with the natural ceiling of the real logarithm. -/
public lemma clog_ceil_eq_natCeil_logb {base : Nat} (large : 1 < base)
    {scale : Real} (positive : 0 < scale) :
    Nat.clog base ⌈scale⌉₊ = ⌈Real.logb base scale⌉₊ := by
  apply eq_of_forall_ge_iff
  intro width
  rw [Nat.clog_le_iff_le_pow large, Nat.ceil_le, Nat.ceil_le,
    Real.logb_le_iff_le_rpow (by exact_mod_cast large) positive,
    Real.rpow_natCast, Nat.cast_pow]

end QuantumAlg.RealLog
