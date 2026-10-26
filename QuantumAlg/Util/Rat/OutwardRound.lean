/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.NormNum

/-!
# Outward rational rounding to a fixed dyadic grid

Reducing interval endpoints to 64 fractional bits keeps subsequent exact
arithmetic compact without ever shrinking the interval.
-/

@[expose] public section

namespace QuantumAlg.RationalBounds

/-- Round down to a multiple of `2⁻⁶⁴`. -/
def roundDown (q : ℚ) : ℚ := (⌊q * 2 ^ 64⌋ : ℚ) / 2 ^ 64

/-- An outward upper endpoint on the same grid, including exact grid inputs. -/
def roundUp (q : ℚ) : ℚ := ((⌊q * 2 ^ 64⌋ : ℚ) + 1) / 2 ^ 64

lemma roundDown_le (q : ℚ) : roundDown q ≤ q := by
  unfold roundDown
  exact (div_le_iff₀ (by positivity)).mpr (Int.floor_le _)

lemma le_roundUp (q : ℚ) : q ≤ roundUp q := by
  unfold roundUp
  exact (le_div_iff₀ (by positivity)).mpr (Int.lt_floor_add_one _).le

end QuantumAlg.RationalBounds
