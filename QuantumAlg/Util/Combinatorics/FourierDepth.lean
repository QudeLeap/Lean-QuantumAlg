/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Mathlib.Data.Nat.Basic

/-!
# Monotone count of structural Fourier stages

The scalar counts one stage per Hadamard, controlled phase and register-swap
pair in a serial structural Fourier construction. Native decompositions have
their own executed gate and depth ledgers; this count does not identify those
ledgers. The formula and monotonicity include widths zero and one.
-/

namespace QuantumAlg.Combinatorics

/-- Scalar structural-stage count, independent of an execution model or decomposition. -/
public def logicalFourierStageCount (width : Nat) : Nat :=
  width + width * (width - 1) / 2 + width / 2

/-- Enlarging the width cannot decrease the scalar structural-stage count. -/
public theorem logicalFourierStageCount_mono {left right : Nat} (bound : left ≤ right) :
    logicalFourierStageCount left ≤ logicalFourierStageCount right := by
  unfold logicalFourierStageCount
  exact Nat.add_le_add
    (Nat.add_le_add bound
      (Nat.div_le_div_right
        (Nat.mul_le_mul bound (Nat.sub_le_sub_right bound 1))))
    (Nat.div_le_div_right bound)

end QuantumAlg.Combinatorics
