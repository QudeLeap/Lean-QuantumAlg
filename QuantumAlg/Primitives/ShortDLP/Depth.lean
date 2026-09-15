/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP

/-!
# Monotonicity of the source QFT depth formula

This scalar property depends only on the number of exponent-register wires.
It is independent of a factoring implementation or its retry interpreter.
-/

namespace QuantumAlg.ShortDLP

/-- The structural QFT unit-depth formula is monotone in register width. -/
theorem qftUnitDepth_mono {left right : Nat} (bound : left ≤ right) :
    qftUnitDepth left ≤ qftUnitDepth right := by
  unfold qftUnitDepth
  exact Nat.add_le_add
    (Nat.add_le_add bound
      (Nat.div_le_div_right
        (Nat.mul_le_mul bound (Nat.sub_le_sub_right bound 1))))
    (Nat.div_le_div_right bound)

end QuantumAlg.ShortDLP
