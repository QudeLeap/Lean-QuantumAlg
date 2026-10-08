/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Mathlib.Data.Nat.Basic

/-!
# Monotonicity of the scalar Fourier unit-depth formula

The formula counts width, a triangular term, and an integer half-width term.
Its monotonicity includes width zero and is independent of a particular
factoring circuit, oracle model, or retry interpreter. Matching an actual
implementation to this scalar formula is a separate obligation.
-/

namespace QuantumAlg.Nat

/-- The structural scalar unit-depth formula at an arbitrary natural width. -/
public def qftUnitDepth (bits : Nat) : Nat := bits + bits * (bits - 1) / 2 + bits / 2

/-- The scalar formula is monotone for every pair of natural widths. -/
public theorem qftUnitDepth_mono {left right : Nat} (bound : left ≤ right) :
    qftUnitDepth left ≤ qftUnitDepth right := by
  unfold qftUnitDepth
  exact Nat.add_le_add
    (Nat.add_le_add bound
      (Nat.div_le_div_right
        (Nat.mul_le_mul bound (Nat.sub_le_sub_right bound 1))))
    (Nat.div_le_div_right bound)

end QuantumAlg.Nat
