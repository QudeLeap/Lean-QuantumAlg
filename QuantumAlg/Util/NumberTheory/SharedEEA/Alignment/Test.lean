/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Alignment

/-!
# Exact stopping test of the actually shifted alignment loop

The source tests the original remainder against the divisor at its newly
doubled scale [LYL+26, sec_EEA/sub_regshare.tex:275-278]. At bounded actual
positions, the first strict rejection occurs exactly at the quotient's
bit length. Equality still permits alignment to continue.

This is a correctness characterization of the real comparison. The
quotient is not evaluated to initialize a scale register or to replace
the native flag update. The actual first phase begins at scale one and
retains each shift, as in the registered four-phase construction.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.AlignmentTest

/-- The strict full comparison is exactly that the actual quotient lies below the current scale. -/
theorem comparison_iff (dividend divisor shift : Nat) (active : 0 < divisor) :
    dividend < divisor * 2 ^ shift ↔ dividend / divisor < 2 ^ shift := by
  have divided : dividend / divisor < 2 ^ shift ↔ dividend < 2 ^ shift * divisor :=
    Nat.div_lt_iff_lt_mul active
  simpa only [Nat.mul_comm] using divided.symm

/-- Within the real alignment range, rejection occurs precisely at the terminal shift count. -/
theorem comparison_iff_last (state : IterationState) (shift : Nat)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size) :
    state.remainder < state.divisor * 2 ^ shift ↔ shift = state.quotient.size := by
  rw [comparison_iff state.remainder state.divisor shift active]
  change state.quotient < 2 ^ shift ↔ shift = state.quotient.size
  constructor
  · intro below
    have enough := Nat.size_le.mpr below
    omega
  · intro last
    rw [last]
    exact Nat.lt_size_self _

/-- The Boolean stored by the real comparison is the exact bounded terminal-position predicate. -/
theorem decide_comparison (state : IterationState) (shift : Nat)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size) :
    decide (state.remainder < state.divisor * 2 ^ shift) =
      decide (shift = state.quotient.size) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using comparison_iff_last state shift active within

end QuantumAlg.NumberTheory.SharedEEA.AlignmentTest
