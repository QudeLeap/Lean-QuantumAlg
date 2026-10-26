/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Suffix.Preservation

/-! # Whole-word subtraction by the complete actual reversed suffix increment -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition

noncomputable section

open QuantumAlg.EncodedBit GateSpec

/-- Subtract the actual selected place value, retaining the original addend and control. -/
def suffixReverseWordStep (length : Nat) (state : Registers) : Registers :=
  if state.2 then
    ((state.1.1, ⟨(state.1.2.val + (2 ^ width - 2 ^ (width - length))) % 2 ^ width,
      Nat.mod_lt _ (Nat.two_pow_pos width)⟩), state.2)
  else state

private lemma suffixWordStep_reverseWordStep (length : Nat) (state : Registers) :
    suffixWordStep length (suffixReverseWordStep length state) = state := by
  have placeFits : 2 ^ (width - length) ≤ 2 ^ width :=
    Nat.pow_le_pow_right (by decide) (by omega)
  rcases state with ⟨⟨addend, target⟩, control⟩
  cases control with
  | false => rfl
  | true =>
      apply Prod.ext
      · apply Prod.ext
        · rfl
        · apply Fin.ext
          have inverse := Nat.FixedWidth.ModularSuffix.increment_inverse
            (capacity := 2 ^ width) (place := 2 ^ width - 2 ^ (width - length))
            (Nat.sub_le _ _) target.isLt
          rw [Nat.sub_sub_self placeFits] at inverse
          exact inverse
      · rfl

/-- Reversal includes every original dirty-wire restoration and subtracts the selected place. -/
lemma suffixIncrement_reverse_step (length : Nat) (fits : length ≤ width) (state : Registers) :
    stepList (suffixIncrementGates length fits).reverse state =
      suffixReverseWordStep length state := by
  let before := suffixReverseWordStep length state
  have forward : stepList (suffixIncrementGates length fits) before = state := by
    rw [suffixIncrementGates_step, suffixIncrementStep_eq_wordStep]
    exact suffixWordStep_reverseWordStep length state
  have inverse := stepList_reverse_stepList (suffixIncrementGates length fits) before
  rw [forward] at inverse
  exact inverse

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition
