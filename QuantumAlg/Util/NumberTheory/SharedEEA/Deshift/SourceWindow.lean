/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Deshift.Window
import all QuantumAlg.Util.NumberTheory.SharedEEA.PackingBoundary

/-!
# Exact source operand for a complete coefficient deshift comparison

Once quotient consumption has really finished, the first shared word
contains the coefficient, zero quotient region, and the entire Euclidean
remainder [LYL+26, sec_EEA/sub_regshare.tex:16-17,288-298]. The remainder is
strictly below the still-live divisor. Therefore extending the coefficient
comparison to the complete aligned coefficient region reads precisely the
old coefficient with zero high bits; it does not include the remainder.

These are equalities of extracted actual packed bits. The quotient-zero
and field bounds are discharged by the original admissible macro state's
completed coefficient phase. No low-remainder-zero hypothesis is added.
Native placement of this complete comparison remains a separate refinement.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.DeshiftSourceWindow

private lemma read_zero_quotient {coefficientWidth quotientWidth remainderWidth : Nat}
    (payload : WordPacking.Work1Payload coefficientWidth quotientWidth remainderWidth)
    (length : Nat) (coefficientFits : coefficientWidth ≤ length)
    (within : length ≤ (coefficientWidth + 1) + (quotientWidth + remainderWidth))
    (empty : payload.quotientBits.toNat = 0)
    (remainderBelow : payload.remainderBits.toNat <
      2 ^ ((coefficientWidth + 1) + (quotientWidth + remainderWidth) - length)) :
    (PhysicalWindow.read length (WordPacking.packWork1 payload)).toNat =
      payload.coefficientBits.toNat := by
  have coefficientBound : payload.coefficientBits.toNat < 2 ^ length :=
    payload.coefficientBits.isLt.trans_le
      (Nat.pow_le_pow_right Nat.zero_lt_two coefficientFits)
  have word : PhysicalWindow.read length (WordPacking.packWork1 payload) =
      BitVec.ofNatLT payload.coefficientBits.toNat coefficientBound := by
    apply BitVec.eq_of_getLsbD_eq
    intro index selected
    rw [PhysicalWindow.read_bit _ within index selected,
      PackingBoundary.work1_zero_quotient_bit payload empty index (selected.trans_le within)]
    have remainderZero : payload.remainderBits.toNat.testBit
        ((coefficientWidth + 1) + (quotientWidth + remainderWidth) - 1 - index) = false :=
      Nat.testBit_lt_two_pow (remainderBelow.trans_le
        (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
    change (payload.coefficientBits.toNat.testBit index ||
      payload.remainderBits.toNat.testBit
        ((coefficientWidth + 1) + (quotientWidth + remainderWidth) - 1 - index)) =
          payload.coefficientBits.toNat.testBit index
    rw [remainderZero, Bool.or_false]
  exact congrArg (fun value : BitVec length => value.toNat) word

/-- The full completed-phase source window is precisely the original coefficient, zero-extended. -/
lemma read_completed (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size) :
    (PhysicalWindow.read (CoefficientCapacity.work2CoefficientWidth state modulus - shift)
      (WordPacking.packWork1 (CoefficientCapacity.work1Payload state modulus state.quotient.size
        valid conserved))).toNat = state.coefficient := by
  let payload := CoefficientCapacity.work1Payload state modulus state.quotient.size valid conserved
  have complete := CoefficientCapacity.work1_width state modulus state.quotient.size valid conserved
  have secondComplete := CoefficientCapacity.work2_width state modulus valid conserved
  have aligned := DeshiftWindow.source_window_bound state modulus shift
    valid conserved active within
  have empty : payload.quotientBits.toNat = 0 :=
    CoefficientPhase.finish_remaining state.coefficient (CoefficientPhase.start state)
  have remainderBelow : payload.remainderBits.toNat < 2 ^ state.divisor.size :=
    (Nat.mod_lt state.remainder active).trans (Nat.lt_size_self state.divisor)
  exact read_zero_quotient payload
    (CoefficientCapacity.work2CoefficientWidth state modulus - shift)
    (by omega) (by omega) empty
    (remainderBelow.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))

/-- Both actual full windows together give the original integer comparison, including equality. -/
lemma complete_comparison (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size) :
    (PhysicalWindow.read (CoefficientCapacity.work2CoefficientWidth state modulus - shift)
      (WordPacking.packWork1 (CoefficientCapacity.work1Payload state modulus state.quotient.size
        valid conserved))).toNat ≤
      (PhysicalWindow.read (CoefficientCapacity.work2CoefficientWidth state modulus - shift)
        (WordRotation.packRotatedWork2 shift
          (CoefficientCapacity.work2Payload state modulus state.quotient.size
            valid conserved active))).toNat ↔
        state.coefficient * 2 ^ shift ≤ (IterationState.step state).coefficient := by
  rw [read_completed state modulus shift valid conserved active within]
  exact DeshiftWindow.comparison_completed state modulus shift valid conserved active within

end QuantumAlg.NumberTheory.SharedEEA.DeshiftSourceWindow
