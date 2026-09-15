/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Capacity
import all QuantumAlg.Util.NumberTheory.SharedEEA.Coefficient.Phase
import all QuantumAlg.Util.NumberTheory.SharedEEA.Word.Rotation

/-!
# Actual coefficient-phase capacity and shared-word encoding

During the source's third phase, the first word stores the fixed coefficient,
the unconsumed quotient suffix, and the completed division remainder. The
second word stores the increasing coefficient and the fixed divisor, with
the actual circular shift count retained
[LYL+26, sec_EEA/sub_regshare.tex:16-20,263-264,288-296].

The bounds below apply to the already defined `CoefficientPhase.run`, not
to hypothetical arithmetic coordinates. The conserved macro cross-sum and
the actual phase total imply the intermediate triple and pair capacities.
Zero quotient suffixes, zero division remainders, and the initial zero
coefficient are included. Exact bounded `BitVec` constructors then encode
both payloads without truncating a natural number.

The first word includes the source's explicit coefficient separator bit.
Both word widths are exactly `modulus.size + 3`. The second word uses the
existing literal circular rotation and its proved decoder. These are
reachable-state encoding laws; whole phase-flag recovery, signed arithmetic
instructions, and a fixed complete iteration schedule are not asserted.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.CoefficientCapacity

private theorem size_div_two (value : Nat) : (value / 2).size = value.size - 1 := by
  by_cases zero : value = 0
  · simp [zero]
  · have bitNonzero : Nat.bit (Nat.bodd value) (Nat.div2 value) ≠ 0 := by
      simpa only [Nat.bit_bodd_div2] using zero
    have sized : value.size = (value / 2).size + 1 := by
      calc
        value.size = (Nat.bit (Nat.bodd value) (Nat.div2 value)).size :=
          congrArg Nat.size (Nat.bit_bodd_div2 value).symm
        _ = Nat.succ (Nat.div2 value).size := Nat.size_bit bitNonzero
        _ = (value / 2).size + 1 := rfl
    omega

/-- Each actual right shift removes precisely one effective quotient digit until zero. -/
theorem size_div_pow_two (value count : Nat) :
    (value / 2 ^ count).size = value.size - count := by
  induction count with
  | zero => simp
  | succ count inductionHypothesis =>
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, size_div_two, inductionHypothesis]
    omega

/-- The source's decreasing quotient-length coordinate is the actual remaining bit length. -/
theorem remaining_size (state : IterationState) (count : Nat) :
    (CoefficientPhase.run state.coefficient count (CoefficientPhase.start state)).remaining.size =
      state.quotient.size - count := by
  rw [CoefficientPhase.run_remaining]
  exact size_div_pow_two state.quotient count

/-- The source's retained circular shift count matches the actual microstep binary scale. -/
theorem current_scale (state : IterationState) (count : Nat) :
    (CoefficientPhase.run state.coefficient count (CoefficientPhase.start state)).scale =
      2 ^ count := by
  simpa only [CoefficientPhase.start, Nat.mul_one] using
    CoefficientPhase.run_scale state.coefficient count (CoefficientPhase.start state)

/-- No intermediate coefficient exceeds the actual next macro coefficient. -/
theorem value_le_next (state : IterationState) (count : Nat) :
    (CoefficientPhase.run state.coefficient count (CoefficientPhase.start state)).value ≤
      (IterationState.step state).coefficient := by
  have conserved := CoefficientPhase.run_total state.coefficient count
    (CoefficientPhase.start state)
  have targetTotal : CoefficientPhase.total state.coefficient (CoefficientPhase.start state) =
      (IterationState.step state).coefficient := by
    change state.previousCoefficient + state.quotient * 1 * state.coefficient =
      state.previousCoefficient + state.coefficient * state.quotient
    ring
  rw [targetTotal] at conserved
  unfold CoefficientPhase.total at conserved
  omega

private theorem clamped_product (coefficient quotient remainder modulus : Nat)
    (coefficientPositive : 0 < coefficient) (coefficientBound : coefficient ≤ modulus)
    (quotientProduct : coefficient * quotient ≤ modulus)
    (remainderProduct : coefficient * remainder ≤ modulus)
    (tripleProduct : coefficient * quotient * remainder ≤ modulus) :
    max coefficient 1 * max quotient 1 * max remainder 1 ≤ modulus := by
  rw [max_eq_left (show 1 ≤ coefficient by omega)]
  by_cases quotientPositive : 1 ≤ quotient
  · by_cases remainderPositive : 1 ≤ remainder
    · simpa only [max_eq_left quotientPositive, max_eq_left remainderPositive] using
        tripleProduct
    · have remainderZero : remainder = 0 := by omega
      simpa [max_eq_left quotientPositive, remainderZero] using quotientProduct
  · have quotientZero : quotient = 0 := by omega
    by_cases remainderPositive : 1 ≤ remainder
    · simpa [quotientZero, max_eq_left remainderPositive] using remainderProduct
    · have remainderZero : remainder = 0 := by omega
      simpa [quotientZero, remainderZero] using coefficientBound

/-- The actual first-word triple satisfies the product bound even when a factor is zero. -/
theorem work1_clamped_product (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    max state.coefficient 1 *
        max (CoefficientPhase.run state.coefficient count
          (CoefficientPhase.start state)).remaining 1 *
        max (state.remainder % state.divisor) 1 ≤ modulus := by
  let remaining := (CoefficientPhase.run state.coefficient count
    (CoefficientPhase.start state)).remaining
  have suffixBound : remaining ≤ state.quotient := by
    dsimp only [remaining]
    rw [CoefficientPhase.run_remaining]
    exact Nat.div_le_self state.quotient (2 ^ count)
  have quotientBound : state.quotient ≤ state.remainder :=
    Nat.div_le_self state.remainder state.divisor
  have remainderBound : state.remainder % state.divisor ≤ state.remainder :=
    Nat.mod_le state.remainder state.divisor
  have macroProduct : state.coefficient * state.remainder ≤ modulus := by
    simpa only [conserved, Nat.mul_comm] using (IterationState.products_le_balance state).1
  have quotientProduct : state.coefficient * remaining ≤ modulus :=
    (Nat.mul_le_mul_left _ (suffixBound.trans quotientBound)).trans macroProduct
  have remainderProduct : state.coefficient * (state.remainder % state.divisor) ≤ modulus :=
    (Nat.mul_le_mul_left _ remainderBound).trans macroProduct
  have tripleProduct : state.coefficient * remaining *
      (state.remainder % state.divisor) ≤ modulus := by
    by_cases active : 0 < state.divisor
    · have belowDivisor : state.remainder % state.divisor ≤ state.divisor :=
        (Nat.mod_lt _ active).le
      calc
        _ ≤ (state.coefficient * state.quotient) * state.divisor :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ suffixBound) belowDivisor
        _ = state.coefficient * (state.quotient * state.divisor) := by ring
        _ ≤ state.coefficient * state.remainder :=
          Nat.mul_le_mul_left _ (Nat.div_mul_le_self state.remainder state.divisor)
        _ ≤ modulus := macroProduct
    · have divisorZero : state.divisor = 0 := by omega
      have quotientZero : state.quotient = 0 := by simp [IterationState.quotient, divisorZero]
      have suffixZero : remaining = 0 := by omega
      simp [suffixZero]
  exact clamped_product _ _ _ _ valid.coefficient_pos
    (Capacity.iteration_fields_le state modulus valid conserved).2.2.1
    quotientProduct remainderProduct tripleProduct

/-- Every actual first-word triple, including its separator bit, fits the source word. -/
theorem work1_capacity (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    state.coefficient.size + 1 + (state.quotient.size - count) +
        (state.remainder % state.divisor).size ≤ modulus.size + 3 := by
  have capacity := Capacity.triple_size_of_clamped_product state.coefficient
    (CoefficientPhase.run state.coefficient count (CoefficientPhase.start state)).remaining
    (state.remainder % state.divisor) modulus
    (work1_clamped_product state modulus count valid conserved)
  rw [remaining_size] at capacity
  omega

/-- The actual increasing coefficient and fixed divisor fit throughout phase three. -/
theorem work2_capacity (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) :
    (CoefficientPhase.run state.coefficient count (CoefficientPhase.start state)).value.size +
        state.divisor.size ≤ modulus.size + 1 := by
  let next := IterationState.step state
  have nextValid := IterationState.step_admissible state valid active
  have nextConserved := (IterationState.step_balance state).trans conserved
  have fields := Capacity.iteration_fields_le next modulus nextValid nextConserved
  have valueBound := (value_le_next state count).trans fields.2.2.1
  have nextProduct : next.coefficient * state.divisor ≤ modulus := by
    have product := (IterationState.products_le_balance next).1
    rw [nextConserved] at product
    simpa only [next, IterationState.step, Nat.mul_comm] using product
  have productBound := (Nat.mul_le_mul_right state.divisor
    (value_le_next state count)).trans nextProduct
  exact Capacity.pair_size _ _ _ valueBound fields.1 productBound

/-- The literal first-word remainder region after its coefficient, separator, and live quotient. -/
def work1RemainderWidth (state : IterationState) (modulus count : Nat) : Nat :=
  modulus.size + 3 - (state.coefficient.size + 1 + (state.quotient.size - count))

/-- The prescribed source segments occupy exactly the first shared word. -/
theorem work1_width (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    (state.coefficient.size + 1) +
        ((state.quotient.size - count) + work1RemainderWidth state modulus count) =
      modulus.size + 3 := by
  have capacity := work1_capacity state modulus count valid conserved
  unfold work1RemainderWidth
  omega

/-- The actual division remainder fits the region left by the source's live quotient length. -/
theorem remainder_fits (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    state.remainder % state.divisor < 2 ^ work1RemainderWidth state modulus count := by
  apply Nat.size_le.mp
  have capacity := work1_capacity state modulus count valid conserved
  unfold work1RemainderWidth
  omega

/-- Encode all three actual first-word coordinates using proved bounds, without truncation. -/
def work1Payload (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    WordPacking.Work1Payload state.coefficient.size (state.quotient.size - count)
      (work1RemainderWidth state modulus count) where
  coefficientBits := BitVec.ofNatLT state.coefficient (Nat.lt_size_self _)
  quotientBits := BitVec.ofNatLT
    (CoefficientPhase.run state.coefficient count (CoefficientPhase.start state)).remaining
    (Nat.size_le.mp (Nat.le_of_eq (remaining_size state count)))
  remainderBits := BitVec.ofNatLT (state.remainder % state.divisor)
    (remainder_fits state modulus count valid conserved)

/-- Actual encoding and decoding recover the three unbounded arithmetic coordinates exactly. -/
theorem work1_decode (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    let payload := work1Payload state modulus count valid conserved
    let recovered := WordPacking.unpackWork1 (WordPacking.packWork1 payload)
    recovered.coefficientBits.toNat = state.coefficient ∧
      recovered.quotientBits.toNat =
        (CoefficientPhase.run state.coefficient count (CoefficientPhase.start state)).remaining ∧
      recovered.remainderBits.toNat = state.remainder % state.divisor := by
  simp only [WordPacking.unpackWork1_packWork1, work1Payload, BitVec.toNat_ofNatLT,
    and_self]

/-- The coefficient occupies the complete region before the divisor in the unrotated second word. -/
def work2CoefficientWidth (state : IterationState) (modulus : Nat) : Nat :=
  modulus.size + 3 - state.divisor.size

/-- The prescribed second-word regions occupy exactly the source word. -/
theorem work2_width (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    work2CoefficientWidth state modulus + state.divisor.size = modulus.size + 3 := by
  have divisorSize := Nat.size_le_size
    (Capacity.iteration_fields_le state modulus valid conserved).2.1
  unfold work2CoefficientWidth
  omega

/-- Every actual accumulated coefficient fits the full second-word coefficient region. -/
theorem value_fits (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) :
    (CoefficientPhase.run state.coefficient count (CoefficientPhase.start state)).value <
      2 ^ work2CoefficientWidth state modulus := by
  apply Nat.size_le.mp
  have capacity := work2_capacity state modulus count valid conserved active
  unfold work2CoefficientWidth
  omega

/-- Encode the actual growing coefficient beside its divisor before circular rotation. -/
def work2Payload (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) :
    WordPacking.Work2Payload (work2CoefficientWidth state modulus) state.divisor.size where
  coefficientBits := BitVec.ofNatLT
    (CoefficientPhase.run state.coefficient count (CoefficientPhase.start state)).value
    (value_fits state modulus count valid conserved active)
  remainderBits := BitVec.ofNatLT state.divisor (Nat.lt_size_self _)

/-- Undoing the actual retained circular shift recovers both second-word coordinates exactly. -/
theorem rotated_work2_decode (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) :
    let payload := work2Payload state modulus count valid conserved active
    let recovered := WordRotation.unpackRotatedWork2 count
      (WordRotation.packRotatedWork2 count payload)
    recovered.coefficientBits.toNat =
        (CoefficientPhase.run state.coefficient count (CoefficientPhase.start state)).value ∧
      recovered.remainderBits.toNat = state.divisor := by
  simp only [WordRotation.unpackRotatedWork2_packRotatedWork2, work2Payload,
    BitVec.toNat_ofNatLT, and_self]

/-- The original input fold supplies both intermediate capacities without extra domain premises. -/
theorem folded_capacities (modulus input count : Nat)
    (positive : 0 < input) (bounded : input < modulus) :
    let state := IterationState.initial modulus (foldInput modulus input).2
    state.coefficient.size + 1 + (state.quotient.size - count) +
          (state.remainder % state.divisor).size ≤ modulus.size + 3 ∧
      (CoefficientPhase.run state.coefficient count (CoefficientPhase.start state)).value.size +
          state.divisor.size ≤ modulus.size + 1 := by
  have valid := folded_initial_admissible modulus input positive bounded
  have conserved := IterationState.initial_balance modulus (foldInput modulus input).2
  have active := (foldInput_positive_half modulus input positive bounded).1
  exact ⟨work1_capacity _ _ _ valid conserved, work2_capacity _ _ _ valid conserved active⟩

end QuantumAlg.NumberTheory.SharedEEA.CoefficientCapacity
