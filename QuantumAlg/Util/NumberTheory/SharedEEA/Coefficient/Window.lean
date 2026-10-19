/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Coefficient.Capacity
import all QuantumAlg.Util.NumberTheory.SharedEEA.Signed.Coefficient

/-!
# Actual signed coefficient windows and preserved fractional bits

After the source's circular shift, the left arithmetic window represents
the integer part of `t' / 2^ℓ_s`; the low fractional bits remain at the
other end of the word [LYL+26, sec_EEA/sub_regshare.tex:263-264]. The actual
signed arithmetic acts on exactly `ℓ_t + 1` window bits
[LYL+26, sec_EEA/sub_regshare.tex:288-296].

The existing coefficient microstate supplies both parts. Its invariant
bounds the integer window by the fixed coefficient; the specified width
supplies the signed instruction's addition range. Swapping the actual
quotient bit with the initially zero Sign position, executing the concrete
signed instructions, and reassembling the unchanged low part gives exactly
the existing next coefficient microstate. No divisibility assumption is
made, and the consumed bit is recoverable from the actual updated window.

The source capacity also keeps the entire aligned arithmetic window inside
the coefficient region at every genuine phase position. Exact extraction
and replacement of those physical bits in the rotated packed word remain
a separate placement refinement; no quantum operator or cost is asserted.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.CoefficientWindow

/-- The actual coefficient-phase state after the specified number of source microsteps. -/
abbrev current (state : IterationState) (count : Nat) : CoefficientPhase.State :=
  CoefficientPhase.run state.coefficient count (CoefficientPhase.start state)

/-- The prescribed arithmetic window contains the coefficient's bit length and one guard bit. -/
def width (state : IterationState) : Nat := state.coefficient.size + 1

/-- The actual integer part aligned at the left end of the circularly shifted word. -/
def integerPart (state : IterationState) (count : Nat) : Nat :=
  (current state count).value / (current state count).scale

/-- The actual low part kept at the other end of the rotated word. -/
def fractionPart (state : IterationState) (count : Nat) : Nat :=
  (current state count).value % (current state count).scale

/-- Splitting and reassembling the current coefficient preserves every actual bit contribution. -/
lemma parts_reassemble (state : IterationState) (count : Nat) :
    integerPart state count * (current state count).scale + fractionPart state count =
      (current state count).value := by
  unfold integerPart fractionPart
  rw [Nat.mul_comm]
  exact Nat.div_add_mod _ _

/-- The actual low-part invariant bounds the aligned integer window by the fixed coefficient. -/
lemma integerPart_lt (state : IterationState) (count : Nat) (valid : state.Admissible) :
    integerPart state count < state.coefficient := by
  have below := CoefficientPhase.run_below state.coefficient count (CoefficientPhase.start state)
    (CoefficientPhase.start_below state valid)
  change (current state count).value < (current state count).scale * state.coefficient at below
  have scalePositive : 0 < (current state count).scale := by
    rw [CoefficientCapacity.current_scale]
    exact Nat.two_pow_pos count
  unfold integerPart
  apply (Nat.div_lt_iff_lt_mul scalePositive).mpr
  simpa only [Nat.mul_comm] using below

/-- The source's one extra window bit gives enough room for either actual quotient branch. -/
lemma addition_room (state : IterationState) (count : Nat) (valid : state.Admissible) :
    integerPart state count + state.coefficient < 2 ^ width state := by
  have below := integerPart_lt state count valid
  have coefficientBound := Nat.lt_size_self state.coefficient
  unfold width
  rw [Nat.pow_succ]
  omega

/-- Encode the actual aligned integer window without truncation. -/
def valueWord (state : IterationState) (count : Nat) (valid : state.Admissible) :
    BitVec (width state) :=
  BitVec.ofNatLT (integerPart state count) (by
    have room := addition_room state count valid
    omega)

/-- Encode the fixed coefficient in the same declared arithmetic window. -/
def coefficientWord (state : IterationState) : BitVec (width state) :=
  BitVec.ofNatLT state.coefficient (by
    have coefficientBound := Nat.lt_size_self state.coefficient
    unfold width
    rw [Nat.pow_succ]
    omega)

/-- Swap the quotient bit into Sign, leaving zero at that position, then run signed arithmetic. -/
def instruction (state : IterationState) (count : Nat) (valid : state.Admissible) :
    Bool × BitVec (width state + 1) :=
  let quotientDigit := CoefficientPhase.lowBit (current state count).remaining
  let swapped : Bool × Bool := (quotientDigit, false)
  (swapped.2,
    SignedCoefficient.addBit (valueWord state count valid) (coefficientWord state) swapped.1)

/-- The actual initial swap clears the quotient position and the signed arithmetic clears Sign. -/
lemma instruction_clears (state : IterationState) (count : Nat) (valid : state.Admissible) :
    (instruction state count valid).1 = false ∧ (instruction state count valid).2.msb = false := by
  refine ⟨rfl, ?_⟩
  exact SignedCoefficient.addBit_sign _ _ _ (integerPart_lt state count valid)
    (addition_room state count valid)

/-- The actual signed instruction updates precisely the aligned integer contribution. -/
lemma instruction_low (state : IterationState) (count : Nat) (valid : state.Admissible) :
    ((instruction state count valid).2.setWidth (width state)).toNat =
      integerPart state count +
        if CoefficientPhase.lowBit (current state count).remaining then state.coefficient else 0 :=
  SignedCoefficient.addBit_low _ _ _ (integerPart_lt state count valid)
    (addition_room state count valid)

/-- Reattach the unchanged fractional part to the actual signed-instruction output window. -/
def reassembled (state : IterationState) (count : Nat) (valid : state.Admissible) : Nat :=
  ((instruction state count valid).2.setWidth (width state)).toNat *
    (current state count).scale + fractionPart state count

/-- The signed window update computes exactly the existing next coefficient microstep. -/
lemma reassembled_next (state : IterationState) (count : Nat) (valid : state.Admissible) :
    reassembled state count valid = (current state (count + 1)).value := by
  have assembled := parts_reassemble state count
  unfold reassembled
  rw [instruction_low]
  change (integerPart state count +
      (if CoefficientPhase.lowBit (current state count).remaining then state.coefficient else 0)) *
        (current state count).scale + fractionPart state count =
    (current state count).value +
      if CoefficientPhase.lowBit (current state count).remaining
        then (current state count).scale * state.coefficient else 0
  cases digit : CoefficientPhase.lowBit (current state count).remaining with
  | false => simpa only [Bool.false_eq_true, if_false, Nat.add_zero] using assembled
  | true =>
    simp only [if_true]
    calc
      _ = (integerPart state count * (current state count).scale + fractionPart state count) +
          (current state count).scale * state.coefficient := by ring
      _ = _ := by rw [assembled]

/-- The actual updated window recovers the integer part and the consumed quotient digit. -/
lemma instruction_rewind (state : IterationState) (count : Nat) (valid : state.Admissible) :
    SignedCoefficient.rewind (coefficientWord state)
        ((instruction state count valid).2.setWidth (width state)) =
      (valueWord state count valid, CoefficientPhase.lowBit (current state count).remaining) :=
  SignedCoefficient.rewind_addBit _ _ _ (integerPart_lt state count valid)
    (addition_room state count valid)

/-- The aligned window stays entirely inside the full coefficient region of the shared word. -/
lemma arithmetic_window_fits (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : count ≤ state.quotient.size) :
    count + width state ≤ CoefficientCapacity.work2CoefficientWidth state modulus := by
  have quotientPositive := IterationState.quotient_pos state valid.divisor_lt active
  have macroProduct : state.coefficient * state.remainder ≤ modulus := by
    simpa only [conserved, Nat.mul_comm] using (IterationState.products_le_balance state).1
  have productBound : state.coefficient * state.quotient * state.divisor ≤ modulus := by
    calc
      _ = state.coefficient * (state.quotient * state.divisor) := by ring
      _ ≤ state.coefficient * state.remainder :=
        Nat.mul_le_mul_left _ (Nat.div_mul_le_self state.remainder state.divisor)
      _ ≤ modulus := macroProduct
  have capacity := Capacity.positive_triple_size state.coefficient state.quotient state.divisor
    modulus valid.coefficient_pos quotientPositive active productBound
  unfold width CoefficientCapacity.work2CoefficientWidth
  omega

/-- A real input path with a nonzero fractional part requires no divisibility assumption. -/
lemma nonzero_fraction_actual_step :
    let state := IterationState.step (IterationState.initial 17 (foldInput 17 5).2)
    let valid : state.Admissible := IterationState.step_admissible _
      (folded_initial_admissible 17 5 (by decide) (by decide))
      (foldInput_positive_half 17 5 (by decide) (by decide)).1
    integerPart state 1 = 0 ∧ fractionPart state 1 = 1 ∧
      (instruction state 1 valid).1 = false ∧ (instruction state 1 valid).2.msb = false ∧
      reassembled state 1 valid = 7 ∧ (current state 2).value = 7 := by
  decide

end QuantumAlg.NumberTheory.SharedEEA.CoefficientWindow
