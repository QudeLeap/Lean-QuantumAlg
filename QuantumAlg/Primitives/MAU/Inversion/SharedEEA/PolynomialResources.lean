/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ForwardResources

/-!
# Fixed-degree polynomial envelopes for actual shared-EEA resources

Every exponent in the finite selector and decoder bounds applies only to
the binary length-counter width. The elementary inequalities below replace
these powers by fixed-degree polynomials in the actual input width, including
width zero. Consequently the already proved native event counts have fully
explicit polynomial upper bounds. This is a bound for the implemented gate
lists, not the source's leading-constant estimate
[LYL+26, sec_EEA/sub_opt.tex:37-84; app_proof/sub_stepnum.tex:4-16].

No execution, state, selector, or resource coordinate is changed here.
The polynomial may be deliberately conservative; space and the original
prime positive-residue domain are exactly those of the existing programs.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.PolynomialResources

noncomputable section

private theorem size_le (width : Nat) : width.size ≤ width :=
  Nat.size_le.mpr Nat.lt_two_pow_self

private theorem power_size_le (width : Nat) : 2 ^ width.size ≤ 2 * (width + 1) := by
  by_cases zero : width = 0
  · subst width
    decide
  · exact (SelectionResources.power_size_le width (by omega)).trans (by omega)

private theorem gateCount_le (tail : Nat) : NativePredicate.gateCount tail ≤ 6 * tail + 5 := by
  unfold NativePredicate.gateCount
  split_ifs <;> omega

private theorem increment_le (width : Nat) :
    ShiftResources.incrementCount width ≤ 28 * width := by
  unfold ShiftResources.incrementCount
  omega

private theorem condition_le (width : Nat) :
    NativeControl.conditionCount width ≤ 18 * width + 10 := by
  have first := gateCount_le (width.size - 2)
  have second := gateCount_le (2 * width.size - 2)
  have length := size_le width
  unfold NativeControl.conditionCount
  omega

/-- One instruction emits a quartic number of candidates with a linear per-candidate bound. -/
def instruction (width : Nat) : Nat :=
  8 * (2 * (width + 1)) ^ 4 * (20 * (4 * width + 3) + 28 * (width + 3) + 10)

private theorem instruction_le (width : Nat) (operation : ArithmeticInstruction.Instruction) :
    MicrostepResources.instructionBound width operation ≤ instruction width := by
  have length := size_le width
  have source : ArithmeticSelectionLayout.sourceCount width
      (ArithmeticInstruction.includeSign operation) ≤ 4 * width + 3 := by
    have actual := ArithmeticSelectionLayout.sourceCount_bound width
      (ArithmeticInstruction.includeSign operation)
    omega
  have selector : ArithmeticScheduleResources.selectorBound width
      (ArithmeticInstruction.includeSign operation) ≤
        20 * (4 * width + 3) + 28 * (width + 3) + 10 := by
    unfold ArithmeticScheduleResources.selectorBound
    omega
  have exponent : 4 * width.size + 2 +
      (if ArithmeticInstruction.includeSign operation then 1 else 0) ≤ 4 * width.size + 3 := by
    split_ifs <;> omega
  have candidates : 2 ^ (4 * width.size + 2 +
      if ArithmeticInstruction.includeSign operation then 1 else 0) ≤
        8 * (2 * (width + 1)) ^ 4 := by
    calc
      _ ≤ 2 ^ (4 * width.size + 3) := Nat.pow_le_pow_right (by decide) exponent
      _ = 8 * (2 ^ width.size) ^ 4 := by
        rw [Nat.mul_comm 4 width.size, pow_add, pow_mul]
        ring
      _ ≤ _ := Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (power_size_le width) 4)
  exact Nat.mul_le_mul candidates selector

/-- The real dynamic Sign exchange has a quadratic number of candidates and linear gate lists. -/
def signQuotient (width : Nat) : Nat :=
  2 * (2 * (width + 1)) ^ 2 * (32 * width + 21) + 28 * width + 2 * width + 4

private theorem signQuotient_le (width : Nat) :
    MicrostepResources.signQuotientBound width ≤ signQuotient width := by
  have length := size_le width
  have power := power_size_le width
  have increment := (increment_le width.size).trans (Nat.mul_le_mul_left 28 length)
  have candidates : 2 ^ (width.size + (width.size + 1)) ≤
      2 * (2 * (width + 1)) ^ 2 := by
    calc
      _ = 2 * (2 ^ width.size) ^ 2 := by rw [pow_add, pow_succ]; ring
      _ ≤ _ := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left power 2)
  have selected := Nat.mul_le_mul candidates (show 32 * width.size + 21 ≤
    32 * width + 21 by omega)
  unfold MicrostepResources.signQuotientBound signQuotient
  omega

/-- Actual complete length refresh has polynomially many boundary/position/output candidates. -/
def refresh (width : Nat) : Nat :=
  4 * (2 * (width + 1) * ((width + 3) *
    (width * (10 * (width + (width + 3) + 1) + 1))))

private theorem refresh_le (width : Nat) :
    ControlledLengthResources.refreshBound width ≤ refresh width := by
  have length := size_le width
  have predicate : ControlledLengthResources.predicateBound width ≤
      10 * (width + (width + 3) + 1) + 1 := by
    unfold ControlledLengthResources.predicateBound
    omega
  exact Nat.mul_le_mul_left 4 (Nat.mul_le_mul (power_size_le width)
    (Nat.mul_le_mul_left (width + 3) (Nat.mul_le_mul length predicate)))

/-- A polynomial includes every actual boundary predicate, physical swap, and length update. -/
def boundary (width : Nat) : Nat :=
  2 * (72 * width + 27) + 3 * (width + 3) + refresh width + 1

private theorem boundary_le (width : Nat) :
    TerminalBoundaryResources.boundaryBound width ≤ boundary width := by
  have length := size_le width
  have conjunction := gateCount_le (2 * width.size - 2)
  have predicate : TerminalBoundaryResources.predicateBound width ≤ 72 * width + 27 := by
    unfold TerminalBoundaryResources.predicateBound
    omega
  have refreshBound := refresh_le width
  unfold TerminalBoundaryResources.boundaryBound boundary
  omega

/-- Fixed degree five suffices for every native occurrence of one complete actual microstep. -/
def microstep (width : Nat) : Nat :=
  2 * (93 * (width + 2) + 10) + 4 * instruction width + 4 + signQuotient width +
    (2 * (18 * width + 10) + 3) +
    (2 * ((18 * width + 10) + (10 * (width + 2 + width) + 1)) + 2) + boundary width

/-- The original finite enumeration envelope is bounded without a positive-width premise. -/
theorem microstep_le (width : Nat) : MicrostepResources.bound width ≤ microstep width := by
  have length := size_le width
  have increment := increment_le (2 + width.size)
  have shift : ShiftResources.guardedBound width ≤ 93 * (width + 2) + 10 := by
    unfold ShiftResources.guardedBound
    omega
  have subtract := instruction_le width .remainderSubtract
  have addback := instruction_le width .remainderAddback
  have subtractCoefficient := instruction_le width .coefficientSubtract
  have addCoefficient := instruction_le width .coefficientAdd
  have sign := signQuotient_le width
  have condition := condition_le width
  have zero : MicrostepResources.zeroShiftBound width ≤
      2 * ((18 * width + 10) + (10 * (width + 2 + width) + 1)) + 2 := by
    unfold MicrostepResources.zeroShiftBound
    omega
  have last := boundary_le width
  unfold MicrostepResources.bound microstep
  omega

/-- A direct polynomial replaces the logarithmic offset envelope at every word width. -/
def offset (width : Nat) : Nat := width * (39 * width + 1)

private theorem offset_le (width : Nat) :
    Addition.Gidney.constantOffsetEventBound width ≤ offset width := by
  have logarithm : Nat.clog 2 width ≤ width :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
  exact Nat.mul_le_mul_left width (show 39 * Nat.clog 2 width + 1 ≤
    39 * width + 1 by omega)

/-- Actual fixed loading, comparison, folding, and initial length writing have degree-three cost. -/
def initialization (width : Nat) : Nat :=
  offset (1 + (width + 3)) + offset (width + 3) + 1 + 1 +
    (offset (width + 3) + (width + 3)) + width * (width * (12 * width + 2))

private theorem initialization_le (width : Nat) :
    InitializationResources.bound width ≤ initialization width := by
  have high := offset_le (1 + (width + 3))
  have low := offset_le (width + 3)
  have length := Nat.mul_le_mul_left width
    (Nat.mul_le_mul_right (12 * width + 2) (size_le width))
  unfold InitializationResources.bound InitializationResources.lengthBound
    Addition.Gidney.comparisonEventBound Addition.Gidney.biFlipEventBound initialization
  omega

private theorem decoder_le (width : Nat) :
    ClockDecodeResources.count width ≤ 3 * (width + 2) * (8 * (width + 1)) := by
  have power : 2 ^ (width.size + 2) ≤ 8 * (width + 1) := by
    calc
      _ = 2 ^ width.size * 4 := by rw [pow_add]; rfl
      _ ≤ 2 * (width + 1) * 4 := Nat.mul_le_mul_right 4 (power_size_le width)
      _ = _ := by ring
  exact Nat.mul_le_mul_left (3 * (width + 2)) ((Nat.sub_le _ _).trans power)

/-- A closed degree-six polynomial bounds initialization, the fixed schedule, and decoding. -/
def corrected (width : Nat) : Nat :=
  initialization width + 8 * width * microstep width +
    3 * (width + 2) * (8 * (width + 1)) + offset (width + 3) + (width + 3) + 2

/-- The complete corrected forward envelope has this fixed-degree polynomial upper bound. -/
theorem corrected_le (width : Nat) : ForwardResources.correctedBound width ≤ corrected width := by
  have initial := initialization_le width
  have repeated := Nat.mul_le_mul (show 4 * (2 * width - 1) ≤ 8 * width by omega)
    (microstep_le width)
  have decoder := decoder_le width
  have correction := offset_le (width + 3)
  unfold ForwardResources.correctedBound Addition.Gidney.biFlipEventBound corrected
  omega

/-- The in-place consumer includes polynomial loading, physical output swaps, and unload. -/
def inPlace (width : Nat) : Nat :=
  width + 3 + corrected width + 3 * (width + 3) + width + 3

/-- The separate XOR target includes two complete corrected passes and its actual n-bit copy. -/
def xor (width : Nat) : Nat := 2 * corrected width + width

/-- Actual in-place native event count is polynomial on the unchanged original prime domain. -/
theorem inPlace_count (modulus : Nat) (prime : Nat.Prime modulus) :
    (InPlaceForward.program modulus prime.one_lt).eventCost.card ≤ inPlace modulus.size := by
  have actual := ForwardResources.inPlace_count modulus prime.one_lt
  have corrected := corrected_le modulus.size
  have divided := Nat.div_le_self (modulus.size + 3) 2
  unfold ForwardResources.inPlaceBound inPlace at *
  omega

/-- Actual standalone native event count is polynomial, including complete reversible cleanup. -/
theorem xor_count (modulus : Nat) (prime : Nat.Prime modulus) :
    (NativeInverse.program modulus prime.one_lt).eventCost.card ≤ xor modulus.size :=
  (ForwardResources.xor_count modulus prime.one_lt).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (corrected_le modulus.size)) modulus.size)

end

end QuantumAlg.MAU.Inversion.SharedEEA.PolynomialResources
