/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Division.Phase
import Mathlib.Tactic.Ring

/-!
# Actual first-phase alignment for the shared EEA

The first phase starts at scale one and doubles it until the shifted
divisor strictly exceeds the dividend [LYL+26, sec_EEA/sub_4phase.tex:6].
Each actual doubling increments the retained shift count, as in
`sec_EEA/sub_regshare.tex:275-278`. The loop below uses only multiplication
by two and the actual comparison. It never initializes from a precomputed
quotient or its bit length.

The dividend's bit length supplies sufficient recursion fuel for every
positive divisor. A stopped loop performs no further doublings; its exact
number is retained in `places`, and reversing that recorded number of
doublings reconstructs the initial alignment state. This is a decoded
variable-length phase specification, not fixed-schedule terminal padding
or a claim about the full reversible phase-control circuit.

Only after constructing and proving the loop do we identify its shift
count with the quotient bit length. Its actual output establishes all
entry conditions of `DivisionPhase`, including the strict bound needed
to handle equality during subsequent conditional subtraction.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.Alignment

/-- The actual aligned scale and its retained source shift count. -/
@[ext]
structure State where
  scale : Nat
  places : Nat
deriving DecidableEq

/-- The source initializes alignment before any doubling. -/
def initial : State := ⟨1, 0⟩

/-- One actual left shift and its associated length increment. -/
def step (state : State) : State := ⟨2 * state.scale, state.places + 1⟩

/-- Undo one recorded left shift and its length increment. -/
def rewind (state : State) : State := ⟨state.scale / 2, state.places - 1⟩

/-- Each actual alignment shift preserves enough state for its exact inverse. -/
theorem rewind_step (state : State) : rewind (step state) = state := by
  apply State.ext
  · exact Nat.mul_div_right state.scale (by decide : 0 < 2)
  · change (state.places + 1) - 1 = state.places
    omega

/-- Stop on the actual source comparison, or perform another actual doubling. -/
def run (dividend divisor : Nat) : Nat → State → State
  | 0, state => state
  | fuel + 1, state =>
    if dividend < state.scale * divisor then state
    else run dividend divisor fuel (step state)

/-- Reverse the exact number of doublings recorded by the source length coordinate. -/
def rewindRun : Nat → State → State
  | 0, state => state
  | count + 1, state => rewind (rewindRun count state)

/-- The scale and source length coordinate remain related by their exact power of two. -/
theorem run_scale (dividend divisor fuel : Nat) (state : State)
    (consistent : state.scale = 2 ^ state.places) :
    (run dividend divisor fuel state).scale = 2 ^ (run dividend divisor fuel state).places := by
  induction fuel generalizing state with
  | zero => exact consistent
  | succ fuel inductionHypothesis =>
    by_cases stopped : dividend < state.scale * divisor
    · simpa only [run, if_pos stopped] using consistent
    · simp only [run, if_neg stopped]
      apply inductionHypothesis
      change 2 * state.scale = 2 ^ (state.places + 1)
      rw [consistent, Nat.pow_succ]
      omega

/-- The retained counter measures actual shifts and never exceeds the supplied fuel. -/
theorem run_places (dividend divisor fuel : Nat) (state : State) :
    state.places ≤ (run dividend divisor fuel state).places ∧
      (run dividend divisor fuel state).places ≤ state.places + fuel := by
  induction fuel generalizing state with
  | zero => simp [run]
  | succ fuel inductionHypothesis =>
    by_cases stopped : dividend < state.scale * divisor
    · simp only [run, if_pos stopped]
      omega
    · simp only [run, if_neg stopped]
      have bounds := inductionHypothesis (step state)
      change state.places + 1 ≤ (run dividend divisor fuel (step state)).places ∧
        (run dividend divisor fuel (step state)).places ≤ (state.places + 1) + fuel at bounds
      omega

/-- Adequate independent doubling fuel guarantees the actual strict stopping comparison. -/
theorem run_stops (dividend divisor fuel : Nat) (state : State)
    (enough : dividend < 2 ^ fuel * state.scale * divisor) :
    dividend < (run dividend divisor fuel state).scale * divisor := by
  induction fuel generalizing state with
  | zero => simpa only [run, Nat.pow_zero, Nat.one_mul] using enough
  | succ fuel inductionHypothesis =>
    by_cases stopped : dividend < state.scale * divisor
    · simpa only [run, if_pos stopped] using stopped
    · simp only [run, if_neg stopped]
      apply inductionHypothesis
      change dividend < 2 ^ fuel * (2 * state.scale) * divisor
      calc
        dividend < 2 ^ (fuel + 1) * state.scale * divisor := enough
        _ = _ := by rw [Nat.pow_succ]; ring

/-- Every performed doubling was required by the preceding source comparison. -/
theorem run_previous_fits (dividend divisor fuel : Nat) (state : State)
    (previous : state.places = 0 ∨ state.scale / 2 * divisor ≤ dividend) :
    (run dividend divisor fuel state).places = 0 ∨
      (run dividend divisor fuel state).scale / 2 * divisor ≤ dividend := by
  induction fuel generalizing state with
  | zero => exact previous
  | succ fuel inductionHypothesis =>
    by_cases stopped : dividend < state.scale * divisor
    · simpa only [run, if_pos stopped] using previous
    · simp only [run, if_neg stopped]
      apply inductionHypothesis
      right
      change (2 * state.scale) / 2 * divisor ≤ dividend
      rw [Nat.mul_div_right _ (by decide : 0 < 2)]
      omega

/-- The actual counter displacement reverses exactly the shifts that were performed. -/
theorem rewindRun_run (dividend divisor fuel : Nat) (state : State) :
    rewindRun ((run dividend divisor fuel state).places - state.places)
      (run dividend divisor fuel state) = state := by
  induction fuel generalizing state with
  | zero => simp [run, rewindRun]
  | succ fuel inductionHypothesis =>
    by_cases stopped : dividend < state.scale * divisor
    · simp only [run, if_pos stopped, Nat.sub_self, rewindRun]
    · simp only [run, if_neg stopped]
      have lower := (run_places dividend divisor fuel (step state)).1
      change state.places + 1 ≤ (run dividend divisor fuel (step state)).places at lower
      have displacement : (run dividend divisor fuel (step state)).places - state.places =
          ((run dividend divisor fuel (step state)).places - (state.places + 1)) + 1 := by
        omega
      rw [displacement]
      change rewind (rewindRun
        ((run dividend divisor fuel (step state)).places - (step state).places)
          (run dividend divisor fuel (step state))) = state
      rw [inductionHypothesis (step state)]
      exact rewind_step state

/-- Align by actual comparisons and shifts, using the dividend's independent bit-length fuel. -/
def align (dividend divisor : Nat) : State :=
  run dividend divisor dividend.size initial

/-- Actual first-phase output has the exact power-of-two scale recorded by its counter. -/
theorem align_scale (dividend divisor : Nat) :
    (align dividend divisor).scale = 2 ^ (align dividend divisor).places :=
  run_scale dividend divisor dividend.size initial rfl

/-- A positive divisor suffices for the actual source alignment loop to stop. -/
theorem align_stops (dividend divisor : Nat) (positive : 0 < divisor) :
    dividend < (align dividend divisor).scale * divisor := by
  change dividend < (run dividend divisor dividend.size initial).scale * divisor
  apply run_stops
  change dividend < 2 ^ dividend.size * 1 * divisor
  calc
    dividend < 2 ^ dividend.size := Nat.lt_size_self dividend
    _ ≤ 2 ^ dividend.size * divisor := Nat.le_mul_of_pos_right _ positive
    _ = _ := by rw [Nat.mul_one]

/-- The actual first phase performs at most the dividend bit length many shifts. -/
theorem align_places_le (dividend divisor : Nat) :
    (align dividend divisor).places ≤ dividend.size := by
  unfold align
  simpa only [initial, Nat.zero_add] using
    (run_places dividend divisor dividend.size initial).2

/-- Unless no shift was needed, the immediately preceding scale still fit the dividend. -/
theorem align_previous_fits (dividend divisor : Nat) :
    (align dividend divisor).places = 0 ∨
      (align dividend divisor).scale / 2 * divisor ≤ dividend :=
  run_previous_fits dividend divisor dividend.size initial (Or.inl rfl)

/-- The actual retained shift counter reverses the complete first-phase alignment. -/
theorem align_reversible (dividend divisor : Nat) :
    rewindRun (align dividend divisor).places (align dividend divisor) = initial := by
  unfold align
  simpa only [initial, Nat.sub_zero] using
    rewindRun_run dividend divisor dividend.size initial

/-- The quotient bit length is a proved description of the actual alignment count. -/
theorem align_places_eq_quotient_size (dividend divisor : Nat) (positive : 0 < divisor) :
    (align dividend divisor).places = (dividend / divisor).size := by
  have scale := align_scale dividend divisor
  have upper := align_stops dividend divisor positive
  have quotientUpper : dividend / divisor < 2 ^ (align dividend divisor).places := by
    apply (Nat.div_lt_iff_lt_mul positive).mpr
    simpa only [← scale] using upper
  have sizeUpper := Nat.size_le.mpr quotientUpper
  apply Nat.le_antisymm
  · by_cases zeroPlaces : (align dividend divisor).places = 0
    · omega
    · have previous := align_previous_fits dividend divisor
      have previousBound : (align dividend divisor).scale / 2 * divisor ≤ dividend := by
        omega
      have exponent : (align dividend divisor).places =
          ((align dividend divisor).places - 1) + 1 := by omega
      have halfScale : (align dividend divisor).scale / 2 =
          2 ^ ((align dividend divisor).places - 1) := by
        rw [scale]
        calc
          _ = 2 ^ (((align dividend divisor).places - 1) + 1) / 2 :=
            congrArg (fun power : Nat => 2 ^ power / 2) exponent
          _ = _ := by
            rw [Nat.pow_succ]
            exact Nat.mul_div_left _ (by decide : 0 < 2)
      have quotientLower : 2 ^ ((align dividend divisor).places - 1) ≤
          dividend / divisor := by
        apply (Nat.le_div_iff_mul_le positive).mpr
        simpa only [halfScale] using previousBound
      have sizeLower := Nat.lt_size.mpr quotientLower
      omega
  · exact sizeUpper

/-- Run the actual first and second phases, with no precomputed quotient at their boundary. -/
def divide (dividend divisor : Nat) : DivisionPhase.State :=
  let aligned := align dividend divisor
  DivisionPhase.divide divisor dividend aligned.scale aligned.places

/-- Actual alignment eliminates the internal entry conditions of quotient extraction. -/
theorem divide_quotient (dividend divisor : Nat) (positive : 0 < divisor) :
    (divide dividend divisor).quotientPrefix = dividend / divisor :=
  DivisionPhase.divide_quotient divisor dividend _ _
    (align_scale dividend divisor) (align_stops dividend divisor positive)

/-- The actual first two phases produce the ordinary Euclidean remainder. -/
theorem divide_remainder (dividend divisor : Nat) (positive : 0 < divisor) :
    (divide dividend divisor).remainder = dividend % divisor :=
  DivisionPhase.divide_remainder divisor dividend _ _
    (align_scale dividend divisor) (align_stops dividend divisor positive)

/-- The actual first three arithmetic phases agree with the complete EEA macro coordinates. -/
theorem division_coefficient_coordinates (state : IterationState) (active : 0 < state.divisor) :
    (divide state.remainder state.divisor).remainder = (IterationState.step state).divisor ∧
      (CoefficientPhase.finish state.coefficient
        (DivisionPhase.coefficientStart state (divide state.remainder state.divisor))).value =
          (IterationState.step state).coefficient :=
  DivisionPhase.division_coefficient_coordinates state _ _
    (align_scale state.remainder state.divisor) (align_stops state.remainder state.divisor active)

/-- The original positive-residue domain reaches the actual macro result after folding. -/
theorem folded_coordinates (modulus input : Nat)
    (positive : 0 < input) (bounded : input < modulus) :
    let state := IterationState.initial modulus (foldInput modulus input).2
    (divide state.remainder state.divisor).remainder = (IterationState.step state).divisor ∧
      (CoefficientPhase.finish state.coefficient
        (DivisionPhase.coefficientStart state (divide state.remainder state.divisor))).value =
          (IterationState.step state).coefficient :=
  division_coefficient_coordinates _
    (foldInput_positive_half modulus input positive bounded).1

/-- The smallest input actually doubles twice before the equality-boundary division step. -/
theorem smallest_input_alignment :
    align 2 1 = ⟨4, 2⟩ ∧ divide 2 1 = ⟨0, 2, 1, 2⟩ ∧
      align 0 1 = ⟨1, 0⟩ := by
  decide

end QuantumAlg.NumberTheory.SharedEEA.Alignment
