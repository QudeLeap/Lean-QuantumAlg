/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Division.Capacity

/-!
# Actual aligned-threshold and changing-region capacities

The next phase-two threshold is the actual current scale shifted right,
times the unchanged divisor [LYL+26, sec_EEA/sub_regshare.tex:279-287].
Minimality of the already executed first-phase alignment bounds its
highest binary place. Consequently every actual subtraction threshold
fits the next remainder region, even though the old remainder need not.

The old region is exactly one bit wider than the next region. Signed
subtraction and add-back must retain that old bit until the corrected
remainder fits the smaller region and the quotient-bit swap takes place.
All capacity conditions here follow from the conserved reachable macro
invariant and the actual intermediate position. No extra original input
restriction or precomputed quotient is used to initialize a phase.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.DivisionThreshold

private theorem run_succ (divisor count : Nat) (state : DivisionPhase.State) :
    DivisionPhase.run divisor (count + 1) state =
      DivisionPhase.step divisor (DivisionPhase.run divisor count state) := by
  induction count generalizing state with
  | zero => rfl
  | succ count inductionHypothesis =>
    exact inductionHypothesis (DivisionPhase.step divisor state)

/-- The next actual intermediate state is the same source division microstep. -/
theorem current_step (state : IterationState) (count : Nat) :
    DivisionProgress.current state (count + 1) =
      DivisionPhase.step state.divisor (DivisionProgress.current state count) :=
  run_succ state.divisor count _

/-- The source threshold after its actual right shift at the next division microstep. -/
def threshold (state : IterationState) (count : Nat) : Nat :=
  (DivisionProgress.current state count).scale / 2 * state.divisor

/-- The actual right-shifted threshold has the corresponding remaining binary-place value. -/
theorem threshold_eq (state : IterationState) (count : Nat) (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    threshold state count =
      2 ^ ((Alignment.align state.remainder state.divisor).places - (count + 1)) *
        state.divisor := by
  have scale := (DivisionProgress.current_invariants state count active beforeEnd.le).1
  unfold threshold
  rw [scale]
  have exponent : (Alignment.align state.remainder state.divisor).places - count =
      ((Alignment.align state.remainder state.divisor).places - (count + 1)) + 1 := by omega
  rw [exponent, Nat.pow_succ, Nat.mul_div_left _ (by decide : 0 < 2)]

/-- Every actual subtraction threshold is positive before the division phase ends. -/
theorem threshold_positive (state : IterationState) (count : Nat)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    0 < threshold state count := by
  rw [threshold_eq state count active beforeEnd]
  exact Nat.mul_pos (Nat.two_pow_pos _) active

/-- Undoing the written-position displacement recovers the same actual highest threshold. -/
theorem threshold_scaled (state : IterationState) (count : Nat)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    2 ^ count * threshold state count =
      2 ^ ((Alignment.align state.remainder state.divisor).places - 1) * state.divisor := by
  rw [threshold_eq state count active beforeEnd]
  calc
    _ = (2 ^ count *
          2 ^ ((Alignment.align state.remainder state.divisor).places - (count + 1))) *
        state.divisor := by ring
    _ = 2 ^ (count + ((Alignment.align state.remainder state.divisor).places - (count + 1))) *
        state.divisor := by rw [← Nat.pow_add]
    _ = _ := by
      congr 2
      omega

/-- Actual alignment minimality bounds the highest threshold by the original remainder. -/
theorem highest_threshold_le (state : IterationState)
    (hasPlace : 0 < (Alignment.align state.remainder state.divisor).places) :
    2 ^ ((Alignment.align state.remainder state.divisor).places - 1) * state.divisor ≤
      state.remainder := by
  have previous := Alignment.align_previous_fits state.remainder state.divisor
  have previousBound : (Alignment.align state.remainder state.divisor).scale / 2 *
      state.divisor ≤ state.remainder := by omega
  have halfScale : (Alignment.align state.remainder state.divisor).scale / 2 =
      2 ^ ((Alignment.align state.remainder state.divisor).places - 1) := by
    rw [Alignment.align_scale]
    have exponent : (Alignment.align state.remainder state.divisor).places =
        ((Alignment.align state.remainder state.divisor).places - 1) + 1 := by omega
    rw [exponent, Nat.pow_succ, Nat.mul_div_left _ (by decide : 0 < 2)]
    congr 1
  simpa only [halfScale] using previousBound

/-- The actual highest-place product yields the threshold's full position-dependent bit bound. -/
theorem threshold_size (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    state.coefficient.size + count + (threshold state count).size ≤ modulus.size + 1 := by
  have thresholdPositive := threshold_positive state count active beforeEnd
  have highestBound := highest_threshold_le state (by omega)
  have macroProduct : state.coefficient * state.remainder ≤ modulus := by
    simpa only [conserved, Nat.mul_comm] using (IterationState.products_le_balance state).1
  have productBound : state.coefficient * (2 ^ count * threshold state count) ≤ modulus := by
    rw [threshold_scaled state count active beforeEnd]
    exact (Nat.mul_le_mul_left _ highestBound).trans macroProduct
  have capacity := Capacity.positive_pair_size state.coefficient
    (2 ^ count * threshold state count) modulus valid.coefficient_pos
    (Nat.mul_pos (Nat.two_pow_pos count) thresholdPositive) productBound
  have shiftedSize : (2 ^ count * threshold state count).size =
      (threshold state count).size + count := by
    rw [Nat.mul_comm, ← Nat.shiftLeft_eq_mul_pow]
    exact Nat.size_shiftLeft (Nat.ne_of_gt thresholdPositive) count
  rw [shiftedSize] at capacity
  omega

/-- The actual threshold fits the new remainder region, although the old remainder can be larger. -/
theorem threshold_fits_next (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    threshold state count < 2 ^ DivisionCapacity.remainderWidth state modulus (count + 1) := by
  apply Nat.size_le.mp
  have capacity := threshold_size state modulus count valid conserved active beforeEnd
  unfold DivisionCapacity.remainderWidth
  rw [DivisionProgress.current_written]
  omega

/-- One new quotient position takes exactly one bit from the old remainder region. -/
theorem remainder_width_succ (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    DivisionCapacity.remainderWidth state modulus count =
      DivisionCapacity.remainderWidth state modulus (count + 1) + 1 := by
  have nextCapacity := DivisionCapacity.work1_capacity state modulus (count + 1)
    valid conserved active (by omega)
  rw [DivisionProgress.current_written] at nextCapacity
  unfold DivisionCapacity.remainderWidth
  rw [DivisionProgress.current_written, DivisionProgress.current_written]
  omega

end QuantumAlg.NumberTheory.SharedEEA.DivisionThreshold
