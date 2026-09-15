/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Advance
import Mathlib.Logic.Function.Iterate

/-!
# Exact complete-frame trajectory of actual native quotient consumption

Each real phase-three microstep consumes the next quotient bit, expands
the complete remainder field by its physically cleared bit, updates the
coefficient, and advances the rotated Work2 and finite shift counter
[LYL+26, sec_EEA/sub_regshare.tex:288-296]. The same native ordered control
suffix enters phase four with Sign one after the last quotient bit
[LYL+26, sec_EEA/sub_opt.tex:74-75]. All earlier steps have Sign zero.

The iteration here is ordinary function iteration of the already realized
native microstep, with arbitrary original Iter retained. It is not another
executor or a detached resource formula. This proof ends at the exact
phase-four entry; it does not assume that the later fixed coefficient
comparison window implements a full integer comparison.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.CoefficientTrajectory

noncomputable section

open NumberTheory.SharedEEA

private theorem count_fits (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (within : count ≤ state.quotient.size) : count < 2 ^ modulus.size.size :=
  (within.trans (CoefficientPhaseFrame.quotient_size_le state modulus valid conserved)).trans_lt
    (Nat.lt_size_self modulus.size)

/-- Full basis frame after the specified number of actual coefficient microsteps. -/
def phaseFrame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : count ≤ state.quotient.size)
    (iteration : Bool) : Registers modulus.size where
  firstWord := (WordPacking.packWork1
    (CoefficientCapacity.work1Payload state modulus count valid conserved)).cast
      (CoefficientCapacity.work1_width state modulus count valid conserved)
  secondWord := (PackedCoefficientWindow.word state modulus count valid conserved active).cast
    (CoefficientCapacity.work2_width state modulus valid conserved)
  coefficientLength := BitVec.ofNatLT state.coefficient.size
    (CoefficientPhaseFrame.size_fits_counter
      (Capacity.iteration_fields_le state modulus valid conserved).2.2.1)
  quotientLength := BitVec.ofNatLT (state.quotient.size - count)
    (CoefficientConsumeFrame.remaining_fits state modulus count valid conserved)
  divisorLength := BitVec.ofNatLT state.divisor.size
    (CoefficientPhaseFrame.size_fits_counter
      (Capacity.iteration_fields_le state modulus valid conserved).2.1)
  shift := BitVec.ofNatLT count (count_fits state modulus count valid conserved within)
  flags := ⟨true, decide (count = state.quotient.size),
    decide (count = state.quotient.size), iteration⟩
  control := false

private theorem frame_eq_consume (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    phaseFrame state modulus count valid conserved active beforeEnd.le iteration =
      CoefficientConsumeFrame.frame state modulus count
        valid conserved active beforeEnd iteration := by
  unfold phaseFrame
  rw [decide_eq_false (Nat.ne_of_lt beforeEnd)]
  rfl

private theorem next_eq_frame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    let expected := CoefficientAdvance.nextFrame state modulus count
      valid conserved active beforeEnd iteration
    { expected with flags :=
      ⟨true, decide (expected.quotientLength = (0#modulus.size.size)),
        decide (expected.quotientLength = (0#modulus.size.size)), iteration⟩ } =
      phaseFrame state modulus (count + 1) valid conserved active (by omega) iteration := by
  dsimp only
  let expected := CoefficientAdvance.nextFrame state modulus count
    valid conserved active beforeEnd iteration
  have zero : expected.quotientLength = (0#modulus.size.size) ↔
      count + 1 = state.quotient.size := by
    constructor
    · intro same
      have value := congrArg (fun word : BitVec modulus.size.size => word.toNat) same
      change state.quotient.size - (count + 1) = 0 at value
      omega
    · intro atEnd
      apply BitVec.eq_of_toNat_eq
      change state.quotient.size - (count + 1) = 0
      omega
  have test : decide (expected.quotientLength = (0#modulus.size.size)) =
      decide (count + 1 = state.quotient.size) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using zero
  change { expected with flags :=
    ⟨true, decide (expected.quotientLength = (0#modulus.size.size)),
      decide (expected.quotientLength = (0#modulus.size.size)), iteration⟩ } = _
  rw [test]
  rfl

/-- The same complete native microstep advances the phase frame at every active position. -/
theorem microstep_frame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    NativeMicrostep.step modulus.size
      (phaseFrame state modulus count valid conserved active beforeEnd.le iteration) =
      phaseFrame state modulus (count + 1) valid conserved active (by omega) iteration := by
  rw [frame_eq_consume state modulus count valid conserved active beforeEnd iteration,
    CoefficientAdvance.microstep_frame state modulus count
      valid conserved active beforeEnd iteration]
  exact next_eq_frame state modulus count valid conserved active beforeEnd iteration

/-- Every bounded iteration of the actual native program has the complete specified frame. -/
theorem iterate_frame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : count ≤ state.quotient.size) (iteration : Bool) :
    (NativeMicrostep.step modulus.size)^[count]
      (phaseFrame state modulus 0 valid conserved active (Nat.zero_le _) iteration) =
      phaseFrame state modulus count valid conserved active within iteration := by
  revert within
  induction count with
  | zero =>
      intro within
      rfl
  | succ count ih =>
      intro within
      have previous : count ≤ state.quotient.size := by omega
      rw [Function.iterate_succ_apply', ih previous]
      exact microstep_frame state modulus count valid conserved active (by omega) iteration

/-- Exact quotient consumption reaches the actual phase-four entry, including its Sign one. -/
theorem finish_frame (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (iteration : Bool) :
    (NativeMicrostep.step modulus.size)^[state.quotient.size]
      (phaseFrame state modulus 0 valid conserved active (Nat.zero_le _) iteration) =
      phaseFrame state modulus state.quotient.size valid conserved active le_rfl iteration :=
  iterate_frame state modulus _ valid conserved active le_rfl iteration

/-- The full coefficient phase leaves no quotient, but retains the exact shift and entry flags. -/
theorem finish_fields (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (iteration : Bool) :
    let result := (NativeMicrostep.step modulus.size)^[state.quotient.size]
      (phaseFrame state modulus 0 valid conserved active (Nat.zero_le _) iteration)
    result.quotientLength.toNat = 0 ∧ result.shift.toNat = state.quotient.size ∧
      result.flags = ⟨true, true, true, iteration⟩ := by
  dsimp only
  rw [finish_frame state modulus valid conserved active iteration]
  change state.quotient.size - state.quotient.size = 0 ∧ state.quotient.size = state.quotient.size ∧
    (⟨true, decide (state.quotient.size = state.quotient.size),
      decide (state.quotient.size = state.quotient.size), iteration⟩ : PhaseControl.Flags) = _
  simp only [Nat.sub_self, decide_true, and_self]

end

end QuantumAlg.MAU.Inversion.SharedEEA.CoefficientTrajectory
