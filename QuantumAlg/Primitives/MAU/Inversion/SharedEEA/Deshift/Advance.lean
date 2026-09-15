/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Deshift.Comparison
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Deshift.Phase.Prelude
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Division.Entry

/-!
# Complete actual fourth-phase comparison, right shift, and ordered control

The source's real post-shift follows coefficient comparison and precedes
the ordered flag update [LYL+26, sec_EEA/sub_opt.tex:61-79]. Its increment
and two decrements compose to a decrement of the retained finite counter;
the corresponding actual full-word rotations remove one physical shift.

Every complete intermediate native microstep below has a nonzero remaining
shift, so its actual boundary predicates are false. The final zero-shift
step must instead execute the real word exchange, length updates, and Iter
flip. That boundary is deliberately retained as an explicit suffix, never
replaced by an idle rule. All bounds come from the original macro invariant.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.DeshiftAdvance

noncomputable section

open NumberTheory.SharedEEA DeshiftPhaseFrame

private theorem word_after (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size)
    (positive : 0 < shift) (sign iteration : Bool) :
    (frame state modulus shift valid conserved active within sign iteration).secondWord.rotateRight
        1 =
      (frame state modulus (shift - 1) valid conserved active
        ((Nat.sub_le _ _).trans within) sign iteration).secondWord := by
  have displacement : shift = shift - 1 + 1 := by omega
  change ((WordRotation.packRotatedWork2 shift
    (CoefficientCapacity.work2Payload state modulus state.quotient.size
      valid conserved active)).cast
        (CoefficientCapacity.work2_width state modulus valid conserved)).rotateRight 1 = _
  rw [DivisionEntry.cast_rotateRight]
  conv_lhs => rw [displacement, WordRotation.packRotatedWork2_unshift]
  rfl

private theorem shift_after (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size)
    (positive : 0 < shift) (sign iteration : Bool) :
    (frame state modulus shift valid conserved active within sign iteration).shift - 1 =
      (frame state modulus (shift - 1) valid conserved active
        ((Nat.sub_le _ _).trans within) sign iteration).shift := by
  have bounded := DeshiftPhaseFrame.shift_fits state modulus shift valid conserved within
  have oneFits : 1 < 2 ^ modulus.size.size := by omega
  rw [BitVec.sub_eq_iff_eq_add]
  apply BitVec.eq_of_toNat_eq
  change shift = ((frame state modulus (shift - 1) valid conserved active
    ((Nat.sub_le _ _).trans within) sign iteration).shift + 1).toNat
  rw [BitVec.toNat_add]
  change shift = (shift - 1 + 1 % 2 ^ modulus.size.size) % 2 ^ modulus.size.size
  rw [Nat.mod_eq_of_lt oneFits, Nat.sub_add_cancel positive, Nat.mod_eq_of_lt bounded]

/-- The actual post-shift preserves the entire frame except its exact rotation and counter. -/
theorem post_shift_frame (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size)
    (positive : 0 < shift) (sign iteration : Bool) :
    GuardedShift.step true
      (frame state modulus shift valid conserved active within sign iteration) =
      frame state modulus (shift - 1) valid conserved active
        ((Nat.sub_le _ _).trans within) sign iteration := by
  have actualPositive :
      0 < (frame state modulus shift valid conserved active within sign iteration).shift.toNat := by
    change 0 < shift
    exact positive
  rw [DeshiftPhasePrelude.post_shift modulus.size
    (frame state modulus shift valid conserved active within sign iteration)
      rfl rfl rfl actualPositive,
    word_after state modulus shift valid conserved active within positive sign iteration,
    shift_after state modulus shift valid conserved active within positive sign iteration]
  rfl

/-- The real ordered control clears comparison Sign one and retains the full phase-four frame. -/
theorem control_frame (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size) (iteration : Bool) :
    NativeControl.step (frame state modulus shift valid conserved active within true iteration) =
      frame state modulus shift valid conserved active within false iteration := by
  let original := frame state modulus shift valid conserved active within true iteration
  have quotient : original.quotientLength = (0#modulus.size.size) := by
    apply BitVec.eq_of_toNat_eq
    change state.quotient.size - state.quotient.size = 0
    exact Nat.sub_self _
  have divisor : original.divisorLength ≠ (0#modulus.size.size) := by
    intro zero
    have value := congrArg (fun word : BitVec modulus.size.size => word.toNat) zero
    change state.divisor.size = 0 at value
    have positive := Nat.size_pos.mpr active
    omega
  exact DeshiftPhasePrelude.control_clears original rfl rfl rfl rfl quotient divisor

/-- Actual comparison, post-shifts, and control reach the complete next rotation with Sign zero. -/
theorem native_shift_control (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    NativeControl.step (GuardedShift.step true (ArithmeticBlocks.coefficientStep modulus.size
      (frame state modulus (state.quotient.size - count) valid conserved active
        (Nat.sub_le _ _) (decide (count = 0)) iteration))) =
      frame state modulus (state.quotient.size - count - 1) valid conserved active
        ((Nat.sub_le _ _).trans (Nat.sub_le _ _)) false iteration := by
  rw [DeshiftComparison.native_frame state modulus count valid conserved active beforeEnd iteration,
    post_shift_frame state modulus (state.quotient.size - count) valid conserved active
      (Nat.sub_le _ _) (by omega) true iteration,
    control_frame state modulus (state.quotient.size - count - 1) valid conserved active
      ((Nat.sub_le _ _).trans (Nat.sub_le _ _)) iteration]

/-- Every intermediate microstep includes all eight real blocks and retains the complete frame. -/
theorem microstep_frame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (notLast : count + 1 < state.quotient.size) (iteration : Bool) :
    NativeMicrostep.step modulus.size
      (frame state modulus (state.quotient.size - count) valid conserved active
        (Nat.sub_le _ _) (decide (count = 0)) iteration) =
      frame state modulus (state.quotient.size - count - 1) valid conserved active
        ((Nat.sub_le _ _).trans (Nat.sub_le _ _)) false iteration := by
  let original := frame state modulus (state.quotient.size - count) valid conserved active
    (Nat.sub_le _ _) (decide (count = 0)) iteration
  let expected := frame state modulus (state.quotient.size - count - 1) valid conserved active
    ((Nat.sub_le _ _).trans (Nat.sub_le _ _)) false iteration
  have nonzero : expected.shift ≠ (0#modulus.size.size) := by
    intro zero
    have value := congrArg (fun word : BitVec modulus.size.size => word.toNat) zero
    change state.quotient.size - count - 1 = 0 at value
    omega
  rw [NativeMicrostep.step,
    CoefficientTail.pre_shift_inactive modulus.size original rfl rfl,
    CoefficientTail.remainder_inactive modulus.size original rfl rfl,
    DeshiftPhasePrelude.quotient_inactive modulus.size original rfl rfl,
    native_shift_control state modulus count valid conserved active (by omega) iteration,
    CoefficientTail.zero_shift_inactive expected rfl nonzero,
    CoefficientTail.boundary_inactive expected rfl nonzero]

end

end QuantumAlg.MAU.Inversion.SharedEEA.DeshiftAdvance
