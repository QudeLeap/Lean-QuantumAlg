/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Trajectory
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Division.Trajectory

/-!
# Exact native division-to-coefficient phase boundary

The completed native division trajectory supplies the complete quotient,
Euclidean remainder, unrotated previous coefficient/divisor word, and
phase-three entry flags [LYL+26, sec_EEA/sub_regshare.tex:279-289]. These
are exactly the physical input of the native coefficient trajectory.
The equality below checks all original bits and finite fields; it neither
prepares an input-dependent state nor casts between unrelated cardinalities.

The combined result executes the same native microstep through both middle
phases and ends at the precise phase-four entry with Sign one. Later
comparison-window and terminal-counter correctness are separate obligations.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.CoefficientEntry

noncomputable section

open NumberTheory.SharedEEA

private lemma final_quotient (state : IterationState) (active : 0 < state.divisor) :
    (DivisionProgress.current state
      (Alignment.align state.remainder state.divisor).places).quotientPrefix =
        state.quotient := by
  rw [DivisionProgress.current_prefix state _ active le_rfl,
    Nat.sub_self, Nat.pow_zero, Nat.div_one]

private lemma final_remainder (state : IterationState) (active : 0 < state.divisor) :
    (DivisionProgress.current state
      (Alignment.align state.remainder state.divisor).places).remainder =
        state.remainder % state.divisor := by
  rw [DivisionProgress.current_end, Alignment.divide_remainder _ _ active]

private lemma firstWord_same (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (iteration : Bool) :
    (DivisionTrajectory.phaseFrame state modulus
      (Alignment.align state.remainder state.divisor).places
      valid conserved active le_rfl iteration).firstWord =
    (CoefficientTrajectory.phaseFrame state modulus 0 valid conserved active
      (Nat.zero_le _) iteration).firstWord := by
  let count := (Alignment.align state.remainder state.divisor).places
  let old := DivisionCapacity.work1Payload state modulus count valid conserved active le_rfl
  let next := CoefficientCapacity.work1Payload state modulus 0 valid conserved
  have countEq : count = state.quotient.size :=
    Alignment.align_places_eq_quotient_size state.remainder state.divisor active
  have written : (DivisionProgress.current state count).written = state.quotient.size :=
    (DivisionProgress.current_written state count).trans countEq
  have remainderWidth : DivisionCapacity.remainderWidth state modulus count =
      CoefficientCapacity.work1RemainderWidth state modulus 0 := by
    unfold DivisionCapacity.remainderWidth CoefficientCapacity.work1RemainderWidth
    rw [written, Nat.sub_zero]
  apply BitVec.eq_of_toNat_eq
  change ((WordPacking.packWork1 old).cast
    (DivisionCapacity.work1_width state modulus count valid conserved active le_rfl)).toNat =
    ((WordPacking.packWork1 next).cast
      (CoefficientCapacity.work1_width state modulus 0 valid conserved)).toNat
  rw [BitVec.toNat_cast, BitVec.toNat_cast]
  change (((old.coefficientBits.reverse ++ (0 : BitVec 1)) ++
    (old.quotientBits ++ old.remainderBits)).toNat) =
    (((next.coefficientBits.reverse ++ (0 : BitVec 1)) ++
      (next.quotientBits ++ next.remainderBits)).toNat)
  rw [DivisionPackedStep.append_toNat (old.coefficientBits.reverse ++ (0 : BitVec 1))
      (old.quotientBits ++ old.remainderBits),
    DivisionPackedStep.append_toNat (next.coefficientBits.reverse ++ (0 : BitVec 1))
      (next.quotientBits ++ next.remainderBits),
    DivisionPackedStep.append_toNat old.quotientBits old.remainderBits,
    DivisionPackedStep.append_toNat next.quotientBits next.remainderBits]
  change ((BitVec.ofNatLT state.coefficient (Nat.lt_size_self _)).reverse ++
      (0 : BitVec 1)).toNat *
      2 ^ ((DivisionProgress.current state count).written +
        DivisionCapacity.remainderWidth state modulus count) +
      ((DivisionProgress.current state count).quotientPrefix *
        2 ^ DivisionCapacity.remainderWidth state modulus count +
          (DivisionProgress.current state count).remainder) =
    ((BitVec.ofNatLT state.coefficient (Nat.lt_size_self _)).reverse ++
      (0 : BitVec 1)).toNat *
      2 ^ ((state.quotient.size - 0) +
        CoefficientCapacity.work1RemainderWidth state modulus 0) +
      (state.quotient * 2 ^ CoefficientCapacity.work1RemainderWidth state modulus 0 +
        state.remainder % state.divisor)
  rw [written, remainderWidth, final_quotient state active, final_remainder state active,
    Nat.sub_zero]

private lemma secondWord_same (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (iteration : Bool) :
    (DivisionTrajectory.phaseFrame state modulus
      (Alignment.align state.remainder state.divisor).places
      valid conserved active le_rfl iteration).secondWord =
    (CoefficientTrajectory.phaseFrame state modulus 0 valid conserved active
      (Nat.zero_le _) iteration).secondWord := by
  change ((WordRotation.packRotatedWork2
    ((Alignment.align state.remainder state.divisor).places -
      (Alignment.align state.remainder state.divisor).places)
    (DivisionCapacity.work2Payload state modulus valid conserved)).cast
      (DivisionCapacity.work2_width state modulus valid conserved)) = _
  rw [Nat.sub_self]
  rfl

/-- All phase-two output fields are exactly the input to actual quotient consumption. -/
lemma division_eq_coefficient (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (iteration : Bool) :
    DivisionTrajectory.phaseFrame state modulus
      (Alignment.align state.remainder state.divisor).places
      valid conserved active le_rfl iteration =
    CoefficientTrajectory.phaseFrame state modulus 0 valid conserved active
      (Nat.zero_le _) iteration := by
  have positive : 0 < state.quotient.size := Nat.size_pos.mpr
    (IterationState.quotient_pos state valid.divisor_lt active)
  have initialTest : decide (0 = state.quotient.size) = false :=
    decide_eq_false (by omega)
  have countEq : (Alignment.align state.remainder state.divisor).places = state.quotient.size :=
    Alignment.align_places_eq_quotient_size state.remainder state.divisor active
  apply Registers.ext_fields
  · exact firstWord_same state modulus valid conserved active iteration
  · exact secondWord_same state modulus valid conserved active iteration
  · rfl
  · apply BitVec.eq_of_toNat_eq
    change (Alignment.align state.remainder state.divisor).places = state.quotient.size - 0
    simpa only [Nat.sub_zero] using countEq
  · rfl
  · apply BitVec.eq_of_toNat_eq
    change (Alignment.align state.remainder state.divisor).places -
      (Alignment.align state.remainder state.divisor).places = 0
    exact Nat.sub_self _
  · change decide ((Alignment.align state.remainder state.divisor).places =
      (Alignment.align state.remainder state.divisor).places) = true
    exact decide_eq_true rfl
  · change (!decide ((Alignment.align state.remainder state.divisor).places =
      (Alignment.align state.remainder state.divisor).places)) =
        decide (0 = state.quotient.size)
    rw [decide_eq_true rfl, initialTest, Bool.not_true]
  · change false = decide (0 = state.quotient.size)
    exact initialTest.symm
  · rfl
  · rfl

/-- The same actual native sequence completes division and then consumes its complete quotient. -/
lemma middle_phases (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (iteration : Bool) :
    (NativeMicrostep.step modulus.size)^[state.quotient.size]
      ((NativeMicrostep.step modulus.size)^[
        (Alignment.align state.remainder state.divisor).places]
        (DivisionTrajectory.phaseFrame state modulus 0 valid conserved active
          (Nat.zero_le _) iteration)) =
      CoefficientTrajectory.phaseFrame state modulus state.quotient.size
        valid conserved active le_rfl iteration := by
  rw [DivisionTrajectory.finish_frame state modulus valid conserved active iteration,
    division_eq_coefficient state modulus valid conserved active iteration]
  exact CoefficientTrajectory.finish_frame state modulus valid conserved active iteration

end

end QuantumAlg.MAU.Inversion.SharedEEA.CoefficientEntry
