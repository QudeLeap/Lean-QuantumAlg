/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Macrostep

/-!
# Actual internal Ctrl invariant at every certified source-phase position

The original complete microstep can leave Ctrl nonzero on unreachable
labels. Its admitted active trajectories instead have the exact physical
phase frames below at every intermediate position. These identities
supply the internal invariant for iterating the new scanned native word;
they introduce no input-dependent circuit construction.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.TrajectoryControl

noncomputable section

open NumberTheory.SharedEEA

/-- Every original active alignment position retains the internally initialized Ctrl. -/
lemma alignment_control (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : count ≤ state.quotient.size) (iteration : Bool) :
    ((SharedEEA.NativeMicrostep.step modulus.size)^[count]
      (MacroBoundary.frame state modulus valid conserved iteration)).control = false := by
  rw [AlignmentTrajectory.iterate_position state modulus count valid conserved active within
    iteration]
  rfl

/-- Every original active division position retains the same internal Ctrl value. -/
lemma division_control (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (within : count ≤ (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    ((SharedEEA.NativeMicrostep.step modulus.size)^[count]
      (DivisionTrajectory.phaseFrame state modulus 0 valid conserved active
        (Nat.zero_le _) iteration)).control = false := by
  rw [DivisionTrajectory.iterate_frame state modulus count valid conserved active within iteration]
  rfl

/-- Every original active coefficient position retains the same internal Ctrl value. -/
lemma coefficient_control (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : count ≤ state.quotient.size) (iteration : Bool) :
    ((SharedEEA.NativeMicrostep.step modulus.size)^[count]
      (CoefficientTrajectory.phaseFrame state modulus 0 valid conserved active
        (Nat.zero_le _) iteration)).control = false := by
  rw [CoefficientTrajectory.iterate_frame state modulus count valid conserved active within
    iteration]
  rfl

/-- The complete deshift trajectory includes the actual final boundary Ctrl cleanup. -/
lemma deshift_control (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (coprime : Nat.gcd state.remainder state.divisor = 1)
    (active : 0 < state.divisor) (within : count ≤ state.quotient.size) (iteration : Bool) :
    ((SharedEEA.NativeMicrostep.step modulus.size)^[count]
      (CoefficientTrajectory.phaseFrame state modulus state.quotient.size
        valid conserved active le_rfl iteration)).control = false := by
  rw [DeshiftComparison.entry_frame state modulus valid conserved active iteration,
    DeshiftTrajectory.iterate_position state modulus count valid conserved coprime active within
      iteration]
  unfold DeshiftTrajectory.position
  split <;> rfl

/-- Every intermediate position of the complete source macrostep has internally clean Ctrl. -/
lemma macro_control (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (coprime : Nat.gcd state.remainder state.divisor = 1)
    (active : 0 < state.divisor) (within : count ≤ 4 * state.quotient.size)
    (iteration : Bool) :
    ((SharedEEA.NativeMicrostep.step modulus.size)^[count]
      (MacroBoundary.frame state modulus valid conserved iteration)).control = false := by
  let q := state.quotient.size
  have places : (Alignment.align state.remainder state.divisor).places = q :=
    Alignment.align_places_eq_quotient_size state.remainder state.divisor active
  have divisionFinish :
      (SharedEEA.NativeMicrostep.step modulus.size)^[q]
        (DivisionTrajectory.phaseFrame state modulus 0 valid conserved active
          (Nat.zero_le _) iteration) =
      CoefficientTrajectory.phaseFrame state modulus 0 valid conserved active
        (Nat.zero_le _) iteration := by
    rw [← places, DivisionTrajectory.finish_frame,
      CoefficientEntry.division_eq_coefficient state modulus valid conserved active iteration]
  have middleFinish :
      (SharedEEA.NativeMicrostep.step modulus.size)^[q + q]
        (MacroBoundary.frame state modulus valid conserved iteration) =
      CoefficientTrajectory.phaseFrame state modulus 0 valid conserved active
        (Nat.zero_le _) iteration := by
    rw [Function.iterate_add_apply,
      AlignmentTrajectory.finish_frame state modulus valid conserved active iteration,
      divisionFinish]
  have thirdFinish :
      (SharedEEA.NativeMicrostep.step modulus.size)^[q + q + q]
        (MacroBoundary.frame state modulus valid conserved iteration) =
      CoefficientTrajectory.phaseFrame state modulus q valid conserved active le_rfl iteration := by
    rw [show q + q + q = q + (q + q) by omega, Function.iterate_add_apply, middleFinish,
      CoefficientTrajectory.finish_frame state modulus valid conserved active iteration]
  change count ≤ 4 * q at within
  by_cases first : count ≤ q
  · exact alignment_control state modulus count valid conserved active first iteration
  · by_cases second : count ≤ 2 * q
    · rw [show count = (count - q) + q by omega, Function.iterate_add_apply,
        AlignmentTrajectory.finish_frame state modulus valid conserved active iteration]
      exact division_control state modulus (count - q) valid conserved active (by omega) iteration
    · by_cases third : count ≤ 3 * q
      · rw [show count = (count - (q + q)) + (q + q) by omega,
          Function.iterate_add_apply, middleFinish]
        exact coefficient_control state modulus (count - (q + q)) valid conserved active
          (by omega) iteration
      · rw [show count = (count - (q + q + q)) + (q + q + q) by omega,
          Function.iterate_add_apply, thirdFinish]
        exact deshift_control state modulus (count - (q + q + q)) valid conserved coprime active
          (by omega) iteration

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.TrajectoryControl
