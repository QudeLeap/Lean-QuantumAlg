/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Macrostep

/-!
# Exact retained Iter before the actual final macro boundary

The original complete source trajectory retains Iter in its first three
phases and every nonfinal deshift position. Only the actual final
macro-boundary exchange complements it. These statements concern the
same full native source action, not a proposed shortened circuit.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.TrajectoryIteration

noncomputable section

open NumberTheory.SharedEEA

/-- Every complete alignment position retains the original Iter. -/
lemma alignment_iteration (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : count ≤ state.quotient.size) (iteration : Bool) :
    ((SharedEEA.NativeMicrostep.step modulus.size)^[count]
      (MacroBoundary.frame state modulus valid conserved iteration)).flags.iteration =
        iteration := by
  rw [AlignmentTrajectory.iterate_position state modulus count valid conserved active within
    iteration]
  rfl

/-- Every complete division position retains the original Iter. -/
lemma division_iteration (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (within : count ≤ (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    ((SharedEEA.NativeMicrostep.step modulus.size)^[count]
      (DivisionTrajectory.phaseFrame state modulus 0 valid conserved active
        (Nat.zero_le _) iteration)).flags.iteration = iteration := by
  rw [DivisionTrajectory.iterate_frame state modulus count valid conserved active within iteration]
  rfl

/-- Every complete coefficient position retains the original Iter. -/
lemma coefficient_iteration (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : count ≤ state.quotient.size) (iteration : Bool) :
    ((SharedEEA.NativeMicrostep.step modulus.size)^[count]
      (CoefficientTrajectory.phaseFrame state modulus 0 valid conserved active
        (Nat.zero_le _) iteration)).flags.iteration = iteration := by
  rw [CoefficientTrajectory.iterate_frame state modulus count valid conserved active within
    iteration]
  rfl

/-- Strictly before its final real boundary, deshifting retains the original Iter. -/
lemma deshift_iteration_before (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (coprime : Nat.gcd state.remainder state.divisor = 1)
    (active : 0 < state.divisor) (before : count < state.quotient.size) (iteration : Bool) :
    ((SharedEEA.NativeMicrostep.step modulus.size)^[count]
      (CoefficientTrajectory.phaseFrame state modulus state.quotient.size
        valid conserved active le_rfl iteration)).flags.iteration = iteration := by
  rw [DeshiftComparison.entry_frame state modulus valid conserved active iteration,
    DeshiftTrajectory.iterate_position state modulus count valid conserved coprime active
      before.le iteration, DeshiftTrajectory.position, if_pos before]
  rfl

/-- Only the last position of the complete source macrostep can change Iter. -/
lemma macro_iteration_before (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (coprime : Nat.gcd state.remainder state.divisor = 1)
    (active : 0 < state.divisor) (before : count < 4 * state.quotient.size)
    (iteration : Bool) :
    ((SharedEEA.NativeMicrostep.step modulus.size)^[count]
      (MacroBoundary.frame state modulus valid conserved iteration)).flags.iteration =
        iteration := by
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
  change count < 4 * q at before
  by_cases first : count ≤ q
  · exact alignment_iteration state modulus count valid conserved active first iteration
  · by_cases second : count ≤ 2 * q
    · rw [show count = (count - q) + q by omega, Function.iterate_add_apply,
        AlignmentTrajectory.finish_frame state modulus valid conserved active iteration]
      exact division_iteration state modulus (count - q) valid conserved active (by omega) iteration
    · by_cases third : count ≤ 3 * q
      · rw [show count = (count - (q + q)) + (q + q) by omega,
          Function.iterate_add_apply, middleFinish]
        exact coefficient_iteration state modulus (count - (q + q)) valid conserved active
          (by omega) iteration
      · rw [show count = (count - (q + q + q)) + (q + q + q) by omega,
          Function.iterate_add_apply, thirdFinish]
        exact deshift_iteration_before state modulus (count - (q + q + q)) valid conserved
          coprime active (by omega) iteration

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.TrajectoryIteration
