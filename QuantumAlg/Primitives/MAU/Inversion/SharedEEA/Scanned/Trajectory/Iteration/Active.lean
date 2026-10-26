/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Trajectory.Iteration.Phases
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Trajectory

/-! # Actual active Iter changes occur only after a multiple of four microsteps -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.TrajectoryIteration

noncomputable section

open NumberTheory.SharedEEA

/-- A nonfourth active source step retains Iter, derived from the complete phase trajectory. -/
lemma active_iteration_step (fuel : Nat) (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (coprime : Nat.gcd state.remainder state.divisor = 1)
    (within : count + 1 ≤ 4 * QuotientTrajectory.weight fuel state)
    (nonfourth : (count + 1) % 4 ≠ 0) (iteration : Bool) :
    ((SharedEEA.NativeMicrostep.step modulus.size)^[count + 1]
      (MacroBoundary.frame state modulus valid conserved iteration)).flags.iteration =
    ((SharedEEA.NativeMicrostep.step modulus.size)^[count]
      (MacroBoundary.frame state modulus valid conserved iteration)).flags.iteration := by
  induction fuel generalizing state count iteration with
  | zero =>
      change count + 1 ≤ 4 * 0 at within
      omega
  | succ fuel ih =>
      by_cases finished : state.divisor = 0
      · rw [QuotientTrajectory.weight, if_pos finished, Nat.mul_zero] at within
        omega
      · have active := Nat.pos_of_ne_zero finished
        by_cases before : count < 4 * state.quotient.size
        · have nextBefore : count + 1 < 4 * state.quotient.size := by omega
          exact (macro_iteration_before state modulus (count + 1) valid conserved coprime
            active nextBefore iteration).trans
              (macro_iteration_before state modulus count valid conserved coprime
                active before iteration).symm
        · have tailWithin : count - 4 * state.quotient.size + 1 ≤
              4 * QuotientTrajectory.weight fuel (IterationState.step state) := by
            rw [QuotientTrajectory.weight, if_neg finished] at within
            omega
          let nextFrame := MacroBoundary.frame (IterationState.step state) modulus
            (IterationState.step_admissible state valid active)
            ((IterationState.step_balance state).trans conserved) (!iteration)
          have atNext :
              (SharedEEA.NativeMicrostep.step modulus.size)^[count + 1]
                (MacroBoundary.frame state modulus valid conserved iteration) =
              (SharedEEA.NativeMicrostep.step modulus.size)^[count -
                4 * state.quotient.size + 1] nextFrame := by
            rw [show count + 1 = (count - 4 * state.quotient.size + 1) +
              4 * state.quotient.size by omega, Function.iterate_add_apply,
              NativeMacrostep.native_frame state modulus valid conserved coprime active iteration]
          have atCurrent :
              (SharedEEA.NativeMicrostep.step modulus.size)^[count]
                (MacroBoundary.frame state modulus valid conserved iteration) =
              (SharedEEA.NativeMicrostep.step modulus.size)^[count -
                4 * state.quotient.size] nextFrame := by
            conv_lhs => rw [show count = (count - 4 * state.quotient.size) +
              4 * state.quotient.size by omega]
            rw [Function.iterate_add_apply,
              NativeMacrostep.native_frame state modulus valid conserved coprime active iteration]
          rw [atNext, atCurrent]
          exact ih (state := IterationState.step state)
            (count := count - 4 * state.quotient.size)
            (valid := IterationState.step_admissible state valid active)
            (conserved := (IterationState.step_balance state).trans conserved)
            (coprime := (IterationState.step_gcd state).trans coprime)
            (within := tailWithin) (nonfourth := by omega) (iteration := !iteration)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.TrajectoryIteration
