/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Trajectory.Control.Phases
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Trajectory

/-! # Internally clean Ctrl at every actual active-prefix microstep -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.TrajectoryControl

noncomputable section

open NumberTheory.SharedEEA

/-- Every bounded prefix of the proved active trajectory retains internally initialized Ctrl. -/
lemma active_control (fuel : Nat) (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (coprime : Nat.gcd state.remainder state.divisor = 1)
    (within : count ≤ 4 * QuotientTrajectory.weight fuel state) (iteration : Bool) :
    ((SharedEEA.NativeMicrostep.step modulus.size)^[count]
      (MacroBoundary.frame state modulus valid conserved iteration)).control = false := by
  induction fuel generalizing state count iteration with
  | zero =>
      have zero : count = 0 := by
        change count ≤ 4 * 0 at within
        omega
      subst count
      rfl
  | succ fuel ih =>
      by_cases finished : state.divisor = 0
      · have zero : count = 0 := by
          rw [QuotientTrajectory.weight, if_pos finished, Nat.mul_zero] at within
          omega
        subst count
        rfl
      · have active := Nat.pos_of_ne_zero finished
        by_cases before : count ≤ 4 * state.quotient.size
        · exact macro_control state modulus count valid conserved coprime active before iteration
        · have tailBound :
              count - 4 * state.quotient.size ≤
                4 * QuotientTrajectory.weight fuel (IterationState.step state) := by
            rw [QuotientTrajectory.weight, if_neg finished] at within
            omega
          rw [show count = (count - 4 * state.quotient.size) + 4 * state.quotient.size by omega,
            Function.iterate_add_apply,
            NativeMacrostep.native_frame state modulus valid conserved coprime active iteration]
          exact ih (state := IterationState.step state)
            (count := count - 4 * state.quotient.size)
            (valid := IterationState.step_admissible state valid active)
            (conserved := (IterationState.step_balance state).trans conserved)
            (coprime := (IterationState.step_gcd state).trans coprime)
            (within := tailBound) (iteration := !iteration)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.TrajectoryControl
