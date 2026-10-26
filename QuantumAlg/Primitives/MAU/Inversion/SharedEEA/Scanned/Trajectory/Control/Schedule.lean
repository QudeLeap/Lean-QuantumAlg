/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Trajectory.Control.Active
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Schedule

/-!
# Every reached position of the independent fixed schedule has clean internal Ctrl

The actual original phase trajectories establish the active prefix. Its
proved terminal frame supplies the complete rotating-clock suffix. The
input-dependent proof split chooses no program or loop count: the public
emitted schedule remains exactly the same for every admitted input.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.TrajectoryControl

noncomputable section

open NumberTheory.SharedEEA ClassicalAlgorithms.NumberTheory

/-- The original coprime positive-residue domain internally supplies every loop invariant. -/
lemma schedule_control (modulus input count : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus)
    (within : count ≤ QuotientSchedule.schedule modulus.size) :
    ((SharedEEA.NativeMicrostep.step modulus.size)^[count]
      (MacroBoundary.frame (IterationState.initial modulus (foldInput modulus input).2) modulus
        (folded_initial_admissible modulus input positive bounded)
        (IterationState.initial_balance modulus (foldInput modulus input).2)
        (foldInput modulus input).1)).control = false := by
  have total : QuotientSchedule.schedule modulus.size =
      QuotientSchedule.phaseWeight modulus input + QuotientSchedule.padding modulus input := by
    have admitted := (QuotientSchedule.phase_weight_bounds modulus input coprime positive bounded).2
    unfold QuotientSchedule.padding
    omega
  by_cases before : count ≤ QuotientSchedule.phaseWeight modulus input
  · have foldedCoprime : Nat.gcd modulus (foldInput modulus input).2 = 1 := by
      rw [foldInput_gcd modulus input bounded.le]
      exact coprime.symm
    exact active_control (Euclid.gcdFuel modulus.size)
      (IterationState.initial modulus (foldInput modulus input).2) modulus count
      (folded_initial_admissible modulus input positive bounded)
      (IterationState.initial_balance modulus (foldInput modulus input).2)
      foldedCoprime before (foldInput modulus input).1
  · let tailCount := count - QuotientSchedule.phaseWeight modulus input
    have tailWithin : tailCount < 2 ^ (2 + modulus.size.size) := by
      have tailLe : tailCount ≤ QuotientSchedule.padding modulus input := by
        rw [total] at within
        dsimp only [tailCount]
        omega
      exact tailLe.trans_lt
        (SharedEEA.NativeSchedule.padding_fits modulus input coprime positive bounded)
    rw [show count = tailCount + QuotientSchedule.phaseWeight modulus input by
      dsimp only [tailCount]
      omega, Function.iterate_add_apply,
      NativeTrajectory.folded_frame modulus input coprime positive bounded]
    change ((SharedEEA.NativeMicrostep.step modulus.size)^[tailCount]
      (SharedEEA.NativeSchedule.terminalFrame modulus input positive bounded)).control = false
    rw [TerminalMicrostep.iterate_frame
        (SharedEEA.NativeSchedule.terminalFrame modulus input positive bounded) tailCount
        rfl rfl rfl (SharedEEA.NativeSchedule.terminal_divisor modulus input positive bounded)
        (SharedEEA.NativeSchedule.terminal_clock modulus input coprime positive bounded) tailWithin]
    rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.TrajectoryControl
