/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Trajectory.Iteration.Active
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Trajectory.Control.Schedule
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Microstep.History

/-!
# Internally certified boundary identity at fixed nonfourth positions

The actual active source macros have lengths divisible by four. Their
complete phase frames and the genuine rotating-clock terminal suffix
prove the unchanged Iter at all other completed positions. The generic
original boundary criterion then identifies the complete source step
with its actual first seven blocks, without a new caller premise.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.TrajectoryIteration

noncomputable section

open NumberTheory.SharedEEA ClassicalAlgorithms.NumberTheory

/-- The full fixed source schedule changes Iter only at completed multiples of four. -/
lemma schedule_iteration_step (modulus input count : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus)
    (within : count + 1 ≤ QuotientSchedule.schedule modulus.size)
    (nonfourth : (count + 1) % 4 ≠ 0) :
    ((SharedEEA.NativeMicrostep.step modulus.size)^[count + 1]
      (MacroBoundary.frame (IterationState.initial modulus (foldInput modulus input).2) modulus
        (folded_initial_admissible modulus input positive bounded)
        (IterationState.initial_balance modulus (foldInput modulus input).2)
        (foldInput modulus input).1)).flags.iteration =
    ((SharedEEA.NativeMicrostep.step modulus.size)^[count]
      (MacroBoundary.frame (IterationState.initial modulus (foldInput modulus input).2) modulus
        (folded_initial_admissible modulus input positive bounded)
        (IterationState.initial_balance modulus (foldInput modulus input).2)
        (foldInput modulus input).1)).flags.iteration := by
  have total : QuotientSchedule.schedule modulus.size =
      QuotientSchedule.phaseWeight modulus input + QuotientSchedule.padding modulus input := by
    have admitted := (QuotientSchedule.phase_weight_bounds modulus input coprime positive bounded).2
    unfold QuotientSchedule.padding
    omega
  by_cases before : count + 1 ≤ QuotientSchedule.phaseWeight modulus input
  · have foldedCoprime : Nat.gcd modulus (foldInput modulus input).2 = 1 := by
      rw [foldInput_gcd modulus input bounded.le]
      exact coprime.symm
    exact active_iteration_step (Euclid.gcdFuel modulus.size)
      (IterationState.initial modulus (foldInput modulus input).2) modulus count
      (folded_initial_admissible modulus input positive bounded)
      (IterationState.initial_balance modulus (foldInput modulus input).2)
      foldedCoprime before nonfourth (foldInput modulus input).1
  · have position (index : Nat) (after : QuotientSchedule.phaseWeight modulus input ≤ index)
        (indexWithin : index ≤ QuotientSchedule.schedule modulus.size) :
        (SharedEEA.NativeMicrostep.step modulus.size)^[index]
          (MacroBoundary.frame (IterationState.initial modulus (foldInput modulus input).2) modulus
            (folded_initial_admissible modulus input positive bounded)
            (IterationState.initial_balance modulus (foldInput modulus input).2)
            (foldInput modulus input).1) =
        TerminalPosition.frame
          (SharedEEA.NativeSchedule.terminalFrame modulus input positive bounded)
          (index - QuotientSchedule.phaseWeight modulus input) := by
      have tailWithin : index - QuotientSchedule.phaseWeight modulus input <
          2 ^ (2 + modulus.size.size) := by
        have tailLe : index - QuotientSchedule.phaseWeight modulus input ≤
            QuotientSchedule.padding modulus input := by omega
        exact tailLe.trans_lt
          (SharedEEA.NativeSchedule.padding_fits modulus input coprime positive bounded)
      conv_lhs => rw [show index = (index - QuotientSchedule.phaseWeight modulus input) +
        QuotientSchedule.phaseWeight modulus input by omega]
      rw [Function.iterate_add_apply,
        NativeTrajectory.folded_frame modulus input coprime positive bounded]
      change (SharedEEA.NativeMicrostep.step modulus.size)^[index -
        QuotientSchedule.phaseWeight modulus input]
          (SharedEEA.NativeSchedule.terminalFrame modulus input positive bounded) = _
      exact TerminalMicrostep.iterate_frame
        (SharedEEA.NativeSchedule.terminalFrame modulus input positive bounded) _
        rfl rfl rfl (SharedEEA.NativeSchedule.terminal_divisor modulus input positive bounded)
        (SharedEEA.NativeSchedule.terminal_clock modulus input coprime positive bounded) tailWithin
    rw [position (count + 1) (by omega) within, position count (by omega) (by omega)]
    rfl

/-- At every fixed nonfourth position, the full real boundary is identity on the source orbit. -/
lemma schedule_step_eq_body (modulus input count : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus)
    (within : count + 1 ≤ QuotientSchedule.schedule modulus.size)
    (nonfourth : (count + 1) % 4 ≠ 0) :
    let state := (SharedEEA.NativeMicrostep.step modulus.size)^[count]
      (MacroBoundary.frame (IterationState.initial modulus (foldInput modulus input).2) modulus
        (folded_initial_admissible modulus input positive bounded)
        (IterationState.initial_balance modulus (foldInput modulus input).2)
        (foldInput modulus input).1)
    SharedEEA.NativeMicrostep.step modulus.size state =
      Scanned.NativeMicrostep.bodyStep modulus.size state := by
  dsimp only
  apply Scanned.NativeMicrostep.source_step_eq_body_of_iteration
  · exact TrajectoryControl.schedule_control modulus input count coprime positive bounded (by omega)
  · have actual := schedule_iteration_step modulus input count coprime positive bounded
      within nonfourth
    rw [Function.iterate_succ_apply'] at actual
    exact actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.TrajectoryIteration
