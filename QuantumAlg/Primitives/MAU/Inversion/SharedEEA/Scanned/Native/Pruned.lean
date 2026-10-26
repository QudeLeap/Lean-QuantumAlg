/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Native.Schedule
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Microstep.Cycle
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Trajectory.Iteration.Schedule

/-!
# Actual fixed shared-EEA schedule with internally certified boundary omissions

Every input executes the same public repetition of three actual
seven-block prefixes followed by one complete eight-block microstep.
The original source-phase/fuel/terminal history proves identity of the
omitted boundaries at each of those static positions. The complete
source state and entire pool have the same final physical endpoint.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.PrunedSchedule

noncomputable section

open NumberTheory.SharedEEA

/-- The same independent public repetition runs for every admitted quantum input. -/
def program (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding modulus.size).width).toQuantum :=
  (NativeSchedule.initialProgram modulus).seq
    (UnitaryCircuit.iterate (2 * modulus.size - 1)
      (NativeMicrostep.cycleProgram modulus.size
        (PredicateLayout.modulus_length_width modulus nontrivial)))

/-- Exact complete fixed-schedule endpoint with the same entire initialized pool returned. -/
lemma program_initial (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) (pool : Pool modulus.size)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false) :
    (program modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((encoding modulus.size).encode (InitialFrame.initial modulus input, pool)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding modulus.size).encode
          (TerminalPosition.frame
            (SharedEEA.NativeSchedule.terminalFrame modulus input.val positive bounded)
            (QuotientSchedule.padding modulus input.val), pool))) := by
  let prepared : Data modulus.size :=
    (MacroBoundary.frame (IterationState.initial modulus (foldInput modulus input.val).2) modulus
      (folded_initial_admissible modulus input.val positive bounded)
      (IterationState.initial_balance modulus (foldInput modulus input.val).2)
      (foldInput modulus input.val).1, pool)
  let ket (value : Data modulus.size) :=
    NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((encoding modulus.size).encode value))
  have firstActual := UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
    (SharedEEA.encoding modulus.size) (poolEncoding modulus.size) (InitialFrame.program modulus)
    (InitialFrame.initial modulus input) prepared.1 pool
    (InitialMacroFrame.program_initial (environment := environment) modulus input positive bounded)
  change (NativeSchedule.initialProgram modulus).applyNormalized environment
    (ket (InitialFrame.initial modulus input, pool)) = ket prepared at firstActual
  have secondActual := NativeMicrostep.iterate_cycle_apply_source modulus.size
    (2 * modulus.size - 1)
    (PredicateLayout.modulus_length_width modulus nontrivial) environment prepared
    prefixZero addressZero borrowZero
    (fun index within => TrajectoryControl.schedule_control modulus input.val index coprime
      positive bounded within.le)
    (fun index within nonfourth => TrajectoryIteration.schedule_step_eq_body modulus input.val
      index coprime positive bounded within nonfourth)
  have orbit := SharedEEA.NativeSchedule.iterate_initial modulus input.val coprime positive bounded
  have endpoint := congrArg (fun result => ket (result, pool)) orbit
  change (program modulus nontrivial).applyNormalized environment
    (ket (InitialFrame.initial modulus input, pool)) = _
  rw [program, UnitaryCircuit.applyNormalized_seq, firstActual]
  exact secondActual.trans endpoint

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.PrunedSchedule
