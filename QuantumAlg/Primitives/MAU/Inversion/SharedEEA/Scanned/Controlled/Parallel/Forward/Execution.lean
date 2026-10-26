/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Parallel.Cycle.Execution
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Parallel.Forward
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Native.Pruned

/-!
# Direct original-domain correctness of the actual complete paired EEA forward

Actual load, initialization, all fixed cycles, complete decoding and
correction, and actual unload are composed directly. The final result
is the original independent same-port inverse specification, with every
original history field and the complete original physical pool retained.
No complete legacy executor equality or output theorem is used.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledParallel

noncomputable section

open NumberTheory.SharedEEA

/-- The active fixed schedule has the complete original terminal source and retained history. -/
private lemma pruned_initial_active (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation) (input : Fin (2 ^ modulus.size))
    (coprime : Nat.Coprime input.val modulus) (positive : 0 < input.val)
    (bounded : input.val < modulus) (pool : Pool modulus.size)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false)
    (flags : Bool × Bool) (selected : flags.1 = true) :
    ((ControlledInitialization.program modulus).seq
      (UnitaryCircuit.iterate (2 * modulus.size - 1)
        (cycleProgram modulus.size
          (PredicateLayout.modulus_length_width modulus nontrivial)))).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding modulus.size).encode
            ((InitialFrame.initial modulus input, pool), flags)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding modulus.size).encode
          ((TerminalPosition.frame
            (SharedEEA.NativeSchedule.terminalFrame modulus input.val positive bounded)
            (QuotientSchedule.padding modulus input.val), pool), flags))) := by
  let prepared : ControlledFrame.Data modulus.size :=
    ((MacroBoundary.frame (IterationState.initial modulus (foldInput modulus input.val).2) modulus
      (folded_initial_admissible modulus input.val positive bounded)
      (IterationState.initial_balance modulus (foldInput modulus input.val).2)
      (foldInput modulus input.val).1, pool), flags)
  let ket (value : ControlledFrame.Data modulus.size) :=
    NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((ControlledFrame.encoding modulus.size).encode value))
  have first := ControlledInitialization.program_initial_active modulus input environment pool
    flags selected positive bounded
  have second := iterate_cycle_apply_active modulus.size
    (2 * modulus.size - 1) (PredicateLayout.modulus_length_width modulus nontrivial)
    environment prepared prefixZero addressZero borrowZero selected
    (fun index within => TrajectoryControl.schedule_control modulus input.val index coprime
      positive bounded within.le)
    (fun index within nonfourth => TrajectoryIteration.schedule_step_eq_body modulus input.val
      index coprime positive bounded within nonfourth)
  have orbit := SharedEEA.NativeSchedule.iterate_initial modulus input.val coprime positive bounded
  have endpoint := congrArg (fun result => ket ((result, pool), flags)) orbit
  exact UnitaryCircuit.applyNormalized_seq_of_eq first (second.trans endpoint)

/-- Direct complete execution retains the original positive coprime residue admission. -/
lemma program_initial_active_direct (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation) (input : Fin (2 ^ modulus.size))
    (coprime : Nat.Coprime input.val modulus) (positive : 0 < input.val)
    (bounded : input.val < modulus) (pool : Pool modulus.size)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false)
    (flags : Bool × Bool) (selected : flags.1 = true) :
    (program modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding modulus.size).encode
            ((InitialPortProgram.inputFrame modulus input, pool), flags)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding modulus.size).encode
          ((SharedEEA.InPlaceForward.result modulus input.val positive bounded, pool),
            flags))) := by
  have first := ControlledInitialization.loadProgram_initial modulus input environment pool flags
  simp only [selected, if_true] at first
  have middle := pruned_initial_active modulus nontrivial environment input coprime positive bounded
    pool addressZero prefixZero borrowZero flags selected
  have completion := ControlledCompletion.program_terminal_active modulus input.val environment
    pool flags selected coprime positive bounded
  have last := (ControlledCompletion.unloadProgram_realizes modulus environment).apply_encoded_ket
    ((SharedEEA.CorrectedSchedule.result modulus input.val positive bounded, pool), flags)
  change (ControlledCompletion.unloadProgram modulus).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding modulus.size).encode
          ((SharedEEA.CorrectedSchedule.result modulus input.val positive bounded, pool),
            flags)))) =
    NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((ControlledFrame.encoding modulus.size).encode
        ((if flags.1 then SharedEEA.InPlaceForward.result modulus input.val positive bounded
          else SharedEEA.CorrectedSchedule.result modulus input.val positive bounded, pool),
            flags)))
    at last
  simp only [selected, if_true] at last
  exact UnitaryCircuit.applyNormalized_seq_of_eq first
    (UnitaryCircuit.applyNormalized_seq_of_eq
      (UnitaryCircuit.applyNormalized_seq_of_eq middle completion) last)

/-- Direct inactive execution accepts zero input and arbitrary original finite source values. -/
lemma program_apply_disabled_direct (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation) (state : ControlledFrame.Data modulus.size)
    (prefixZero : state.1.2.2.1 = 0) (addressZero : state.1.2.1 = 0)
    (borrowZero : state.1.2.2.2 = false) (control : state.1.1.control = false)
    (disabled : state.2.1 = false) :
    (program modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding modulus.size).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding modulus.size).encode state)) := by
  have first := (ControlledSourceWord.program_realizes modulus.size
    (Work1Constant.gates modulus.size (InitialPortProgram.constant modulus))
    environment).apply_encoded_ket state
  change (ControlledInitialization.loadProgram modulus).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding modulus.size).encode state))) =
    NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((ControlledFrame.encoding modulus.size).encode
        (ControlledSource.step modulus.size
          (EncodedBit.GateSpec.stepList
            (Work1Constant.gates modulus.size (InitialPortProgram.constant modulus)))
              state))) at first
  rw [ControlledSource.step_disabled modulus.size _ state disabled] at first
  have initialization :=
    (ControlledInitialization.program_realizes modulus environment).apply_encoded_ket state
  rw [ControlledSource.step_disabled modulus.size _ state disabled] at initialization
  have loop := iterate_cycle_apply_disabled modulus.size (2 * modulus.size - 1)
    (PredicateLayout.modulus_length_width modulus nontrivial) environment state
    prefixZero addressZero borrowZero control disabled
  have completion := (ControlledCompletion.program_realizes modulus environment).apply_encoded_ket
    state
  rw [ControlledSource.step_disabled modulus.size _ state disabled] at completion
  have last := (ControlledCompletion.unloadProgram_realizes modulus environment).apply_encoded_ket
    state
  rw [ControlledSource.step_disabled modulus.size _ state disabled] at last
  exact UnitaryCircuit.applyNormalized_seq_of_eq first
    (UnitaryCircuit.applyNormalized_seq_of_eq
      (UnitaryCircuit.applyNormalized_seq_of_eq
        (UnitaryCircuit.applyNormalized_seq_of_eq initialization loop) completion) last)

/-- The adjoint of this same actual unitary restores the original active physical input. -/
lemma dagger_result_direct (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation) (input : Fin (2 ^ modulus.size))
    (coprime : Nat.Coprime input.val modulus) (positive : 0 < input.val)
    (bounded : input.val < modulus) (pool : Pool modulus.size)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false)
    (flags : Bool × Bool) (selected : flags.1 = true) :
    ((program modulus nontrivial).dagger
        (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized environment
          (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
            ((ControlledFrame.encoding modulus.size).encode
              ((SharedEEA.InPlaceForward.result modulus input.val positive bounded, pool),
                flags)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding modulus.size).encode
          ((InitialPortProgram.inputFrame modulus input, pool), flags))) := by
  have actual := program_initial_active_direct modulus nontrivial environment input coprime positive
    bounded pool addressZero prefixZero borrowZero flags selected
  exact (congrArg (fun state => ((program modulus nontrivial).dagger
      (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized environment state)
    actual).symm.trans
    (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
      (program modulus nontrivial)
      ((program modulus nontrivial).dagger (AlgorithmGate.oracleFreeAdjoints .empty))
      (by
        rw [UnitaryCircuit.dagger_matrix,
          Subsingleton.elim ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment)
            environment]
        exact Unitary.star_eq_inv _) _)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledParallel

