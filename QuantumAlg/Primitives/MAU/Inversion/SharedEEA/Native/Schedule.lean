/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.ActiveProgram
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Terminal.Microstep

/-!
# Complete independent native schedule from every coprime positive input

The emitted loop has the fixed count `4 * (2*n - 1)`, justified by the
integer quotient potential. Its input-dependent active length appears
only in the proof that splits this one fixed program into active phases
and a real rotating terminal suffix
[LYL+26, app_proof/sub_stepnum.tex:4-16;
LYL+26, sec_EEA/sub_4phase.tex:107-128].

The actual full clock uses two existing Work1 positions, whose initial
zero values follow from the terminal gcd-one packing. Every scheduled
terminal position is below its complete capacity, including even nontrivial
moduli. The final frame retains all words, lengths, flags,
and iteration history. Decoding and copying the inverse require their
own actual gates; this forward theorem does not discard any history.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.NativeSchedule

noncomputable section

open NumberTheory.SharedEEA

/-- Mathematical terminal frame reached by the active prefix of the same native program. -/
def terminalFrame (modulus input : Nat) (positive : 0 < input) (bounded : input < modulus) :
    Registers modulus.size :=
  MacroBoundary.frame (TerminalPadding.finalState modulus input) modulus
    (TerminalPadding.final_admissible modulus input positive bounded)
    (TerminalPadding.final_balance modulus input)
    (SignedTrajectory.finalIteration modulus input)

private theorem terminal_divisor (modulus input : Nat)
    (positive : 0 < input) (bounded : input < modulus) :
    (terminalFrame modulus input positive bounded).divisorLength = 0 := by
  change BitVec.ofNat modulus.size.size (TerminalPadding.finalState modulus input).divisor.size = 0
  rw [TerminalPadding.final_divisor modulus input positive bounded]
  rfl

private theorem terminal_clock (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    ExtendedClockRegisters.clock (terminalFrame modulus input positive bounded) = 0 :=
  PaddingClock.final_counter_zero modulus input coprime positive bounded

private theorem padding_fits (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    QuotientSchedule.padding modulus input < 2 ^ (2 + modulus.size.size) := by
  simpa only [Nat.add_comm] using
    QuotientSchedule.padding_fits_extended_clock modulus input coprime positive bounded

/-- The fixed native loop includes every terminal microstep and has the complete retained frame. -/
theorem iterate_initial (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    (NativeMicrostep.step modulus.size)^[QuotientSchedule.schedule modulus.size]
      (MacroBoundary.frame (IterationState.initial modulus (foldInput modulus input).2) modulus
        (folded_initial_admissible modulus input positive bounded)
        (IterationState.initial_balance modulus (foldInput modulus input).2)
        (foldInput modulus input).1) =
      TerminalPosition.frame (terminalFrame modulus input positive bounded)
        (QuotientSchedule.padding modulus input) := by
  have count : QuotientSchedule.schedule modulus.size =
      QuotientSchedule.padding modulus input + QuotientSchedule.phaseWeight modulus input := by
    have within := (QuotientSchedule.phase_weight_bounds modulus input coprime positive bounded).2
    unfold QuotientSchedule.padding
    omega
  rw [count, Function.iterate_add_apply,
    NativeTrajectory.folded_frame modulus input coprime positive bounded]
  exact TerminalMicrostep.iterate_frame (terminalFrame modulus input positive bounded)
    (QuotientSchedule.padding modulus input) rfl rfl rfl
    (terminal_divisor modulus input positive bounded)
    (terminal_clock modulus input coprime positive bounded)
    (padding_fits modulus input coprime positive bounded)

/-- Actual input preprocessing followed by the independently bounded native repetition. -/
def program (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit (Qubits (encoding modulus.size).width) :=
  (InitialFrame.program modulus).seq
    (UnitaryCircuit.iterate (QuotientSchedule.schedule modulus.size)
      (NativeMicrostep.program modulus.size
        (PredicateLayout.modulus_length_width modulus nontrivial)))

/-- Coprime positive residues execute the same fixed circuit with exact normalized amplitudes. -/
theorem program_initial (modulus : Nat) (nontrivial : 1 < modulus)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) :
    (program modulus nontrivial).applyNormalized
        (NormalizedVector.ket (R := Qubits (encoding modulus.size).width)
          ((encoding modulus.size).encode (InitialFrame.initial modulus input))) =
      NormalizedVector.ket (R := Qubits (encoding modulus.size).width)
        ((encoding modulus.size).encode
          (TerminalPosition.frame (terminalFrame modulus input.val positive bounded)
            (QuotientSchedule.padding modulus input.val))) := by
  rw [program, UnitaryCircuit.applyNormalized_seq,
    InitialMacroFrame.program_initial modulus input positive bounded,
    (NativeActiveProgram.iterate_realizes modulus.size (QuotientSchedule.schedule modulus.size)
      (PredicateLayout.modulus_length_width modulus nontrivial)).apply_encoded_ket,
    iterate_initial modulus input.val coprime positive bounded]

/-- The complete emitted inverse restores every normalized forward state and all its history. -/
theorem dagger_after_forward (modulus : Nat) (nontrivial : 1 < modulus)
    (state : NormalizedVector (Qubits (encoding modulus.size).width)) :
    (program modulus nontrivial).dagger.applyNormalized
        ((program modulus nontrivial).applyNormalized state) =
      state :=
  UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized (program modulus nontrivial) state

end

end QuantumAlg.MAU.Inversion.SharedEEA.NativeSchedule
