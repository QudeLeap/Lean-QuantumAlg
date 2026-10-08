/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.CorrectedSchedule
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ClockDecode.Gates

/-! # Complete literal fixed schedule, decoder and correction on the original frame -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.CorrectedSchedule

noncomputable section

open EncodedBit GateSpec

/-- The actual complete word includes every fixed microstep repetition and every decoder gate. -/
def gates (modulus : Nat) (nontrivial : 1 < modulus) : List (GateSpec (encoding modulus.size)) :=
  (FoldProgram.gates modulus ++ InitialLengthWrite.gates modulus.size) ++
    (List.replicate (NumberTheory.SharedEEA.QuotientSchedule.schedule modulus.size)
      (NativeMicrostep.gates modulus.size
        (PredicateLayout.modulus_length_width modulus nontrivial))).flatten ++
    ClockDecode.gates modulus.size ++ OutputCorrection.gates modulus

/-- Complete action on arbitrary source labels, with no restriction on auxiliary values. -/
def step (modulus : Nat) (state : Registers modulus.size) : Registers modulus.size :=
  let active := (NativeMicrostep.step modulus.size)^[
    NumberTheory.SharedEEA.QuotientSchedule.schedule modulus.size]
      (stepList (InitialLengthWrite.gates modulus.size) (FoldProgram.step modulus state))
  OutputCorrection.step modulus { active with
    secondWord := active.secondWord.rotateRight (ExtendedClockRegisters.clock active).toNat }

/-- The fixed literal schedule agrees on every original register, including arbitrary dirty data. -/
theorem correctedSchedule_gates_step (modulus : Nat) (nontrivial : 1 < modulus)
    (state : Registers modulus.size) :
    stepList (gates modulus nontrivial) state = step modulus state := by
  have same : stepList (NativeMicrostep.gates modulus.size
      (PredicateLayout.modulus_length_width modulus nontrivial)) = NativeMicrostep.step
      modulus.size :=
    funext (NativeMicrostep.nativeMicrostep_gates_step _ _)
  simp only [gates, stepList_append, FoldProgram.foldProgram_gates_step,
    ClockDecode.repeated_step, same, ClockDecode.clockDecode_gates_step,
    OutputCorrection.outputCorrection_gates_step]
  rfl

-- Generic realization laws consume this word without evaluating its recursive generator.
attribute [local irreducible] gates

/-- The original symbolic schedule realizes the same complete unrestricted action. -/
theorem correctedSchedule_program_realizes (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit.Realizes (encoding modulus.size) (program modulus nontrivial)
      (step modulus) := by
  exact (((InitialFrame.program_realizes modulus).seq
    ((NativeMicrostep.program_realizes modulus.size
      (PredicateLayout.modulus_length_width modulus nontrivial)).iterate
        (NumberTheory.SharedEEA.QuotientSchedule.schedule modulus.size))).seq
    (ClockDecode.program_realizes modulus.size)).seq
      (OutputCorrection.outputCorrection_nativeProgram_realizes modulus)

/-- Execute the actual concatenated instructions on their original complete physical frame. -/
def nativeProgram (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding modulus.size).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (gates modulus nontrivial)

/-- Exact phases and every original frame coordinate are retained by the emitted word. -/
theorem correctedSchedule_nativeProgram_realizes (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit.Realizes (encoding modulus.size) (nativeProgram modulus nontrivial)
      (step modulus) :=
  realizesList_congrStep (QubitLayout.canonical _) .empty _
    (correctedSchedule_gates_step modulus nontrivial)

/-- The complete native and symbolic schedules agree exactly on every encoded basis label. -/
theorem correctedSchedule_nativeProgram_basis (modulus : Nat) (nontrivial : 1 < modulus)
    (state : Registers modulus.size) :
    (nativeProgram modulus nontrivial).applyNormalized
      (NormalizedVector.ket ((QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
        ((encoding modulus.size).encode state))) =
    (program modulus nontrivial).applyNormalized
      (NormalizedVector.ket ((QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
        ((encoding modulus.size).encode state))) :=
  ((correctedSchedule_nativeProgram_realizes modulus nontrivial).apply_encoded_ket state).trans
    ((correctedSchedule_program_realizes modulus nontrivial).apply_encoded_ket state).symm

/-- No repetition, fold, decode or correction event is omitted or reordered. -/
theorem correctedSchedule_gates_trace (modulus : Nat) (nontrivial : 1 < modulus) :
    (gates modulus nontrivial).map (event .empty) = (program modulus nontrivial).eventTrace := by
  simp only [gates, List.map_append, FoldProgram.foldProgram_gates_trace,
    List.map_flatten, List.map_replicate, ClockDecode.clockDecode_gates_trace,
    OutputCorrection.outputCorrection_gates_trace, program, DecodedSchedule.program,
    NativeSchedule.program, InitialFrame.program, UnitaryCircuit.seq_eventTrace,
    FoldProgram.foldProgram_nativeProgram_trace,
    OutputCorrection.outputCorrection_nativeProgram_trace, UnitaryCircuit.iterate_eventTrace,
    NativeMicrostep.program, InitialLengthWrite.program, programList_eventTrace]

/-- The emitted schedule has exactly the chronological trace of the original program. -/
theorem correctedSchedule_nativeProgram_trace (modulus : Nat) (nontrivial : 1 < modulus) :
    (nativeProgram modulus nontrivial).eventTrace = (program modulus nontrivial).eventTrace := by
  rw [nativeProgram, programList_eventTrace, correctedSchedule_gates_trace]

end

end QuantumAlg.MAU.Inversion.SharedEEA.CorrectedSchedule
