/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Quotient.Increment
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Quotient.Complement
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Predicate

/-!
# Actual phase-selected quotient arithmetic with complete Ctrl cleanup

When Phase1 xor Phase2 is one, the source increments quotient length for
Phase1 zero and decrements it for Phase1 one
[LYL+26, sec_EEA/sub_opt.tex:52-59]. Two actual CNOTs compute this xor into
the existing Ctrl. Phase1-controlled quotient complements surround one
actual HRS incrementer; the exact finite identity proved in the complement
owner changes that increment into decrement on the selected direction.
The two original predicate CNOTs are then executed in reverse order.

The program retains arbitrary borrowed Work1 contents and the original
Ctrl on every label. Its source specialization uses the algorithm's
internal Ctrl-zero invariant. Both complements also execute on the closed
branch and cancel exactly; their events are still counted. This is the
quotient update fragment: the preceding location-controlled Sign/word-bit
exchange and the other arithmetic blocks remain separate actual programs.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.PhaseQuotient

noncomputable section

open EncodedBit NativePredicate

/-- Read the source condition from the two actual retained phase bits. -/
def condition {width : Nat} (state : Registers width) : Bool :=
  state.flags.first ^^ state.flags.second

private theorem first_control (width : Nat) :
    (phase1Bit width).wire ≠ (controlBit width).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [phase1Bit_wire, controlBit_wire] at values
  omega

private theorem second_control (width : Nat) :
    (phase2Bit width).wire ≠ (controlBit width).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [phase2Bit_wire, controlBit_wire] at values
  omega

/-- Two actual CNOTs compute the source xor without changing either phase bit. -/
def guardGates (width : Nat) : List (GateSpec (encoding width)) :=
  [.cnot (phase1Bit width) (controlBit width) (first_control width),
    .cnot (phase2Bit width) (controlBit width) (second_control width)]

private theorem guard_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (guardGates width) state = xorControl (condition state) state := by
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨p1, p2, sign, iteration⟩, control⟩
  cases p1 <;> cases p2 <;> cases control <;> rfl

private theorem guard_reverse_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (guardGates width).reverse state = xorControl (condition state) state := by
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨p1, p2, sign, iteration⟩, control⟩
  cases p1 <;> cases p2 <;> cases control <;> rfl

private def bodyProgram (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  (QuotientComplement.program width).seq
    ((QuotientIncrement.program width).seq (QuotientComplement.program width))

private def bodyStep {width : Nat} (state : Registers width) : Registers width :=
  { state with quotientLength :=
      (if state.control then
        if state.flags.first then state.quotientLength - 1 else state.quotientLength + 1
      else state.quotientLength) }

private theorem body_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (bodyProgram width) bodyStep :=
  ((QuotientComplement.program_realizes width).seq
    ((QuotientIncrement.program_realizes width).seq
      (QuotientComplement.program_realizes width))).congrStep (by
    intro state
    rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
      ⟨p1, p2, sign, iteration⟩, control⟩
    cases p1 <;> cases control <;>
      simp only [QuotientComplement.step, QuotientIncrement.step, bodyStep,
        Bool.false_eq_true, if_false, if_true, BitVec.not_not,
        QuotientComplement.complement_increment])

/-- Full frame action of the computed-xor selection, retaining the old Ctrl. -/
def step {width : Nat} (state : Registers width) : Registers width :=
  { state with quotientLength :=
      (if state.control ^^ condition state then
        if state.flags.first then state.quotientLength - 1 else state.quotientLength + 1
      else state.quotientLength) }

private theorem condition_xorControl {width : Nat} (value : Bool) (state : Registers width) :
    condition (xorControl value state) = condition state := rfl

private theorem condition_step {width : Nat} (state : Registers width) :
    condition (step state) = condition state := rfl

private theorem body_computed {width : Nat} (state : Registers width) :
    bodyStep (xorControl (condition state) state) =
      xorControl (condition state) (step state) := rfl

/-- Compute the actual phase xor, execute direction-selected arithmetic, and reverse the xor. -/
def program (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  (GateSpec.programList (guardGates width)).seq
    ((bodyProgram width).seq (GateSpec.programList (guardGates width).reverse))

/-- Exact complete native action, including arbitrary incoming work and restored Ctrl. -/
theorem program_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (program width) step :=
  ((GateSpec.realizesList_congrStep _ (guard_step width)).seq
    ((body_realizes width).seq
      (GateSpec.realizesList_congrStep _ (guard_reverse_step width)))).congrStep (by
    intro state
    rw [body_computed, condition_xorControl, condition_step, xorControl_twice])

/-- The retained source flags select increment or decrement in the source's actual order. -/
def sourceStep {width : Nat} (state : Registers width) : Registers width :=
  { state with quotientLength :=
      (if condition state then
        if state.flags.first then state.quotientLength - 1 else state.quotientLength + 1
      else state.quotientLength) }

/-- Internal initialization specializes the full native action to the original source guard. -/
theorem step_eq_sourceStep {width : Nat} (state : Registers width)
    (preparedControl : state.control = false) : step state = sourceStep state := by
  simp only [step, preparedControl, Bool.false_xor, sourceStep]

/-- The source action is performed by this actual program on the internally prepared subspace. -/
theorem program_apply_prepared (width : Nat) (state : Registers width)
    (preparedControl : state.control = false) :
    (program width).applyNormalized (NormalizedVector.ket ((encoding width).encode state)) =
      NormalizedVector.ket ((encoding width).encode (sourceStep state)) := by
  rw [(program_realizes width).apply_encoded_ket, step_eq_sourceStep state preparedControl]

/-- Every borrowed word, other length, and original phase/control bit is retained. -/
theorem step_retained {width : Nat} (state : Registers width) :
    (step state).firstWord = state.firstWord ∧
      (step state).secondWord = state.secondWord ∧
      (step state).coefficientLength = state.coefficientLength ∧
      (step state).divisorLength = state.divisorLength ∧
      (step state).shift = state.shift ∧ (step state).flags = state.flags ∧
      (step state).control = state.control :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem guard_trace (width : Nat) :
    (GateSpec.programList (guardGates width)).eventTrace =
      [.gate (.builtin "cnot"), .gate (.builtin "cnot")] := by
  rw [GateSpec.programList_eventTrace]
  rfl

private theorem guard_reverse_trace (width : Nat) :
    (GateSpec.programList (guardGates width).reverse).eventTrace =
      [.gate (.builtin "cnot"), .gate (.builtin "cnot")] := by
  rw [GateSpec.programList_eventTrace]
  rfl

/-- Every predicate and complement CNOT surrounds the single original HRS event trace. -/
theorem program_eventTrace (width : Nat) :
    (program width).eventTrace =
      [.gate (.builtin "cnot"), .gate (.builtin "cnot")] ++
        List.replicate width.size (.gate (.builtin "cnot")) ++
          (LowShiftIncrement.program width).eventTrace ++
            List.replicate width.size (.gate (.builtin "cnot")) ++
              [.gate (.builtin "cnot"), .gate (.builtin "cnot")] := by
  simp only [program, bodyProgram, UnitaryCircuit.seq_eventTrace, guard_trace,
    guard_reverse_trace, QuotientComplement.program_eventTrace,
    QuotientIncrement.program_eventTrace, List.append_assoc]

/-- The actual event count includes both complements and both complete phase-xor passes. -/
theorem program_eventTrace_length (width : Nat) :
    (program width).eventTrace.length =
      (LowShiftIncrement.program width).eventTrace.length + 2 * width.size + 4 := by
  rw [program_eventTrace]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.PhaseQuotient
