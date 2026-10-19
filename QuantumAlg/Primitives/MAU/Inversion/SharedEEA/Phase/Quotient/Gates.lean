/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Phase.Quotient
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Quotient.Increment.Gates

/-!
# Literal phase-selected quotient word with original predicate cleanup

Two phase CNOTs surround the original direction complements and actual placed
HRS list. The complete original Ctrl and dirty Work1 return unchanged.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.PhaseQuotient

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit GateSpec NativePredicate

private def bodyGates (width : Nat) : List (GateSpec (encoding width)) :=
  QuotientComplement.gates width ++ QuotientIncrement.gates width ++ QuotientComplement.gates width

private lemma bodyGates_step (width : Nat) (state : Registers width) :
    stepList (bodyGates width) state = bodyStep state := by
  rw [bodyGates, stepList_append, stepList_append, QuotientComplement.gates_step,
    QuotientIncrement.quotientIncrement_gates_step, QuotientComplement.gates_step]
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨p1, p2, sign, iteration⟩, control⟩
  cases p1 <;> cases control <;>
    simp only [QuotientComplement.step, QuotientIncrement.step, bodyStep,
      Bool.false_eq_true, if_false, if_true, BitVec.not_not,
      QuotientComplement.complement_increment]

/-- Original phase predicate, direction-selected increment, and literal inverse predicate. -/
def gates (width : Nat) : List (GateSpec (encoding width)) :=
  guardGates width ++ bodyGates width ++ (guardGates width).reverse

/-- Complete finite quotient action and Ctrl cleanup hold for every original frame label. -/
lemma phaseQuotient_gates_step (width : Nat) (state : Registers width) :
    stepList (gates width) state = step state := by
  rw [gates, stepList_append, stepList_append, guard_step, bodyGates_step,
    guard_reverse_step, body_computed, condition_xorControl, condition_step, xorControl_twice]

/-- Execute the complete literal phase-selected word on the original physical frame. -/
def nativeProgram (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (gates width)

/-- Exact full-frame amplitudes include arbitrary dirty work and the zero-width case. -/
lemma phaseQuotient_nativeProgram_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (nativeProgram width) environment step :=
  realizesList_congrStep (QubitLayout.canonical _) .empty _ (phaseQuotient_gates_step width)
    environment

/-- Every predicate, complement and native HRS instruction retains its original trace position. -/
lemma phaseQuotient_gates_trace (width : Nat) :
    (gates width).map (event .empty) = (program width).eventTrace := by
  simp only [gates, bodyGates, List.map_append, program, bodyProgram,
    UnitaryCircuit.seq_eventTrace, programList_eventTrace, QuotientComplement.program,
    QuotientIncrement.quotientIncrement_gates_trace, List.append_assoc]

/-- The consumer's actual emitted word retains the exact original ordered event trace. -/
lemma phaseQuotient_nativeProgram_trace (width : Nat) :
    (nativeProgram width).eventTrace = (program width).eventTrace := by
  rw [nativeProgram, programList_eventTrace, phaseQuotient_gates_trace]

/-- Sequential native depth counts every original predicate, complement and HRS instruction. -/
lemma phaseQuotient_nativeProgram_unitDepth (width : Nat) :
    (nativeProgram width).evaluatedEventDepth (fun _ => 1) =
      (LowShiftIncrement.program width).eventTrace.length + 2 * width.size + 4 := by
  have count := congrArg List.length (phaseQuotient_nativeProgram_trace width)
  rw [nativeProgram, programList_eventTrace, List.length_map, program_eventTrace_length] at count
  rw [nativeProgram, programList_evaluatedEventDepth_unit, count]

/-- The complete native event pool is inherited from the same original quotient computation. -/
lemma phaseQuotient_gates_eventCost (width : Nat) :
    ResourcePool.ofList ((gates width).map (event .empty)) = (program width).eventCost := by
  rw [phaseQuotient_gates_trace, UnitaryCircuit.ofList_eventTrace_eq_eventCost]

end

end QuantumAlg.MAU.Inversion.SharedEEA.PhaseQuotient
