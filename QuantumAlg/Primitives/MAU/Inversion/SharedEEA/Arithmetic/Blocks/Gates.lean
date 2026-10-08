/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Blocks
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Schedule.Gates

/-!
# Literal complete remainder and coefficient instruction words

Each source block concatenates its original finite selector schedules and
intervening Sign gates, retaining every borrowed-work and predicate cleanup.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticBlocks

noncomputable section

open EncodedBit GateSpec

/-- Complete signed remainder subtraction, Sign complement, and selected add-back. -/
def remainderGates (width : Nat) : List (GateSpec (encoding width)) :=
  ArithmeticSchedule.gates width .remainderSubtract ++ ArithmeticSign.remainderGates width ++
    ArithmeticSchedule.gates width .remainderAddback

/-- Complete coefficient low subtraction, Sign complement, and signed addition. -/
def coefficientGates (width : Nat) : List (GateSpec (encoding width)) :=
  ArithmeticSchedule.gates width .coefficientSubtract ++ ArithmeticSign.coefficientGates width ++
    ArithmeticSchedule.gates width .coefficientAdd

/-- Exact complete remainder action includes arbitrary incoming Ctrl and borrowed Iter. -/
theorem arithmeticBlocks_remainderGates_step (width : Nat) (state : Registers width) :
    stepList (remainderGates width) state = remainderStep width state := by
  rw [remainderGates, stepList_append, stepList_append,
    ArithmeticSchedule.arithmeticSchedule_gates_step, ArithmeticSign.remainderGates_step,
    ArithmeticSchedule.arithmeticSchedule_gates_step]
  rfl

/-- Exact complete coefficient action restores every original dirty-work bit. -/
theorem arithmeticBlocks_coefficientGates_step (width : Nat) (state : Registers width) :
    stepList (coefficientGates width) state = coefficientStep width state := by
  rw [coefficientGates, stepList_append, stepList_append,
    ArithmeticSchedule.arithmeticSchedule_gates_step, ArithmeticSign.coefficientGates_step,
    ArithmeticSchedule.arithmeticSchedule_gates_step]
  rfl

/-- The complete emitted remainder word preserves every basis amplitude and relative phase. -/
theorem arithmeticBlocks_remainderGates_realizes (width : Nat)
    (layout : QubitLayout (encoding width).width) :
    UnitaryCircuit.Realizes (layout := layout) (encoding width)
      (programList layout .empty (remainderGates width)) (remainderStep width) :=
  realizesList_congrStep layout .empty _ (arithmeticBlocks_remainderGates_step width)

/-- The complete coefficient word realizes the original full-frame source-order action. -/
theorem arithmeticBlocks_coefficientGates_realizes (width : Nat)
    (layout : QubitLayout (encoding width).width) :
    UnitaryCircuit.Realizes (layout := layout) (encoding width)
      (programList layout .empty (coefficientGates width)) (coefficientStep width) :=
  realizesList_congrStep layout .empty _ (arithmeticBlocks_coefficientGates_step width)

/-- Every remainder event retains its original order through both complete selectors. -/
theorem arithmeticBlocks_remainderGates_trace (width : Nat) :
    (remainderGates width).map (event .empty) = (remainderProgram width).eventTrace := by
  simp only [remainderGates, List.map_append, ArithmeticSchedule.arithmeticSchedule_gates_trace,
    remainderProgram, UnitaryCircuit.seq_eventTrace, ArithmeticSign.remainderProgram,
    programList_eventTrace, List.append_assoc]

/-- Every coefficient event retains its original order through both complete selectors. -/
theorem arithmeticBlocks_coefficientGates_trace (width : Nat) :
    (coefficientGates width).map (event .empty) = (coefficientProgram width).eventTrace := by
  simp only [coefficientGates, List.map_append, ArithmeticSchedule.arithmeticSchedule_gates_trace,
    coefficientProgram, UnitaryCircuit.seq_eventTrace, ArithmeticSign.coefficientProgram,
    programList_eventTrace, List.append_assoc]

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticBlocks
