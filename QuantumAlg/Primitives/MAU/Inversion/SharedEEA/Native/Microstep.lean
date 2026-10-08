/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Guarded.Shift.Gates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Blocks.Gates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.SignQuotient.Gates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Control
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ZeroShiftControl
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Terminal.Boundary

/-!
# One actual source-ordered native shared-register microstep

The single unitary below executes pre-shifts, remainder arithmetic, the
corrected Sign/quotient exchange, coefficient arithmetic, post-shifts,
ordered phase updates, zero-shift phase complements, and the full boundary
exchange/length-refresh/Iter instruction
[LYL+26, sec_EEA/sub_opt.tex:37-84;
sec_EEA/sub_regshare.tex:281-296,303-313]. Every component is an
already specified actual elementary gate program on the same full frame.
The Sign selector retains the baseline source's corrected physical offset.

The exact action is defined on every original register label. Its internally reachable
trajectory restores prepared Ctrl, including the boundary whose divisor
length and high-clock source bits can change. A modulus greater than one
supplies the static zero-test width internally.

This module proves physical composition and operation order of the repaired
complete-clock body. Packed-state refinement and the independent fixed
schedule belong to its actual trajectory consumers; no all-input Ctrl
cleanup is asserted here. Active Work1 padding remains unrestricted.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.NativeMicrostep

noncomputable section

open EncodedBit GateSpec

/-- The complete native instruction word in the original eight-block source order. -/
def gates (width : Nat) (enough : 2 ≤ width.size) : List (GateSpec (encoding width)) :=
  GuardedShift.gates width false ++ ArithmeticBlocks.remainderGates width ++
    SignQuotient.gates width ++ ArithmeticBlocks.coefficientGates width ++
    GuardedShift.gates width true ++ NativeControl.gates width enough ++
    ZeroShiftControl.gates width enough ++ TerminalBoundary.gates width enough

/-- Execute the actual complete literal native word on the original register frame. -/
def program (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (gates width enough)

/-- Complete action of the same eight actual blocks, including arbitrary incoming Ctrl. -/
def step (width : Nat) (state : Registers width) : Registers width :=
  TerminalBoundary.step (ZeroShiftControl.step (NativeControl.step
    (GuardedShift.step true (ArithmeticBlocks.coefficientStep width
      (SignQuotient.step width (ArithmeticBlocks.remainderStep width
        (GuardedShift.step false state)))))))

/-- Every complete original frame follows all eight actual blocks without a work premise. -/
theorem nativeMicrostep_gates_step (width : Nat) (enough : 2 ≤ width.size)
    (state : Registers width) : stepList (gates width enough) state = step width state := by
  simp only [gates, stepList_append, GuardedShift.guardedShift_gates_step,
    ArithmeticBlocks.arithmeticBlocks_remainderGates_step, SignQuotient.signQuotient_gates_step,
    ArithmeticBlocks.arithmeticBlocks_coefficientGates_step, NativeControl.gates_step,
    ZeroShiftControl.gates_step, TerminalBoundary.gates_step]
  rfl

/-- Full-label realization of the literal native word preserves all amplitudes and phases. -/
theorem program_realizes (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit.Realizes (encoding width) (program width enough) (step width) :=
  realizesList_congrStep (QubitLayout.canonical _) .empty _
    (nativeMicrostep_gates_step width enough)

/-- The actual finite microstep is injective on every complete original frame. -/
theorem step_injective (width : Nat) (enough : 2 ≤ width.size) :
    Function.Injective (step width) :=
  (program_realizes width enough).injective

/-- The actual inverse circuit restores every normalized state, beyond individual basis labels. -/
theorem dagger_after_forward (width : Nat) (enough : 2 ≤ width.size)
    (state : NormalizedVector (QubitLayout.canonical (encoding width).width).toQuantum.register) :
    ((program width enough).dagger (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized
      ((program width enough).applyNormalized state) =
      state :=
  UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized (program width enough)
    ((program width enough).dagger (AlgorithmGate.oracleFreeAdjoints .empty))
    (by rw [UnitaryCircuit.dagger_matrix]; exact Unitary.star_eq_inv _) state

/-- Every source block contributes its complete actual event list in the literal execution order. -/
theorem program_eventTrace (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).eventTrace =
      (GuardedShift.program width false).eventTrace ++
        (ArithmeticBlocks.remainderProgram width).eventTrace ++
          (SignQuotient.program width).eventTrace ++
            (ArithmeticBlocks.coefficientProgram width).eventTrace ++
              (GuardedShift.program width true).eventTrace ++
                (NativeControl.program width enough).eventTrace ++
                  (ZeroShiftControl.program width enough).eventTrace ++
                    (TerminalBoundary.program width enough).eventTrace := by
  simp only [program, programList_eventTrace, gates, List.map_append,
    GuardedShift.guardedShift_gates_trace, ArithmeticBlocks.arithmeticBlocks_remainderGates_trace,
    SignQuotient.signQuotient_gates_trace,
    ArithmeticBlocks.arithmeticBlocks_coefficientGates_trace,
    NativeControl.program, ZeroShiftControl.program, TerminalBoundary.program, List.append_assoc]

/-- Reversing the same actual primitive list restores every complete original input frame. -/
theorem nativeMicrostep_reverseGates_restores (width : Nat) (enough : 2 ≤ width.size)
    (state : Registers width) :
    stepList (gates width enough).reverse (step width state) = state := by
  rw [← nativeMicrostep_gates_step width enough state]
  exact stepList_reverse_stepList _ state

/-- The complete sequential native microstep has exactly one unit of depth per emitted gate. -/
theorem nativeMicrostep_program_unitDepth (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).evaluatedEventDepth (fun _ => 1) = (gates width enough).length := by
  rw [program, programList_evaluatedEventDepth_unit]

end

end QuantumAlg.MAU.Inversion.SharedEEA.NativeMicrostep
