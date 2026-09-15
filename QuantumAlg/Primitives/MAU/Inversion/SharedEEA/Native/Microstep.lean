/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Guarded.Shift
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Blocks
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.SignQuotient
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

/-- The actual single native microstep, in the source's execution order. -/
def program (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  (GuardedShift.program width false).seq
    ((ArithmeticBlocks.remainderProgram width).seq
      ((SignQuotient.program width).seq
        ((ArithmeticBlocks.coefficientProgram width).seq
          ((GuardedShift.program width true).seq
            ((NativeControl.program width enough).seq
              ((ZeroShiftControl.program width enough).seq
                (TerminalBoundary.program width enough)))))))

/-- Complete action of the same eight actual blocks, including arbitrary incoming Ctrl. -/
def step (width : Nat) (state : Registers width) : Registers width :=
  TerminalBoundary.step (ZeroShiftControl.step (NativeControl.step
    (GuardedShift.step true (ArithmeticBlocks.coefficientStep width
      (SignQuotient.step width (ArithmeticBlocks.remainderStep width
        (GuardedShift.step false state)))))))

/-- Full-label realization composes the actual subprograms without losing relative phases. -/
theorem program_realizes (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit.Realizes (encoding width) (program width enough) (step width) :=
  (GuardedShift.program_realizes width false).seq
    ((ArithmeticBlocks.remainderProgram_realizes width).seq
      ((SignQuotient.program_realizes width).seq
        ((ArithmeticBlocks.coefficientProgram_realizes width).seq
          ((GuardedShift.program_realizes width true).seq
            ((NativeControl.program_realizes width enough).seq
              ((ZeroShiftControl.program_realizes width enough).seq
                (TerminalBoundary.program_realizes width enough)))))))

/-- The actual finite microstep is injective on every complete original frame. -/
theorem step_injective (width : Nat) (enough : 2 ≤ width.size) :
    Function.Injective (step width) :=
  (program_realizes width enough).injective

/-- The actual inverse circuit restores every normalized state, beyond individual basis labels. -/
theorem dagger_after_forward (width : Nat) (enough : 2 ≤ width.size)
    (state : NormalizedVector (Qubits (encoding width).width)) :
    (program width enough).dagger.applyNormalized ((program width enough).applyNormalized state) =
      state :=
  UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized (program width enough) state

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
  simp only [program, UnitaryCircuit.seq_eventTrace, List.append_assoc]

end

end QuantumAlg.MAU.Inversion.SharedEEA.NativeMicrostep
