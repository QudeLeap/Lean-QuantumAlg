/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Microstep.Program

/-!
# Actual first seven source blocks before the complete terminal boundary

This native prefix keeps all original arithmetic, shifts and phase gates,
with their complete pool cleanup. It is not yet a replacement microstep:
omitting the final boundary requires an independently proved source-state
identity at every static omitted position.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeMicrostep

noncomputable section

/-- Independent original action before the last boundary predicate is computed. -/
def bodyStep (width : Nat) (state : Registers width) : Registers width :=
  ZeroShiftControl.step (NativeControl.step
    (GuardedShift.step true (SharedEEA.ArithmeticBlocks.coefficientStep width
      (SharedEEA.SignQuotient.step width (SharedEEA.ArithmeticBlocks.remainderStep width
        (GuardedShift.step false state))))))

/-- The original complete source action still contains its entire final boundary. -/
lemma source_step_eq_boundary (width : Nat) (state : Registers width) :
    SharedEEA.NativeMicrostep.step width state =
      SharedEEA.TerminalBoundary.step (bodyStep width state) := rfl

/-- All seven actual original component actions restore the incoming Ctrl value. -/
lemma bodyStep_control (width : Nat) (state : Registers width) :
    (bodyStep width state).control = state.control := by
  change (GuardedShift.step true (SharedEEA.ArithmeticBlocks.coefficientStep width
    (SharedEEA.SignQuotient.step width (SharedEEA.ArithmeticBlocks.remainderStep width
      (GuardedShift.step false state))))).control = state.control
  rw [GuardedShift.step_control, SharedEEA.ArithmeticBlocks.coefficientStep_control,
    SharedEEA.SignQuotient.step_control, SharedEEA.ArithmeticBlocks.remainderStep_control,
    GuardedShift.step_control]

/-- Actual native seven-block prefix, retaining the same entire physical frame. -/
def bodyProgram (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (shiftProgram width false).seq
    ((ArithmeticBlocks.remainderProgram width (positive_of_enough width enough)).seq
      ((SignQuotient.program width).seq
        ((ArithmeticBlocks.coefficientProgram width (positive_of_enough width enough)).seq
          ((shiftProgram width true).seq
            ((controlProgram width enough).seq (zeroProgram width enough))))))

/-- The actual prefix has its complete original action and returns every initialized pool bit. -/
lemma bodyProgram_apply_source (width : Nat) (enough : 2 ≤ width.size)
    (environment : OracleModel.empty.Interpretation)
    (state : Data width) (prefixZero : state.2.2.1 = 0) (addressZero : state.2.1 = 0)
    (borrowZero : state.2.2.2 = false) (control : state.1.control = false) :
    (bodyProgram width enough).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (bodyStep width state.1, state.2))) := by
  let first : Data width := (GuardedShift.step false state.1, state.2)
  let second : Data width :=
    (SharedEEA.ArithmeticBlocks.remainderStep width first.1, state.2)
  let third : Data width := (SharedEEA.SignQuotient.step width second.1, state.2)
  let fourth : Data width :=
    (SharedEEA.ArithmeticBlocks.coefficientStep width third.1, state.2)
  let fifth : Data width := (GuardedShift.step true fourth.1, state.2)
  let sixth : Data width := (NativeControl.step fifth.1, state.2)
  let seventh : Data width := (ZeroShiftControl.step sixth.1, state.2)
  let ket (value : Data width) := NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
    ((encoding width).encode value))
  have firstControl : first.1.control = false :=
    (GuardedShift.step_control width false state.1).trans control
  have secondControl : second.1.control = false :=
    (SharedEEA.ArithmeticBlocks.remainderStep_control width first.1).trans firstControl
  have thirdControl : third.1.control = false :=
    (SharedEEA.SignQuotient.step_control width second.1).trans secondControl
  have firstActual := (shiftProgram_realizes width false environment).apply_encoded_ket state
  have secondActual := remainderProgram_apply_original width (positive_of_enough width enough)
    environment first prefixZero borrowZero addressZero firstControl
  have thirdActual := signProgram_apply_original width environment second addressZero prefixZero
    secondControl
  have fourthActual := coefficientProgram_apply_original width (positive_of_enough width enough)
    environment third prefixZero borrowZero addressZero thirdControl
  have fifthActual := (shiftProgram_realizes width true environment).apply_encoded_ket fourth
  have sixthActual := (controlProgram_realizes width enough environment).apply_encoded_ket fifth
  have seventhActual := (zeroProgram_realizes width enough environment).apply_encoded_ket sixth
  change (shiftProgram width false).applyNormalized environment (ket state) =
    ket first at firstActual
  change (ArithmeticBlocks.remainderProgram width (positive_of_enough width enough)).applyNormalized
    environment (ket first) = ket second at secondActual
  change (SignQuotient.program width).applyNormalized environment (ket second) =
    ket third at thirdActual
  change
    (ArithmeticBlocks.coefficientProgram width (positive_of_enough width enough)).applyNormalized
      environment (ket third) = ket fourth at fourthActual
  change (shiftProgram width true).applyNormalized environment (ket fourth) =
    ket fifth at fifthActual
  change (controlProgram width enough).applyNormalized environment (ket fifth) =
    ket sixth at sixthActual
  change (zeroProgram width enough).applyNormalized environment (ket sixth) =
    ket seventh at seventhActual
  change (bodyProgram width enough).applyNormalized environment (ket state) =
    ket (bodyStep width state.1, state.2)
  rw [bodyProgram, UnitaryCircuit.applyNormalized_seq, firstActual,
    UnitaryCircuit.applyNormalized_seq, secondActual, UnitaryCircuit.applyNormalized_seq,
    thirdActual, UnitaryCircuit.applyNormalized_seq, fourthActual,
    UnitaryCircuit.applyNormalized_seq, fifthActual, UnitaryCircuit.applyNormalized_seq,
    sixthActual, seventhActual]
  rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeMicrostep
