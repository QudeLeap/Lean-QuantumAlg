/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Parallel.Arithmetic.Execution
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Parallel.Body

/-!
# Direct independent source semantics of the actual seven-block paired body

The result uses the original current-field mathematical instructions,
without defining a new specification by the old selector fold. Actual
shift, arithmetic, Sign/quotient and phase components execute in their
unchanged source order on the same full source and physical pool.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledParallel

noncomputable section

private def arithmeticSource (width : Nat) (coefficient : Bool) :
    Registers width → Registers width :=
  if coefficient then SharedEEA.ArithmeticBlocks.coefficientSource
  else SharedEEA.ArithmeticBlocks.remainderSource

private lemma arithmeticSource_control (width : Nat) (coefficient : Bool)
    (state : Registers width) (control : state.control = false) :
    (arithmeticSource width coefficient state).control = false := by
  cases coefficient
  · change (SharedEEA.ArithmeticBlocks.remainderSource state).control = false
    rw [← SharedEEA.ArithmeticBlocks.remainderStep_eq_source width state control,
      SharedEEA.ArithmeticBlocks.remainderStep_control]
    exact control
  · change (SharedEEA.ArithmeticBlocks.coefficientSource state).control = false
    rw [← SharedEEA.ArithmeticBlocks.coefficientStep_eq_source width state control,
      SharedEEA.ArithmeticBlocks.coefficientStep_control]
    exact control

private lemma signSource_control (width : Nat) (state : Registers width)
    (control : state.control = false) :
    (SharedEEA.SignQuotient.sourceStep width state).control = false := by
  rw [← SharedEEA.SignQuotient.step_eq_sourceStep width state control,
    SharedEEA.SignQuotient.step_control]
  exact control

/-- Independent original mathematical operations before the final boundary. -/
def bodySource (width : Nat) (source : Registers width) : Registers width :=
  ZeroShiftControl.step (NativeControl.step
    (GuardedShift.step true (arithmeticSource width true
      (SharedEEA.SignQuotient.sourceStep width
        (arithmeticSource width false (GuardedShift.step false source))))))

private lemma bodySource_eq (width : Nat) :
    bodySource width =
      (fun source => ZeroShiftControl.step (NativeControl.step
        (GuardedShift.step true (arithmeticSource width true
          (SharedEEA.SignQuotient.sourceStep width
            (arithmeticSource width false (GuardedShift.step false source))))))) := rfl

/-- External selection retains the entire original shared pool and both external bits. -/
def bodyStep (width : Nat) : ControlledFrame.Data width → ControlledFrame.Data width :=
  ControlledSource.step width (bodySource width)

private lemma bodySource_eq_native (width : Nat) (state : Registers width)
    (control : state.control = false) :
    bodySource width state = NativeMicrostep.bodyStep width state := by
  have firstControl := (GuardedShift.step_control width false state).trans control
  have remainder := SharedEEA.ArithmeticBlocks.remainderStep_eq_source width
    (GuardedShift.step false state) firstControl
  have secondControl := arithmeticSource_control width false
    (GuardedShift.step false state) firstControl
  have sign := SharedEEA.SignQuotient.step_eq_sourceStep width
    (arithmeticSource width false (GuardedShift.step false state)) secondControl
  have thirdControl := signSource_control width
    (arithmeticSource width false (GuardedShift.step false state)) secondControl
  have coefficient := SharedEEA.ArithmeticBlocks.coefficientStep_eq_source width
    (SharedEEA.SignQuotient.sourceStep width
      (arithmeticSource width false (GuardedShift.step false state))) thirdControl
  simp only [arithmeticSource, Bool.false_eq_true, if_false] at sign coefficient
  unfold bodySource NativeMicrostep.bodyStep
  simp only [arithmeticSource, Bool.false_eq_true, if_false, if_true]
  rw [remainder, sign, coefficient]

lemma bodyStep_control (width : Nat) (state : ControlledFrame.Data width)
    (control : state.1.1.control = false) : (bodyStep width state).1.1.control = false := by
  unfold bodyStep ControlledSource.step
  split
  · rw [bodySource_eq_native width state.1.1 control, NativeMicrostep.bodyStep_control]
    exact control
  · exact control

private lemma arithmeticProgram_apply_source (width : Nat) (positive : 1 ≤ width)
    (coefficient : Bool) (environment : OracleModel.empty.Interpretation)
    (state : ControlledFrame.Data width)
    (prefixZero : state.1.2.2.1 = 0) (addressZero : state.1.2.1 = 0)
    (borrowZero : state.1.2.2.2 = false) (control : state.1.1.control = false) :
    (arithmeticProgram width positive coefficient).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode
          (ControlledSource.step width (arithmeticSource width coefficient) state))) :=
  arithmeticProgram_apply_encoded_ket width positive coefficient environment state
    prefixZero borrowZero addressZero control

private lemma signProgram_apply_source (width : Nat)
    (environment : OracleModel.empty.Interpretation) (state : ControlledFrame.Data width)
    (prefixZero : state.1.2.2.1 = 0) (addressZero : state.1.2.1 = 0)
    (control : state.1.1.control = false) :
    (ControlledSignQuotient.program width).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode
          (ControlledSource.step width (SharedEEA.SignQuotient.sourceStep width) state))) :=
  ControlledSignQuotient.program_apply_encoded_ket width environment state
    addressZero prefixZero control

/-- Full native seven-block semantics retain the same original source, pool and external frame. -/
lemma bodyProgram_apply_source (width : Nat) (enough : 2 ≤ width.size)
    (environment : OracleModel.empty.Interpretation) (state : ControlledFrame.Data width)
    (prefixZero : state.1.2.2.1 = 0) (addressZero : state.1.2.1 = 0)
    (borrowZero : state.1.2.2.2 = false) (control : state.1.1.control = false) :
    (bodyProgram width enough).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode (bodyStep width state))) := by
  let first := ControlledSource.step width (GuardedShift.step false) state
  let second := ControlledSource.step width (arithmeticSource width false) first
  let third := ControlledSource.step width (SharedEEA.SignQuotient.sourceStep width) second
  let fourth := ControlledSource.step width (arithmeticSource width true) third
  let fifth := ControlledSource.step width (GuardedShift.step true) fourth
  let sixth := ControlledSource.step width NativeControl.step fifth
  let seventh := ControlledSource.step width ZeroShiftControl.step sixth
  let ket (value : ControlledFrame.Data width) :=
    NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((ControlledFrame.encoding width).encode value))
  have firstControl : first.1.1.control = false :=
    (ControlledSource.step_control width _ (GuardedShift.step_control width false) state).trans
      control
  have secondControl : second.1.1.control = false :=
    by
      change (if first.2.1 then arithmeticSource width false first.1.1
        else first.1.1).control = false
      split
      · exact arithmeticSource_control width false first.1.1 firstControl
      · exact firstControl
  have thirdControl : third.1.1.control = false :=
    by
      change (if second.2.1 then SharedEEA.SignQuotient.sourceStep width second.1.1
        else second.1.1).control = false
      split
      · exact signSource_control width second.1.1 secondControl
      · exact secondControl
  have fourthControl : fourth.1.1.control = false :=
    by
      change (if third.2.1 then arithmeticSource width true third.1.1
        else third.1.1).control = false
      split
      · exact arithmeticSource_control width true third.1.1 thirdControl
      · exact thirdControl
  have firstActual := ControlledShiftBlock.program_apply_encoded_ket width false environment
    state control
  have secondActual := arithmeticProgram_apply_source width
    (NativeMicrostep.positive_of_enough width enough) false environment first
    prefixZero addressZero borrowZero firstControl
  have thirdActual := signProgram_apply_source width environment second
    prefixZero addressZero secondControl
  have fourthActual := arithmeticProgram_apply_source width
    (NativeMicrostep.positive_of_enough width enough) true environment third
    prefixZero addressZero borrowZero thirdControl
  have fifthActual := ControlledShiftBlock.program_apply_encoded_ket width true environment
    fourth fourthControl
  have sixthActual :=
    (ControlledPhaseUpdates.program_realizes width enough false environment).apply_encoded_ket fifth
  have seventhActual :=
    (ControlledPhaseUpdates.program_realizes width enough true environment).apply_encoded_ket sixth
  change (ControlledShiftBlock.program width false).applyNormalized environment (ket state) =
    ket first at firstActual
  change (ControlledShiftBlock.program width true).applyNormalized environment (ket fourth) =
    ket fifth at fifthActual
  change (ControlledPhaseUpdates.program width enough false).applyNormalized environment
    (ket fifth) = ket sixth at sixthActual
  change (ControlledPhaseUpdates.program width enough true).applyNormalized environment
    (ket sixth) = ket seventh at seventhActual
  have actual := UnitaryCircuit.applyNormalized_seq_of_eq firstActual
    (UnitaryCircuit.applyNormalized_seq_of_eq secondActual
      (UnitaryCircuit.applyNormalized_seq_of_eq thirdActual
        (UnitaryCircuit.applyNormalized_seq_of_eq fourthActual
          (UnitaryCircuit.applyNormalized_seq_of_eq fifthActual
            (UnitaryCircuit.applyNormalized_seq_of_eq sixthActual seventhActual)))))
  change (bodyProgram width enough).applyNormalized environment (ket state) = ket seventh at actual
  change (bodyProgram width enough).applyNormalized environment (ket state) =
    ket (bodyStep width state)
  simpa only [first, second, third, fourth, fifth, sixth, seventh, bodyStep,
    bodySource_eq, ControlledSource.step_step] using actual

/-- An inactive external control accepts every original source value, including zero input. -/
lemma bodyProgram_apply_disabled (width : Nat) (enough : 2 ≤ width.size)
    (environment : OracleModel.empty.Interpretation) (state : ControlledFrame.Data width)
    (prefixZero : state.1.2.2.1 = 0) (addressZero : state.1.2.1 = 0)
    (borrowZero : state.1.2.2.2 = false) (control : state.1.1.control = false)
    (disabled : state.2.1 = false) :
    (bodyProgram width enough).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode state)) := by
  have actual := bodyProgram_apply_source width enough environment state
    prefixZero addressZero borrowZero control
  rw [bodyStep, ControlledSource.step_disabled width _ state disabled] at actual
  exact actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledParallel
