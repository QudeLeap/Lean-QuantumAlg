/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Parallel.Body
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Parallel.Arithmetic

/-!
# Direct original-instruction semantics of the actual selected paired arithmetic

Both actual fused guards and the actual source body execute in order.
Their intermediate states are proved directly, without a complete old
instruction endpoint or a legacy whole-program matrix equality. The
result is the original independent mathematical source instruction.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledParallel

noncomputable section

open EncodedBit NumberTheory.SharedEEA

private def sourceToggle (width : Nat) (signed coefficient : Bool) :
    Scanned.Data width → Scanned.Data width :=
  predicateFlip (ArithmeticGuard.flag width 4)
    (ControlledArithmeticToggle.enabled width signed coefficient)

private lemma sourceToggle_pool (width : Nat) (signed coefficient : Bool)
    (state : Scanned.Data width) : (sourceToggle width signed coefficient state).2 = state.2 := by
  unfold sourceToggle predicateFlip
  split <;> rfl

private lemma sourceToggle_self (width : Nat) (signed coefficient : Bool)
    (state : Scanned.Data width) :
    sourceToggle width signed coefficient (sourceToggle width signed coefficient state) =
      state := by
  have stable : ControlledArithmeticToggle.enabled width signed coefficient
        ((ArithmeticGuard.flag width 4).flip state) =
      ControlledArithmeticToggle.enabled width signed coefficient state := by
    cases coefficient
    · exact RemainderGuard.enabled_control_flip width signed state
    · exact CoefficientGuard.enabled_control_flip width signed state
  cases active : ControlledArithmeticToggle.enabled width signed coefficient state <;>
    simp only [sourceToggle, predicateFlip, active, stable, Bool.false_eq_true,
      if_false, if_true, EncodedBit.flip_flip]

private def sourceStep (width : Nat) (signed coefficient : Bool) :
    Scanned.Data width → Scanned.Data width :=
  if coefficient then CoefficientGuard.step width signed else RemainderGuard.step width signed

private lemma sourceStep_pool (width : Nat) (signed coefficient : Bool)
    (state : Scanned.Data width) : (sourceStep width signed coefficient state).2 = state.2 := by
  cases coefficient
  · exact RemainderGuard.step_pool width signed state
  · exact CoefficientGuard.step_pool width signed state

private lemma body_apply_disabled (width : Nat) (positive : 1 ≤ width)
    (signed coefficient : Bool) (environment : OracleModel.empty.Interpretation)
    (state : Scanned.Data width) (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (disabled : state.1.control = false) :
    (arithmeticBody width positive signed coefficient).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((Scanned.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((Scanned.encoding width).encode state)) := by
  cases coefficient
  · exact RemainderAddress.Parallel.bodyProgram_apply_disabled
      width positive signed environment state clean zero disabled
  · exact CoefficientGuard.bodyProgram_apply_disabled
      width positive signed environment state clean zero disabled

private lemma body_apply_before (width : Nat) (positive : 1 ≤ width)
    (signed coefficient : Bool) (environment : OracleModel.empty.Interpretation)
    (state : Scanned.Data width) (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false)
    (addressZero : state.2.1 = 0#(ScanMetadata.addressWidth width))
    (disabled : state.1.control = false) :
    (arithmeticBody width positive signed coefficient).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((Scanned.encoding width).encode (sourceToggle width signed coefficient state)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((Scanned.encoding width).encode
          (sourceToggle width signed coefficient
            (sourceStep width signed coefficient state)))) := by
  cases coefficient with
  | false =>
      by_cases active : ArithmeticGuard.remainderEnabled width signed state = true
      · have accepted := (show RemainderAddress.Parallel.admitted width state.1 from
        RemainderGuard.enabled_admitted width signed state active)
        let selected := RemainderAddress.Parallel.window width state.1 accepted
        let before := (ArithmeticGuard.flag width 4).flip state
        let after := ArithmeticAddress.liftSource width
          (ArithmeticWindowProgram.step selected (RemainderGuard.operation signed)) before
        have beforeEnabled : before.1.control = true := by
          change (!state.1.control) = true
          rw [disabled]
          rfl
        have middle := RemainderAddress.Parallel.bodyProgram_apply_enabled
          width positive signed environment before clean zero addressZero beforeEnabled accepted
        change (RemainderAddress.Parallel.bodyProgram width positive signed).applyNormalized
          environment
          (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
            ((Scanned.encoding width).encode before))) =
          NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
            ((Scanned.encoding width).encode after)) at middle
        have firstToggle : sourceToggle width signed false state = before := if_pos active
        have finish := RemainderGuard.toggle_body_toggle width signed selected state active
        rw [RemainderGuard.toggle_active width signed state active] at finish
        have afterResult : sourceToggle width signed false after =
            sourceStep width signed false state := by
          change ArithmeticGuard.remainderToggleStep width signed after =
            RemainderGuard.step width signed state
          rw [RemainderGuard.step, dif_pos active]
          exact finish
        have afterEq : after = sourceToggle width signed false
            (sourceStep width signed false state) :=
          (sourceToggle_self width signed false after).symm.trans
            (congrArg (sourceToggle width signed false) afterResult)
        change (RemainderAddress.Parallel.bodyProgram width positive signed).applyNormalized
          environment
          (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
            ((Scanned.encoding width).encode (sourceToggle width signed false state)))) = _
        rw [firstToggle]
        exact middle.trans (congrArg (fun value : Scanned.Data width =>
          NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
            ((Scanned.encoding width).encode value))) afterEq)
      · have unchanged : sourceToggle width signed false state = state := if_neg active
        have result : sourceStep width signed false state = state := dif_neg active
        rw [unchanged, result, unchanged]
        exact body_apply_disabled width positive signed false environment state clean zero disabled
  | true =>
      by_cases active : ArithmeticGuard.coefficientEnabled width signed state = true
      · have accepted := CoefficientGuard.enabled_admitted width signed state active
        let selected := CoefficientCoordinates.window width
          (CoefficientAddress.wordLength width state.1)
          (CoefficientAddress.wordLength_fits width state.1 accepted)
        let before := (ArithmeticGuard.flag width 4).flip state
        let after := ArithmeticAddress.liftSource width
          (CoefficientWindowProgram.step selected (CoefficientGuard.operation signed)) before
        have beforeEnabled : before.1.control = true := by
          change (!state.1.control) = true
          rw [disabled]
          rfl
        have middle := CoefficientGuard.bodyProgram_apply_enabled
          width positive signed environment before clean zero addressZero beforeEnabled accepted
        change (CoefficientGuard.bodyProgram width positive signed).applyNormalized environment
          (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
            ((Scanned.encoding width).encode before))) =
          NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
            ((Scanned.encoding width).encode after)) at middle
        have firstToggle : sourceToggle width signed true state = before := if_pos active
        have finish := CoefficientGuard.toggle_body_toggle width signed selected state active
        rw [CoefficientGuard.toggle_active width signed state active] at finish
        have afterResult : sourceToggle width signed true after =
            sourceStep width signed true state := by
          change ArithmeticGuard.coefficientToggleStep width signed after =
            CoefficientGuard.step width signed state
          rw [CoefficientGuard.step, dif_pos active]
          exact finish
        have afterEq : after = sourceToggle width signed true
            (sourceStep width signed true state) :=
          (sourceToggle_self width signed true after).symm.trans
            (congrArg (sourceToggle width signed true) afterResult)
        change (CoefficientGuard.bodyProgram width positive signed).applyNormalized environment
          (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
            ((Scanned.encoding width).encode (sourceToggle width signed true state)))) = _
        rw [firstToggle]
        exact middle.trans (congrArg (fun value : Scanned.Data width =>
          NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
            ((Scanned.encoding width).encode value))) afterEq)
      · have unchanged : sourceToggle width signed true state = state := if_neg active
        have result : sourceStep width signed true state = state := dif_neg active
        rw [unchanged, result, unchanged]
        exact body_apply_disabled width positive signed true environment state clean zero disabled

private def instructionKind (signed coefficient : Bool) : ArithmeticInstruction.Instruction :=
  if coefficient then CoefficientGuard.instruction signed else RemainderGuard.instruction signed

/-- External selection of the original mathematical source instruction, retaining the full pool. -/
def instructionStep (width : Nat) (signed coefficient : Bool)
    (state : ControlledFrame.Data width) : ControlledFrame.Data width :=
  ((if state.2.1 then
      ArithmeticInstruction.sourceStep (instructionKind signed coefficient) state.1.1
    else state.1.1, state.1.2), state.2)

private lemma sourceStep_original (width : Nat) (signed coefficient : Bool)
    (state : Scanned.Data width) :
    sourceStep width signed coefficient state =
      (ArithmeticInstruction.sourceStep (instructionKind signed coefficient) state.1, state.2) := by
  cases coefficient
  · exact RemainderGuard.step_eq_original width signed state
  · exact CoefficientGuard.step_eq_original width signed state

/-- Actual selected guards and actual arithmetic return the independent full source result. -/
lemma instructionProgram_apply_encoded_ket (width : Nat) (positive : 1 ≤ width)
    (signed coefficient : Bool) (environment : OracleModel.empty.Interpretation)
    (state : ControlledFrame.Data width)
    (clean : state.1.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.1.2.2.2 = false)
    (addressZero : state.1.2.1 = 0#(ScanMetadata.addressWidth width))
    (disabled : state.1.1.control = false) :
    (instructionProgram width positive signed coefficient).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode
          (instructionStep width signed coefficient state))) := by
  have targetZero : ArithmeticGeometry.targetValue width state.1 =
      0#(ArithmeticGeometry.fullWidth width) := by
    rw [ArithmeticGeometry.targetValue, zero, addressZero]
    exact BitVec.false_cons_zero
  have first := ControlledArithmeticToggle.program_apply_encoded_ket
    width positive signed coefficient environment state clean targetZero
  cases selected : state.2.1 with
  | false =>
      rw [ControlledArithmeticToggle.step_disabled width signed coefficient state selected] at first
      have middle := body_apply_disabled
        width positive signed coefficient environment state.1 clean zero disabled
      have lifted := UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
        (Scanned.encoding width) ExternalWord.flags
        (arithmeticBody width positive signed coefficient)
        state.1 state.1 state.2 middle
      have actual := UnitaryCircuit.applyNormalized_seq_of_eq first
        (UnitaryCircuit.applyNormalized_seq_of_eq lifted first)
      change (instructionProgram width positive signed coefficient).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding width).encode state))) =
        NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding width).encode state)) at actual
      simpa only [instructionStep, selected, Bool.false_eq_true, if_false] using actual
  | true =>
      let result := sourceStep width signed coefficient state.1
      let after := sourceToggle width signed coefficient result
      have afterPool : after.2 = state.1.2 :=
        (sourceToggle_pool width signed coefficient result).trans
          (sourceStep_pool width signed coefficient state.1)
      have afterClean : after.2.2.1 = 0#(ScanMetadata.addressWidth width) :=
        (congrArg (fun pool : Pool width => pool.2.1) afterPool).trans clean
      have afterTarget : ArithmeticGeometry.targetValue width after =
          0#(ArithmeticGeometry.fullWidth width) := by
        change BitVec.cons after.2.2.2 after.2.1 = _
        rw [congrArg (fun pool : Pool width => pool.2.2) afterPool,
          congrArg Prod.fst afterPool, zero, addressZero]
        exact BitVec.false_cons_zero
      have last := ControlledArithmeticToggle.program_apply_encoded_ket
        width positive signed coefficient environment (after, state.2) afterClean afterTarget
      have lastStep : ControlledArithmeticToggle.step width signed coefficient (after, state.2) =
          (result, state.2) := by
        rw [ControlledArithmeticToggle.step_eq_selected]
        simp only [selected, ↓reduceIte]
        exact congrArg (fun source => (source, state.2))
          (sourceToggle_self width signed coefficient result)
      rw [lastStep] at last
      rw [ControlledArithmeticToggle.step_eq_selected] at first
      simp only [selected, ↓reduceIte] at first
      have middle := body_apply_before
        width positive signed coefficient environment state.1 clean zero addressZero disabled
      have lifted := UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
        (Scanned.encoding width) ExternalWord.flags
        (arithmeticBody width positive signed coefficient)
        (sourceToggle width signed coefficient state.1) after state.2 middle
      have actual := UnitaryCircuit.applyNormalized_seq_of_eq first
        (UnitaryCircuit.applyNormalized_seq_of_eq lifted last)
      change (instructionProgram width positive signed coefficient).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding width).encode state))) =
        NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding width).encode
            (sourceStep width signed coefficient state.1, state.2))) at actual
      rw [sourceStep_original] at actual
      simpa only [instructionStep, selected, if_true] using actual

lemma instructionStep_pool (width : Nat) (signed coefficient : Bool)
    (state : ControlledFrame.Data width) :
    (instructionStep width signed coefficient state).1.2 = state.1.2 := rfl

lemma instructionStep_external (width : Nat) (signed coefficient : Bool)
    (state : ControlledFrame.Data width) :
    (instructionStep width signed coefficient state).2 = state.2 := rfl

lemma instructionStep_control (width : Nat) (signed coefficient : Bool)
    (state : ControlledFrame.Data width) (control : state.1.1.control = false) :
    (instructionStep width signed coefficient state).1.1.control = false := by
  unfold instructionStep
  split
  · exact SharedEEA.ArithmeticBlocks.source_control
      width (instructionKind signed coefficient) state.1.1 control
  · exact control

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledParallel
