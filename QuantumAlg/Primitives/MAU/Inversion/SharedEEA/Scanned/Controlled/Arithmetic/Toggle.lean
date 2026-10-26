/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Arithmetic.Conjunction
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Guard.Remainder
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Guard.Coefficient

/-!
# Actual externally selected complete arithmetic guards

The complete original geometry preparation and its literal native
adjoint execute in both external branches. Only the small phase calls
inside the full conjunction receive the external control. No original
source flag or metadata is an external-control substitute.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledArithmeticToggle

noncomputable section

open EncodedBit NumberTheory.SharedEEA

private def geometryProgram (width : Nat) (positive : 1 ≤ width) (coefficient : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (Scanned.encoding width).width).toQuantum :=
  if coefficient then ArithmeticGeometry.runtimeCoefficientProgram width positive
  else ArithmeticGeometry.remainderProgram width positive

private def geometryStep (width : Nat) (positive : 1 ≤ width) (coefficient : Bool) :
    Scanned.Data width → Scanned.Data width :=
  if coefficient then ArithmeticGeometry.runtimeCoefficientStep width positive
  else ArithmeticGeometry.remainderStep width positive

private lemma geometryProgram_realizes (width : Nat) (positive : 1 ≤ width)
    (coefficient : Bool) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (Scanned.encoding width) (geometryProgram width positive coefficient)
      environment (geometryStep width positive coefficient) := by
  cases coefficient
  · exact ArithmeticGeometry.remainderProgram_realizes width positive environment
  · exact ArithmeticGeometry.runtimeCoefficientProgram_realizes width positive environment

private lemma geometryStep_prefix (width : Nat) (positive : 1 ≤ width) (coefficient : Bool)
    (state : Scanned.Data width) :
    (geometryStep width positive coefficient state).2.2.1 = state.2.2.1 := by
  cases coefficient
  · exact ArithmeticGeometry.remainderStep_prefix width positive state
  · exact ArithmeticGeometry.runtimeCoefficientStep_prefix width positive state

private lemma geometryStep_control_flip (width : Nat) (positive : 1 ≤ width)
    (coefficient : Bool) (state : Scanned.Data width) :
    geometryStep width positive coefficient ((ArithmeticGuard.flag width 4).flip state) =
      (ArithmeticGuard.flag width 4).flip (geometryStep width positive coefficient state) := by
  cases coefficient
  · exact ArithmeticGeometry.remainderStep_control_flip width positive state
  · exact ArithmeticGeometry.runtimeCoefficientStep_control_flip width positive state

/-- Complete untruncated original geometry and phase predicate, before external selection. -/
def enabled (width : Nat) (signed coefficient : Bool) : Scanned.Data width → Bool :=
  if coefficient then ArithmeticGuard.coefficientEnabled width signed
  else ArithmeticGuard.remainderEnabled width signed

private lemma geometryStep_selected (width : Nat) (positive : 1 ≤ width)
    (signed coefficient : Bool) (state : Scanned.Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : ArithmeticGeometry.targetValue width state = 0#(ArithmeticGeometry.fullWidth width)) :
    (ArithmeticGuard.valid width (geometryStep width positive coefficient state) &&
        ArithmeticGuard.condition width signed coefficient
          (geometryStep width positive coefficient state)) =
      enabled width signed coefficient state := by
  cases coefficient with
  | false =>
      let prepared := ArithmeticGeometry.remainderStep width positive state
      have validity : ArithmeticGuard.valid width prepared =
          decide (state.1.coefficientLength.toNat + state.1.quotientLength.toNat + 1 +
            state.1.shift.toNat < width + 3) := by
        apply Bool.eq_iff_iff.mpr
        simpa only [ArithmeticGuard.valid, decide_eq_true_eq] using
          ArithmeticGeometry.remainderStep_target_positive_iff width positive state clean zero
      have phase : ArithmeticGuard.condition width signed false prepared =
          ArithmeticGuard.condition width signed false state :=
        congrArg (fun source : Registers width =>
          ArithmeticGuard.condition width signed false (source, prepared.2))
          (ArithmeticGeometry.remainderStep_source width positive state)
      change (ArithmeticGuard.valid width prepared &&
        ArithmeticGuard.condition width signed false prepared) = _
      rw [validity, phase]
      rfl
  | true =>
      let prepared := ArithmeticGeometry.runtimeCoefficientStep width positive state
      have validity : ArithmeticGuard.valid width prepared = decide (if state.1.flags.second then
          state.1.divisorLength.toNat + state.1.shift.toNat < width + 3
        else state.1.coefficientLength.toNat + 1 ≤ width + 3) := by
        apply Bool.eq_iff_iff.mpr
        simpa only [ArithmeticGuard.valid, decide_eq_true_eq] using
          ArithmeticGeometry.runtimeCoefficientStep_target_positive_iff
            width positive state clean zero
      have phase : ArithmeticGuard.condition width signed true prepared =
          ArithmeticGuard.condition width signed true state :=
        congrArg (fun source : Registers width =>
          ArithmeticGuard.condition width signed true (source, prepared.2))
          (ArithmeticGeometry.runtimeCoefficientStep_source width positive state)
      change (ArithmeticGuard.valid width prepared &&
        ArithmeticGuard.condition width signed true prepared) = _
      rw [validity, phase]
      rfl

/-- Original Ctrl is toggled by the retained external bit and the complete source predicate. -/
def step (width : Nat) (signed coefficient : Bool) :
    ControlledFrame.Data width → ControlledFrame.Data width :=
  predicateFlip (ControlledFrame.sourceBit width (ArithmeticGuard.flag width 4))
    (fun state => state.2.1 && enabled width signed coefficient state.1)

/-- Actual full preparation, the four fused calls, and the complete same-source native adjoint. -/
def program (width : Nat) (positive : 1 ≤ width) (signed coefficient : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledFrame.encoding width).width).toQuantum :=
  PredicateCompute.program
    (ControlledFrame.liftProgram width (geometryProgram width positive coefficient))
    (ControlledArithmeticConjunction.program width signed coefficient)

/-- All original finite metadata and arbitrary original Ctrl/Iter have exact complete cleanup. -/
lemma program_apply_encoded_ket (width : Nat) (positive : 1 ≤ width)
    (signed coefficient : Bool) (environment : OracleModel.empty.Interpretation)
    (state : ControlledFrame.Data width)
    (clean : state.1.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : ArithmeticGeometry.targetValue width state.1 =
      0#(ArithmeticGeometry.fullWidth width)) :
    (program width positive signed coefficient).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode (step width signed coefficient state))) := by
  let sourcePrepared := geometryStep width positive coefficient state.1
  let prepared := (sourcePrepared, state.2)
  let prepareStep : ControlledFrame.Data width → ControlledFrame.Data width :=
    fun value => (geometryStep width positive coefficient value.1, value.2)
  have preparedClean : sourcePrepared.2.2.1 = 0#(ScanMetadata.addressWidth width) :=
    (geometryStep_prefix width positive coefficient state.1).trans clean
  have selected := geometryStep_selected width positive signed coefficient state.1 clean zero
  have middle := ControlledArithmeticConjunction.program_apply_encoded_ket
    width signed coefficient environment prepared preparedClean
  have selectedStep : ControlledArithmeticConjunction.step width signed coefficient prepared =
      if state.2.1 && enabled width signed coefficient state.1 then
        (ControlledFrame.sourceBit width (ArithmeticGuard.flag width 4)).flip prepared
      else prepared := by
    change (if state.2.1 then
      (if ArithmeticGuard.valid width sourcePrepared &&
          ArithmeticGuard.condition width signed coefficient sourcePrepared then
        (ArithmeticGuard.flag width 4).flip sourcePrepared else sourcePrepared)
      else sourcePrepared, state.2) = _
    rw [selected]
    cases state.2.1 <;> cases enabled width signed coefficient state.1 <;> rfl
  rw [selectedStep] at middle
  have commute : prepareStep
        ((ControlledFrame.sourceBit width (ArithmeticGuard.flag width 4)).flip state) =
      (ControlledFrame.sourceBit width (ArithmeticGuard.flag width 4)).flip
        (prepareStep state) := by
    change (geometryStep width positive coefficient
      ((ArithmeticGuard.flag width 4).flip state.1), state.2) =
        ((ArithmeticGuard.flag width 4).flip sourcePrepared, state.2)
    rw [geometryStep_control_flip]
  exact PredicateCompute.program_apply_encoded_ket
    (ControlledFrame.liftProgram width (geometryProgram width positive coefficient))
    (ControlledArithmeticConjunction.program width signed coefficient) prepareStep
    (ControlledFrame.sourceBit width (ArithmeticGuard.flag width 4))
    (fun value => value.2.1 && enabled width signed coefficient value.1) environment
    (ControlledFrame.liftProgram_realizes width (geometryProgram width positive coefficient)
      (geometryStep width positive coefficient) environment
      (geometryProgram_realizes width positive coefficient environment)) state middle commute

/-- The exact independent selected action retains every inactive source and work coordinate. -/
lemma step_eq_selected (width : Nat) (signed coefficient : Bool)
    (state : ControlledFrame.Data width) :
    step width signed coefficient state =
      (if state.2.1 then predicateFlip (ArithmeticGuard.flag width 4)
        (enabled width signed coefficient) state.1 else state.1, state.2) := by
  exact ControlledFrame.selected_predicateFlip width (ArithmeticGuard.flag width 4)
    (enabled width signed coefficient) state

lemma step_disabled (width : Nat) (signed coefficient : Bool)
    (state : ControlledFrame.Data width) (disabled : state.2.1 = false) :
    step width signed coefficient state = state := by
  rw [step_eq_selected, disabled]
  rfl

lemma step_pool (width : Nat) (signed coefficient : Bool) (state : ControlledFrame.Data width) :
    (step width signed coefficient state).1.2 = state.1.2 := by
  unfold step predicateFlip
  split <;> rfl

lemma step_external (width : Nat) (signed coefficient : Bool)
    (state : ControlledFrame.Data width) : (step width signed coefficient state).2 = state.2 := by
  rw [step_eq_selected]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledArithmeticToggle
