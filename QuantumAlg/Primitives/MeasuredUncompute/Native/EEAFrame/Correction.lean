/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.ReusedProduct.Controlled
import all QuantumAlg.Primitives.MeasuredUncompute.Native.EEAFrame.Controlled
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Arithmetic
import all QuantumAlg.Core.Execution.QubitReadouts

/-!
# The native controlled backward EEA followed by the actual selected correction

The retained finite measurement word selects its literal phase sequence.
The suffix composes that concrete correction with the actual controlled EEA
backward list on the same complete frame and original final control.
-/

namespace QuantumAlg.MeasuredUncompute.NativeEEAFrame.Correction

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Execution ProductPlacement EncodedBit GateSpec

/-- A retained finite outcome selects the actual complete-frame correction circuit. -/
def member (width : Nat) (modulus : Fin (2 ^ width + 1)) (active : Bool)
    (value : CShape.Value (.fixedVector width (.finite 2)))
    (layout : QubitLayout (NativeFrameControl.encoding width).width) :
    UnitaryCircuit AlgorithmGate.model .empty layout.toQuantum :=
  ReusedProduct.Controlled.program width modulus active (QubitReadouts.mask value) layout

/-- Coherent EEA selects the original placed adjoint and retains the supplied control. -/
def step (modulus : Nat) (prime : Nat.Prime modulus) (active : Bool) :
    Frame modulus.size × Bool → Frame modulus.size × Bool :=
  NativeFrameControl.step modulus.size active (NativeEEAFrame.backwardStep modulus prime)

/-- The selected outcome contributes its actual recomputed phase after the controlled EEA. -/
def phase (modulus : Nat) (prime : Nat.Prime modulus) (active : Bool)
    (value : CShape.Value (.fixedVector modulus.size (.finite 2)))
    (state : Frame modulus.size × Bool) : ℂ :=
  ReusedProduct.Controlled.phase modulus.size (InPlaceArithmetic.modulusWord modulus)
    active (QubitReadouts.mask value) (step modulus prime active state)

/-- The executable native suffix retains both actual circuits and the same physical layout. -/
def program (modulus : Nat) (prime : Nat.Prime modulus) (active : Bool)
    (value : CShape.Value (.fixedVector modulus.size (.finite 2)))
    (layout : QubitLayout (NativeFrameControl.encoding modulus.size).width) :
    UnitaryCircuit AlgorithmGate.model .empty layout.toQuantum :=
  (Controlled.backward modulus prime active layout).seq
    (member modulus.size (InPlaceArithmetic.modulusWord modulus) active value layout)

/-- Every complete dirty label receives the precise corrected backward action and relative phase. -/
lemma nativeEEACorrection_ket (modulus : Nat) (prime : Nat.Prime modulus) (active : Bool)
    (value : CShape.Value (.fixedVector modulus.size (.finite 2)))
    (layout : QubitLayout (NativeFrameControl.encoding modulus.size).width)
    (state : Frame modulus.size × Bool) :
    ((program modulus prime active value layout).applyVec environment)
      (NormalizedVector.ket (layout.basisEquiv.symm
        ((NativeFrameControl.encoding modulus.size).encode state))).vec =
      phase modulus prime active value state •
        (NormalizedVector.ket (layout.basisEquiv.symm
          ((NativeFrameControl.encoding modulus.size).encode
            (step modulus prime active state)))).vec := by
  have backward := congrArg NormalizedVector.vec
    ((Controlled.nativeEEAControlled_backward_realizes (environment := environment)
      modulus prime active layout).apply_encoded_ket state)
  change ((Controlled.backward modulus prime active layout).applyVec environment)
      (NormalizedVector.ket (layout.basisEquiv.symm
        ((NativeFrameControl.encoding modulus.size).encode state))).vec =
      (NormalizedVector.ket (layout.basisEquiv.symm
        ((NativeFrameControl.encoding modulus.size).encode
          (step modulus prime active state)))).vec at backward
  rw [program, UnitaryCircuit.applyVec_seq, backward, member,
    ReusedProduct.Controlled.reusedProductControlled_ket]
  rfl

/-- The unselected complete frame is identity after both EEA and product correction. -/
lemma nativeEEACorrection_inactive (modulus : Nat) (prime : Nat.Prime modulus) (active : Bool)
    (value : CShape.Value (.fixedVector modulus.size (.finite 2)))
    (layout : QubitLayout (NativeFrameControl.encoding modulus.size).width)
    (state : Frame modulus.size × Bool) (unselected : state.2 ≠ active) :
    ((program modulus prime active value layout).applyVec environment)
      (NormalizedVector.ket (layout.basisEquiv.symm
        ((NativeFrameControl.encoding modulus.size).encode state))).vec =
      (NormalizedVector.ket (layout.basisEquiv.symm
        ((NativeFrameControl.encoding modulus.size).encode state))).vec := by
  have unchanged : step modulus prime active state = state := by
    simp only [step, NativeFrameControl.step, if_neg unselected, Prod.mk.eta]
  rw [nativeEEACorrection_ket, phase, unchanged, ReusedProduct.Controlled.phase,
    if_neg unselected, one_smul]

/-- Arbitrary reference columns preserve the selected full-frame transition and its exact phase. -/
lemma nativeEEACorrection_reference (modulus : Nat) (prime : Nat.Prime modulus) (active : Bool)
    (value : CShape.Value (.fixedVector modulus.size (.finite 2)))
    (layout : QubitLayout (NativeFrameControl.encoding modulus.size).width)
    (state : Frame modulus.size × Bool) {Reference : Register}
    (row : layout.toQuantum.register.Index) (left right : Reference.Index) :
    UnitaryOperator.prodTensor ((program modulus prime active value layout).matrix environment)
      (1 : UnitaryOperator Reference) (row, left)
      (layout.basisEquiv.symm ((NativeFrameControl.encoding modulus.size).encode state), right) =
      if row = layout.basisEquiv.symm ((NativeFrameControl.encoding modulus.size).encode
        (step modulus prime active state)) ∧ left = right then
        phase modulus prime active value state else 0 := by
  have column := congrArg
    (fun vector : HilbertVector layout.toQuantum.register => vector row)
    (nativeEEACorrection_ket (environment := environment) modulus prime active value layout state)
  have matrixColumn := (HilbertOperator.applyVec_ket
    (((program modulus prime active value layout).matrix environment) : HilbertOperator
      layout.toQuantum.register)
    (layout.basisEquiv.symm ((NativeFrameControl.encoding modulus.size).encode state))
    row).symm.trans column
  rw [UnitaryOperator.prodTensor_apply, matrixColumn]
  simp only [PiLp.smul_apply, smul_eq_mul, NormalizedVector.ket_apply]
  change (phase modulus prime active value state *
    (if row = layout.basisEquiv.symm ((NativeFrameControl.encoding modulus.size).encode
      (step modulus prime active state)) then 1 else 0)) * (if left = right then 1 else 0) = _
  by_cases localRow : row = layout.basisEquiv.symm
      ((NativeFrameControl.encoding modulus.size).encode (step modulus prime active state))
    <;> by_cases reference : left = right <;>
      simp only [localRow, reference, ite_true, ite_false,
        and_true, and_false, mul_one, mul_zero]

/-- Actual EEA and selected correction traces remain in their original execution order. -/
lemma nativeEEACorrection_trace (modulus : Nat) (prime : Nat.Prime modulus) (active : Bool)
    (value : CShape.Value (.fixedVector modulus.size (.finite 2)))
    (layout : QubitLayout (NativeFrameControl.encoding modulus.size).width) :
    (program modulus prime active value layout).eventTrace =
      (Controlled.backwardGates modulus prime active).map (event .empty) ++
        (ReusedProduct.Controlled.program modulus.size (InPlaceArithmetic.modulusWord modulus)
          active (QubitReadouts.mask value) layout).eventTrace := by
  rw [program, UnitaryCircuit.seq_eventTrace, Controlled.nativeEEAControlled_backward_trace]
  rfl

/-- Resource coordinates come from the actual native EEA and full correction member. -/
lemma nativeEEACorrection_cost (modulus : Nat) (prime : Nat.Prime modulus) (active : Bool)
    (value : CShape.Value (.fixedVector modulus.size (.finite 2)))
    (layout : QubitLayout (NativeFrameControl.encoding modulus.size).width) :
    (program modulus prime active value layout).eventCost =
      ResourcePool.ofList ((Controlled.backwardGates modulus prime active).map (event .empty)) +
        (ReusedProduct.Controlled.program modulus.size (InPlaceArithmetic.modulusWord modulus)
          active (QubitReadouts.mask value) layout).eventCost := by
  rw [program, UnitaryCircuit.seq_eventCost, Controlled.backward, programList_eventCost]
  rfl

/-- Complete serial depth counts the expanded EEA and each actual selected correction gate. -/
lemma nativeEEACorrection_depth (modulus : Nat) (prime : Nat.Prime modulus) (active : Bool)
    (value : CShape.Value (.fixedVector modulus.size (.finite 2)))
    (layout : QubitLayout (NativeFrameControl.encoding modulus.size).width) :
    (program modulus prime active value layout).evaluatedEventDepth (fun _ => 1) =
      (Controlled.backwardGates modulus prime active).length +
        (2 * (ReusedProduct.Controlled.computeGates modulus.size
          (InPlaceArithmetic.modulusWord modulus)).length +
          3 * (Word.PhaseCorrection.selected (QubitReadouts.mask value)).length +
            (if active then 0 else 2)) := by
  rw [program, UnitaryCircuit.evaluatedEventDepth_seq, Controlled.backward,
    programList_evaluatedEventDepth_unit, member,
    ReusedProduct.Controlled.reusedProductControlled_depth]

end

end QuantumAlg.MeasuredUncompute.NativeEEAFrame.Correction
