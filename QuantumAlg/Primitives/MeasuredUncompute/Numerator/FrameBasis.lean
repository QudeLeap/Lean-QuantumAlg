/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Runtime.Action
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Branch.Action
import all QuantumAlg.Primitives.MeasuredUncompute.Product.Placement

/-!
# Complete frame labels in the actual numerator runtime basis

The basis correspondence is the already certified per-wire runtime map.
Its physical numerator read and selected replacement agree with the real
last word of the complete native frame. These facts connect both measured
arithmetic operations to their actual H/Z/reset operator without dropping
any other field [LYL+26, sec_point_add/sec_point_add.tex:67-105,119-122].
-/

namespace QuantumAlg.MeasuredUncompute.NumeratorFrameBasis

noncomputable section

open Execution MAU.Inversion.SharedEEA NumeratorMeasurement ProductPlacement

/-- A complete native arithmetic frame at its actual runtime wire coordinates. -/
def basis (width : Nat) (frame : Frame width) : (context width).register.Index :=
  (frameBasis width).symm ((frameEncoding width).encode frame)

/-- Every complete native label survives the physical runtime assembly exactly. -/
theorem native_label (width : Nat) (frame : Frame width) :
    frameBasis width (basis width frame) = (frameEncoding width).encode frame :=
  (frameBasis width).apply_symm_apply _

private theorem coordinates (width : Nat) (frame : Frame width) :
    (prodEquiv (m := (encoding width).width) (n := width)).symm
        (frameBasis width (basis width frame)) =
      ((encoding width).encode frame.1, frame.2) := by
  have packed : (frameEncoding width).encode frame =
      prodEquiv ((encoding width).encode frame.1, frame.2) := rfl
  exact (congrArg (prodEquiv (m := (encoding width).width) (n := width)).symm
    ((native_label width frame).trans packed)).trans
      ((prodEquiv (m := (encoding width).width) (n := width)).symm_apply_apply _)

/-- The actually measured runtime word is precisely the last native frame word. -/
theorem word (width : Nat) (frame : Frame width) :
    NumeratorObservation.word width (basis width frame) = frame.2 := by
  have actual := congrArg
    (fun pair : Fin (2 ^ (encoding width).width) × Fin (2 ^ width) => pair.2)
    (coordinates width frame)
  exact actual

/-- All other native fields appear unchanged in the runtime prefix coordinate. -/
theorem frame_prefix (width : Nat) (frame : Frame width) :
    NumeratorResetMatrix.framePrefix width (basis width frame) =
      (encoding width).encode frame.1 := by
  have actual := congrArg
    (fun pair : Fin (2 ^ (encoding width).width) × Fin (2 ^ width) => pair.1)
    (coordinates width frame)
  exact actual

/-- Actual selected replacement changes only the existing last word of the complete frame. -/
theorem replace (width : Nat) (frame : Frame width) (value : Fin (2 ^ width)) :
    NumeratorBranchAction.replaceWord width (basis width frame) value =
      basis width (frame.1, value) := by
  symm
  apply (NumeratorBranchAction.eq_replace_iff width _ (basis width frame) value).mpr
  exact ⟨(frame_prefix width (frame.1, value)).trans (frame_prefix width frame).symm,
    word width (frame.1, value)⟩

/-- A complete actual frame ket retains its arbitrary external-reference basis coordinate. -/
def ket (width : Nat) {Reference : Register} (frame : Frame width)
    (reference : Reference.Index) :
    NormalizedVector (Register.prod (context width).register Reference) :=
  NormalizedVector.ket (basis width frame, reference)

/-- Every native phase action lifts to the actual full runtime frame and the same reference. -/
theorem native_action (width : Nat)
    (body : UnitaryCircuit (Qubits (OutputCopy.encoding width).width))
    (source target : Frame width) (phase : ℂ)
    (action : body.applyVec
      (NormalizedVector.ket (R := Qubits (frameEncoding width).width)
        ((frameEncoding width).encode source)).vec =
      phase • (NormalizedVector.ket (R := Qubits (frameEncoding width).width)
        ((frameEncoding width).encode target)).vec)
    {Reference : Register} (reference : Reference.Index) :
    HilbertOperator.applyVec
      (UnitaryOperator.prodTensor (NumeratorRuntime.program width body).matrix
        (1 : UnitaryOperator Reference) :
          HilbertOperator (Register.prod (context width).register Reference))
      (ket width source reference).vec = phase • (ket width target reference).vec :=
  NumeratorRuntimeAction.reference_ket width body ((frameEncoding width).encode source)
    ((frameEncoding width).encode target) phase action reference

/-- A normalized native basis equation is transported without introducing any relative phase. -/
theorem native_normalized (width : Nat)
    (body : UnitaryCircuit (Qubits (OutputCopy.encoding width).width))
    (source target : Frame width)
    (action : body.applyNormalized
      (NormalizedVector.ket (R := Qubits (frameEncoding width).width)
        ((frameEncoding width).encode source)) =
      NormalizedVector.ket (R := Qubits (frameEncoding width).width)
        ((frameEncoding width).encode target))
    {Reference : Register} (reference : Reference.Index) :
    HilbertOperator.applyVec
      (UnitaryOperator.prodTensor (NumeratorRuntime.program width body).matrix
        (1 : UnitaryOperator Reference) :
          HilbertOperator (Register.prod (context width).register Reference))
      (ket width source reference).vec = (ket width target reference).vec := by
  have vector := congrArg
    (fun state : NormalizedVector (Qubits (OutputCopy.encoding width).width) => state.vec) action
  change body.applyVec
    (NormalizedVector.ket (R := Qubits (OutputCopy.encoding width).width)
      ((frameEncoding width).encode source)).vec =
    (NormalizedVector.ket (R := Qubits (OutputCopy.encoding width).width)
      ((frameEncoding width).encode target)).vec at vector
  have phased : body.applyVec
      (NormalizedVector.ket (R := Qubits (frameEncoding width).width)
        ((frameEncoding width).encode source)).vec =
      (1 : ℂ) • (NormalizedVector.ket (R := Qubits (frameEncoding width).width)
        ((frameEncoding width).encode target)).vec := by
    rw [one_smul]
    exact vector
  simpa only [one_smul] using native_action width body source target 1 phased reference

end

end QuantumAlg.MeasuredUncompute.NumeratorFrameBasis
