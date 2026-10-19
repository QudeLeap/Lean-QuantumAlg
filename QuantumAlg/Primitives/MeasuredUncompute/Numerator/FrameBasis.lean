/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Runtime.Action
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Branch.Action
import all QuantumAlg.Primitives.MeasuredUncompute.Product.Placement
import all QuantumAlg.Components.Encoded.BitGates.Realization

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

variable {environment : OracleModel.empty.Interpretation}

open Execution MAU.Inversion.SharedEEA NumeratorMeasurement ProductPlacement

/-- A complete native arithmetic frame at its actual runtime wire coordinates. -/
def basis (width : Nat) (frame : Frame width) : (context width).register.Index :=
  (frameBasis width).symm ((frameEncoding width).encode frame)

/-- Every complete native label survives the physical runtime assembly exactly. -/
lemma native_label (width : Nat) (frame : Frame width) :
    frameBasis width (basis width frame) = (frameEncoding width).encode frame :=
  (frameBasis width).apply_symm_apply _

private lemma coordinates (width : Nat) (frame : Frame width) :
    (prodEquiv (m := (encoding width).width) (n := width)).symm
        (frameBasis width (basis width frame)) =
      ((encoding width).encode frame.1, frame.2) := by
  have packed : (frameEncoding width).encode frame =
      prodEquiv ((encoding width).encode frame.1, frame.2) := rfl
  exact (congrArg (prodEquiv (m := (encoding width).width) (n := width)).symm
    ((native_label width frame).trans packed)).trans
      ((prodEquiv (m := (encoding width).width) (n := width)).symm_apply_apply _)

/-- The actually measured runtime word is precisely the last native frame word. -/
lemma word (width : Nat) (frame : Frame width) :
    NumeratorObservation.word width (basis width frame) = frame.2 := by
  have actual := congrArg
    (fun pair : Fin (2 ^ (encoding width).width) × Fin (2 ^ width) => pair.2)
    (coordinates width frame)
  exact actual

/-- All other native fields appear unchanged in the runtime prefix coordinate. -/
lemma frame_prefix (width : Nat) (frame : Frame width) :
    NumeratorResetMatrix.framePrefix width (basis width frame) =
      (encoding width).encode frame.1 := by
  have actual := congrArg
    (fun pair : Fin (2 ^ (encoding width).width) × Fin (2 ^ width) => pair.1)
    (coordinates width frame)
  exact actual

/-- Actual selected replacement changes only the existing last word of the complete frame. -/
lemma replace (width : Nat) (frame : Frame width) (value : Fin (2 ^ width)) :
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

/-- Transport a physical basis phase through the canonical binary coordinate map. -/
private lemma binary_phase (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    (source target : Fin (2 ^ (frameEncoding width).width)) (phase : ℂ)
    (action : (body.applyVec environment)
      (NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding width).width).basisEquiv.symm source)).vec =
      phase • (NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding width).width).basisEquiv.symm target)).vec) :
    (body.binaryMatrix environment).applyVec (NormalizedVector.ket source).vec =
      phase • (NormalizedVector.ket target).vec := by
  let coordinates := (QubitLayout.canonical (frameEncoding width).width).basisEquiv
  have transported := UnitaryOperator.reindex_applyVec coordinates (body.matrix environment)
    (NormalizedVector.ket (coordinates.symm source)).vec
  change (body.binaryMatrix environment).applyVec
      (HilbertVector.reindex coordinates (NormalizedVector.ket (coordinates.symm source)).vec) =
    HilbertVector.reindex coordinates
      ((body.applyVec environment)
        (NormalizedVector.ket (coordinates.symm source)).vec) at transported
  erw [HilbertVector.reindex_ket, coordinates.apply_symm_apply] at transported
  erw [action] at transported
  have reindexedTarget :
      HilbertVector.reindex coordinates
          (phase • (NormalizedVector.ket (coordinates.symm target)).vec) =
        phase • (NormalizedVector.ket target).vec := by
    apply WithLp.ofLp_injective
    funext index
    simp only [HilbertVector.reindex_apply, PiLp.smul_apply]
    congr 1
    have same : coordinates.symm index = coordinates.symm target ↔ index = target :=
      coordinates.symm.injective.eq_iff
    simp only [NormalizedVector.ket_apply, same]
  exact transported.trans reindexedTarget

/-- Every native phase action lifts to the actual full runtime frame and the same reference. -/
lemma native_action (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    (source target : Frame width) (phase : ℂ)
    (action : (body.applyVec environment)
      (NormalizedVector.ket ((QubitLayout.canonical (frameEncoding width).width).basisEquiv.symm
        ((frameEncoding width).encode source))).vec =
      phase • (NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding width).width).basisEquiv.symm
          ((frameEncoding width).encode target))).vec)
    {Reference : Register} (reference : Reference.Index) :
    HilbertOperator.applyVec
      (UnitaryOperator.prodTensor ((NumeratorRuntime.program width body).matrix environment)
        (1 : UnitaryOperator Reference) :
          HilbertOperator (Register.prod (context width).register Reference))
      (ket width source reference).vec = phase • (ket width target reference).vec :=
  NumeratorRuntimeAction.reference_ket width body ((frameEncoding width).encode source)
    ((frameEncoding width).encode target) phase
    (binary_phase width body _ _ phase action) reference

/-- A normalized native basis equation is transported without introducing any relative phase. -/
lemma native_normalized (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    (source target : Frame width)
    (action : (body.applyNormalized environment)
      (NormalizedVector.ket ((QubitLayout.canonical (frameEncoding width).width).basisEquiv.symm
        ((frameEncoding width).encode source))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding width).width).basisEquiv.symm
          ((frameEncoding width).encode target)))
    {Reference : Register} (reference : Reference.Index) :
    HilbertOperator.applyVec
      (UnitaryOperator.prodTensor ((NumeratorRuntime.program width body).matrix environment)
        (1 : UnitaryOperator Reference) :
          HilbertOperator (Register.prod (context width).register Reference))
      (ket width source reference).vec = (ket width target reference).vec := by
  have vector := congrArg (fun state : NormalizedVector
    (QubitLayout.canonical (frameEncoding width).width).toQuantum.register => state.vec) action
  have phased : (body.applyVec environment)
      (NormalizedVector.ket ((QubitLayout.canonical (frameEncoding width).width).basisEquiv.symm
        ((frameEncoding width).encode source))).vec =
      (1 : ℂ) • (NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding width).width).basisEquiv.symm
          ((frameEncoding width).encode target))).vec := by
    rw [one_smul]
    exact vector
  simpa only [one_smul] using native_action width body source target 1 phased reference

end

end QuantumAlg.MeasuredUncompute.NumeratorFrameBasis
