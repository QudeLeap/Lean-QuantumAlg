/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.ReusedProduct
import all QuantumAlg.Primitives.MeasuredUncompute.Native.Product.Gates
import all QuantumAlg.Primitives.MeasuredUncompute.Native.Frame.Controlled
import all QuantumAlg.Components.Encoded.BitGates.Word.PhaseCorrection.Controlled

/-!
# Actual controlled phase correction through the reused product

The original product is recomputed at the same complete physical placement.
Only the middle H-CNOT-H phase sequence is controlled; the literal reversed
product cancels both unconditional arithmetic passes in the unselected sector.
Every original dirty coordinate and reference coherence is retained.
-/

namespace QuantumAlg.MeasuredUncompute.ReusedProduct.Controlled

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open ProductPlacement EncodedBit GateSpec Word

/-- Actual reused product instructions beside the original final control. -/
def computeGates (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    List (GateSpec (NativeFrameControl.encoding width)) :=
  ((NativeProductFrame.gates width modulus).map (WorkspaceReuse.placement width).placeGate).map
    (GateSpec.prodLeft BinaryLabelEncoding.bool)

/-- FullPlacement and the untouched final control determine the complete arithmetic action. -/
lemma reusedProductControlled_computeGates_step (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (state : Frame width × Bool) :
    stepList (computeGates width modulus) state =
      (computeStep width modulus state.1, state.2) := by
  erw [computeGates, stepList_prodLeft, FullPlacement.placeGates_step]
  unfold computeStep FullPlacement.step
  rw [NativeProductFrame.nativeProductFrame_gates_step]

/-- The measured word retains its original little-endian measurement order. -/
def word (width : Nat) : EncodedBit.Word (NativeFrameControl.encoding width) width :=
  ⟨fun index => BinaryLabelEncoding.prodLeftBit (frameEncoding width) BinaryLabelEncoding.bool
    ((measuredWord width).bit index)⟩

private lemma different (width : Nat) (index : Fin width) :
    (NativeFrameControl.control width).wire ≠ ((word width).bit index).wire :=
  prodRightBit_wire_ne_prodLeftBit_wire (frameEncoding width) BinaryLabelEncoding.bool
    BinaryLabelEncoding.boolBit ((measuredWord width).bit index)

/-- Exact selected phase on the complete recomputed state, including arbitrary target contents. -/
def phase (width : Nat) (modulus : Fin (2 ^ width + 1)) (active : Bool)
    (mask : Fin width → Bool) (state : Frame width × Bool) : ℂ :=
  if state.2 = active then
    PhaseCorrection.sign (measuredWord width) (computeStep width modulus state.1)
      (PhaseCorrection.selected mask) else 1

private lemma word_sign (width : Nat) (state : Frame width × Bool)
    (indices : List (Fin width)) :
    PhaseCorrection.sign (word width) state indices =
      PhaseCorrection.sign (measuredWord width) state.1 indices := by
  induction indices with
  | nil => rfl
  | cons index rest ih => rw [PhaseCorrection.sign, PhaseCorrection.sign, ih]; rfl

/-- Two literal product passes surround the selected physical H-CNOT-H correction word. -/
def program (width : Nat) (modulus : Fin (2 ^ width + 1)) (active : Bool)
    (mask : Fin width → Bool) (layout : QubitLayout (NativeFrameControl.encoding width).width) :
    UnitaryCircuit AlgorithmGate.model .empty layout.toQuantum :=
  (programList layout .empty (computeGates width modulus)).seq
    ((PhaseCorrection.Controlled.program layout .empty (NativeFrameControl.control width)
      (word width) (different width) active mask).seq
      (programList layout .empty (computeGates width modulus).reverse))

-- Composition uses the certified full-frame word rather than evaluating its recursive generator.
attribute [local irreducible] computeGates

/-- Every local label is restored with precisely the selected relative phase. -/
lemma reusedProductControlled_ket (width : Nat) (modulus : Fin (2 ^ width + 1))
    (active : Bool) (mask : Fin width → Bool)
    (layout : QubitLayout (NativeFrameControl.encoding width).width) (state : Frame width × Bool) :
    ((program width modulus active mask layout).applyVec environment)
      (NormalizedVector.ket (layout.basisEquiv.symm
        ((NativeFrameControl.encoding width).encode state))).vec =
      phase width modulus active mask state •
        (NormalizedVector.ket (layout.basisEquiv.symm
          ((NativeFrameControl.encoding width).encode state))).vec := by
  have forward := congrArg NormalizedVector.vec
    ((realizesList layout .empty (computeGates width modulus) environment).apply_encoded_ket state)
  have backward := congrArg NormalizedVector.vec
    ((realizesList layout .empty (computeGates width modulus).reverse environment).apply_encoded_ket
      (stepList (computeGates width modulus) state))
  rw [stepList_reverse_stepList] at backward
  change ((programList layout .empty (computeGates width modulus)).applyVec environment)
      (NormalizedVector.ket (layout.basisEquiv.symm
        ((NativeFrameControl.encoding width).encode state))).vec =
      (NormalizedVector.ket (layout.basisEquiv.symm
        ((NativeFrameControl.encoding width).encode
          (stepList (computeGates width modulus) state)))).vec at forward
  change ((programList layout .empty (computeGates width modulus).reverse).applyVec environment)
      (NormalizedVector.ket (layout.basisEquiv.symm
        ((NativeFrameControl.encoding width).encode
          (stepList (computeGates width modulus) state)))).vec =
      (NormalizedVector.ket (layout.basisEquiv.symm
        ((NativeFrameControl.encoding width).encode state))).vec at backward
  rw [program, UnitaryCircuit.applyVec_seq, forward, UnitaryCircuit.applyVec_seq,
    PhaseCorrection.Controlled.program,
    PhaseCorrection.Controlled.controlledPhaseCorrection_sequence_ket,
    UnitaryCircuit.applyVec_smul, backward]
  rw [reusedProductControlled_computeGates_step, word_sign]
  rfl

/-- The unselected sector is exactly identity, for arbitrary dirty data and control coherences. -/
lemma reusedProductControlled_inactive (width : Nat) (modulus : Fin (2 ^ width + 1))
    (active : Bool) (mask : Fin width → Bool)
    (layout : QubitLayout (NativeFrameControl.encoding width).width)
    (state : Frame width × Bool) (unselected : state.2 ≠ active) :
    ((program width modulus active mask layout).applyVec environment)
      (NormalizedVector.ket (layout.basisEquiv.symm
        ((NativeFrameControl.encoding width).encode state))).vec =
      (NormalizedVector.ket (layout.basisEquiv.symm
        ((NativeFrameControl.encoding width).encode state))).vec := by
  rw [reusedProductControlled_ket, phase, if_neg unselected, one_smul]

/-- Every arbitrary reference column retains the same full-state relative phase. -/
lemma reusedProductControlled_reference (width : Nat) (modulus : Fin (2 ^ width + 1))
    (active : Bool) (mask : Fin width → Bool)
    (layout : QubitLayout (NativeFrameControl.encoding width).width) (state : Frame width × Bool)
    {Reference : Register} (row : layout.toQuantum.register.Index) (left right : Reference.Index) :
    UnitaryOperator.prodTensor ((program width modulus active mask layout).matrix environment)
      (1 : UnitaryOperator Reference) (row, left)
      (layout.basisEquiv.symm ((NativeFrameControl.encoding width).encode state), right) =
      if row = layout.basisEquiv.symm ((NativeFrameControl.encoding width).encode state) ∧
        left = right then phase width modulus active mask state else 0 := by
  have column := congrArg
    (fun vector : HilbertVector layout.toQuantum.register => vector row)
    (reusedProductControlled_ket (environment := environment)
      width modulus active mask layout state)
  have matrixColumn := (HilbertOperator.applyVec_ket
    (((program width modulus active mask layout).matrix environment) : HilbertOperator
      layout.toQuantum.register)
    (layout.basisEquiv.symm ((NativeFrameControl.encoding width).encode state))
    row).symm.trans column
  rw [UnitaryOperator.prodTensor_apply, matrixColumn]
  simp only [PiLp.smul_apply, smul_eq_mul, NormalizedVector.ket_apply]
  change (phase width modulus active mask state *
    (if row = layout.basisEquiv.symm ((NativeFrameControl.encoding width).encode state)
      then 1 else 0)) * (if left = right then 1 else 0) = _
  by_cases localRow : row =
      layout.basisEquiv.symm ((NativeFrameControl.encoding width).encode state)
    <;> by_cases reference : left = right <;>
      simp only [localRow, reference, ite_true, ite_false,
        and_true, and_false, mul_one, mul_zero]

/-- The trace retains both product passes, all H-CNOT-H blocks and negative-control X gates. -/
lemma reusedProductControlled_trace (width : Nat) (modulus : Fin (2 ^ width + 1))
    (active : Bool) (mask : Fin width → Bool)
    (layout : QubitLayout (NativeFrameControl.encoding width).width) :
    (program width modulus active mask layout).eventTrace =
      (computeGates width modulus).map (event .empty) ++
        (if active then (PhaseCorrection.selected mask).flatMap
          (fun _ => [.gate .singleQubit, .gate .cnot, .gate .singleQubit]) else
          [.gate .singleQubit] ++ (PhaseCorrection.selected mask).flatMap
            (fun _ => [.gate .singleQubit, .gate .cnot, .gate .singleQubit]) ++
              [.gate .singleQubit]) ++
        ((computeGates width modulus).map (event .empty)).reverse := by
  simp only [program, UnitaryCircuit.seq_eventTrace, programList_eventTrace,
    PhaseCorrection.Controlled.program,
    PhaseCorrection.Controlled.controlledPhaseCorrection_sequence_trace, List.map_reverse,
    List.append_assoc]

/-- The exact resource pool counts both literal passes and every actual selected phase gate. -/
lemma reusedProductControlled_cost (width : Nat) (modulus : Fin (2 ^ width + 1))
    (active : Bool) (mask : Fin width → Bool)
    (layout : QubitLayout (NativeFrameControl.encoding width).width) :
    (program width modulus active mask layout).eventCost =
      ResourcePool.ofList ((computeGates width modulus).map (event .empty)) +
        ((PhaseCorrection.selected mask).length •
          (2 • ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
            (.gate .singleQubit) +
            ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)) +
          (if active then 0 else 2 •
            ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
              (.gate .singleQubit))) +
        ResourcePool.ofList (((computeGates width modulus).map (event .empty)).reverse) := by
  simp only [program, UnitaryCircuit.seq_eventCost, programList_eventCost,
    PhaseCorrection.Controlled.program,
    PhaseCorrection.Controlled.controlledPhaseCorrection_sequence_cost, List.map_reverse,
    add_assoc]

/-- Exact serial count includes both passes and both negative-control flips. -/
lemma reusedProductControlled_depth (width : Nat) (modulus : Fin (2 ^ width + 1))
    (active : Bool) (mask : Fin width → Bool)
    (layout : QubitLayout (NativeFrameControl.encoding width).width) :
    (program width modulus active mask layout).evaluatedEventDepth (fun _ => 1) =
      2 * (computeGates width modulus).length + 3 * (PhaseCorrection.selected mask).length +
        (if active then 0 else 2) := by
  simp only [program, UnitaryCircuit.evaluatedEventDepth_seq,
    programList_evaluatedEventDepth_unit, PhaseCorrection.Controlled.program,
    PhaseCorrection.Controlled.controlledPhaseCorrection_sequence_depth, List.length_reverse]
  omega

/-- The original independent multiplication bound controls the complete phase-correction depth. -/
lemma reusedProductControlled_depth_bound (width : Nat) (modulus : Fin (2 ^ width + 1))
    (active : Bool) (mask : Fin width → Bool)
    (layout : QubitLayout (NativeFrameControl.encoding width).width) :
    (program width modulus active mask layout).evaluatedEventDepth (fun _ => 1) ≤
      2 * MAU.Multiplication.VariableGidney.eventBound width + 3 * width +
        (if active then 0 else 2) := by
  rw [reusedProductControlled_depth]
  have source := NativeProductFrame.nativeProductFrame_gates_length_bound width modulus
  have length : (computeGates width modulus).length =
      (NativeProductFrame.gates width modulus).length := by
    simp only [computeGates, List.length_map]
  have selected := PhaseCorrection.phaseCorrection_selected_count_le mask
  rw [length]
  omega

end

end QuantumAlg.MeasuredUncompute.ReusedProduct.Controlled
