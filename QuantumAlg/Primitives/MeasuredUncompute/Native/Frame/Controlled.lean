/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Product.Placement
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Product

/-!
# Native control on the complete measured arithmetic frame

Every borrowed position belongs to the original complete frame and is restored
for every initial value. The supplied quantum control occupies the final wire.
-/

namespace QuantumAlg.MeasuredUncompute.NativeFrameControl

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open MAU.Multiplication ProductPlacement EncodedBit GateSpec

/-- The complete original frame followed by its supplied quantum control. -/
abbrev encoding (width : Nat) : BinaryLabelEncoding (Frame width × Bool) :=
  BinaryLabelEncoding.prod (frameEncoding width) BinaryLabelEncoding.bool

private def productBits (width : Nat) :
    Fin (VariableGidney.encoding width).width → EncodedBit (VariableGidney.encoding width) :=
  productBit (BinaryLabelEncoding.finIdentityBit width)
    (productBit (BinaryLabelEncoding.finIdentityBit width)
      (BinaryLabelEncoding.finIdentityBit width))

private lemma productBits_wire (width : Nat)
    (position : Fin (VariableGidney.encoding width).width) :
    (productBits width position).wire = position :=
  productBit_wire (left := BinaryLabelEncoding.finIdentity width)
    (right := BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity width)
      (BinaryLabelEncoding.finIdentity width)) (BinaryLabelEncoding.finIdentityBit width)
    (productBit (BinaryLabelEncoding.finIdentityBit width)
      (BinaryLabelEncoding.finIdentityBit width))
    (fun _ => rfl)
    (productBit_wire (left := BinaryLabelEncoding.finIdentity width)
      (right := BinaryLabelEncoding.finIdentity width) (BinaryLabelEncoding.finIdentityBit width)
      (BinaryLabelEncoding.finIdentityBit width) (fun _ => rfl) (fun _ => rfl)) position

private def sourceBits (width : Nat) :
    Fin (sourceEncoding width).width → EncodedBit (sourceEncoding width) :=
  productBit (productBits width) (BinaryLabelEncoding.finIdentityBit (historyWidth width))

private lemma sourceBits_wire (width : Nat) (position : Fin (sourceEncoding width).width) :
    (sourceBits width position).wire = position :=
  productBit_wire (left := VariableGidney.encoding width)
    (right := BinaryLabelEncoding.finIdentity (historyWidth width))
    (productBits width) (BinaryLabelEncoding.finIdentityBit (historyWidth width))
    (productBits_wire width) (fun _ => rfl) position

private def frameBits (width : Nat) (position : Fin (frameEncoding width).width) :
    EncodedBit (frameEncoding width) :=
  (placement width).placeBit (sourceBits width ((wires width).symm position))

private lemma frameBits_wire (width : Nat) (position : Fin (frameEncoding width).width) :
    (frameBits width position).wire = position := by
  apply Fin.ext
  change (placement width).physicalIndex
    (sourceBits width ((wires width).symm position)).wire.val = position.val
  rw [sourceBits_wire]
  change FullPlacement.wireAddress (sourceEncoding width) (frameEncoding width)
    (wires width) ((wires width).symm position).val = position.val
  simp only [FullPlacement.wireAddress, dif_pos ((wires width).symm position).isLt]
  exact congrArg Fin.val ((wires width).apply_symm_apply position)

private def controlBits (_position : Fin BinaryLabelEncoding.bool.width) :
    EncodedBit BinaryLabelEncoding.bool := BinaryLabelEncoding.boolBit

private lemma controlBits_wire (position : Fin BinaryLabelEncoding.bool.width) :
    (controlBits position).wire = position := by
  apply Fin.ext
  have bound : position.val < 1 := position.isLt
  change 0 = position.val
  omega

def bits (width : Nat) : Fin (encoding width).width → EncodedBit (encoding width) :=
  productBit (frameBits width) controlBits

lemma nativeFrameControl_bits_wire (width : Nat) (position : Fin (encoding width).width) :
    (bits width position).wire = position :=
  productBit_wire (frameBits width) controlBits (frameBits_wire width) controlBits_wire position

def control (width : Nat) : EncodedBit (encoding width) :=
  BinaryLabelEncoding.prodRightBit (frameEncoding width) BinaryLabelEncoding.bool
    BinaryLabelEncoding.boolBit

lemma nativeFrameControl_capacity (width : Nat) : 5 ≤ (encoding width).width := by
  change 5 ≤ (frameEncoding width).width + 1
  rw [frame_width]
  unfold ProductWires.width tailWidth
  omega

private def lifted (width : Nat) (source : List (GateSpec (frameEncoding width))) :=
  source.map (GateSpec.prodLeft BinaryLabelEncoding.bool)

private lemma lifted_disjoint (width : Nat) (source : List (GateSpec (frameEncoding width))) :
    ∀ gate, gate ∈ lifted width source → bitDisjoint (control width) gate := by
  intro gate present
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp present
  exact bitDisjoint_prodLeft_rightBit (frameEncoding width) BinaryLabelEncoding.bool
    BinaryLabelEncoding.boolBit original

/-- The positive-control expansion borrows only existing frame positions. -/
def positiveGates (width : Nat) (source : List (GateSpec (frameEncoding width))) :
    List (GateSpec (encoding width)) :=
  controlWithin (bits width) (nativeFrameControl_bits_wire width)
    (nativeFrameControl_capacity width) (control width) (lifted width source)
    (lifted_disjoint width source)

/-- Negative selection uses two actual control flips. -/
def gates (width : Nat) (active : Bool) (source : List (GateSpec (frameEncoding width))) :
    List (GateSpec (encoding width)) :=
  if active then positiveGates width source
  else [.x (control width)] ++ positiveGates width source ++ [.x (control width)]

/-- The full original state is retained outside the selected sector. -/
def step (width : Nat) (active : Bool) (action : Frame width → Frame width)
    (state : Frame width × Bool) : Frame width × Bool :=
  (if state.2 = active then action state.1 else state.1, state.2)

private lemma positive_step (width : Nat) (source : List (GateSpec (frameEncoding width)))
    (state : Frame width × Bool) :
    stepList (positiveGates width source) state =
      (if state.2 then stepList source state.1 else state.1, state.2) := by
  erw [positiveGates, controlWithin_step]
  change (if state.2 then stepList (lifted width source) state else state) = _
  rw [lifted, stepList_prodLeft]
  rcases state with ⟨frame, selected⟩
  cases selected <;> rfl

/-- Exact all-label selection includes restoration of every temporary dirty value. -/
lemma nativeFrameControl_gates_step (width : Nat) (active : Bool)
    (source : List (GateSpec (frameEncoding width))) (state : Frame width × Bool) :
    stepList (gates width active source) state = step width active (stepList source) state := by
  rcases state with ⟨frame, selected⟩
  cases active
  · simp only [gates, Bool.false_eq_true, ↓reduceIte, stepList_append]
    change (control width).flip
      (stepList (positiveGates width source) ((control width).flip (frame, selected))) = _
    rw [positive_step]
    cases selected <;> rfl
  · rw [gates, if_pos rfl, positive_step]
    cases selected <;> rfl

/-- Reversing the emitted word realizes the exact inverse without recompiling borrowed blocks. -/
lemma nativeFrameControl_reverseGates_step (width : Nat) (active : Bool)
    (source : List (GateSpec (frameEncoding width))) (state : Frame width × Bool) :
    stepList (gates width active source).reverse state =
      step width active (stepList source.reverse) state := by
  have cancels : stepList (gates width active source)
      (step width active (stepList source.reverse) state) = state := by
    rw [nativeFrameControl_gates_step]
    have inverse (frame : Frame width) :
        stepList source (stepList source.reverse frame) = frame := by
      simpa only [List.reverse_reverse] using stepList_reverse_stepList source.reverse frame
    rcases state with ⟨frame, selected⟩
    cases active <;> cases selected <;> simp [step, inverse]
  have restored := congrArg (stepList (gates width active source).reverse) cancels
  rw [stepList_reverse_stepList] at restored
  exact restored.symm

/-- Actual native instructions on the supplied physical layout. -/
def program (width : Nat) (active : Bool) (source : List (GateSpec (frameEncoding width)))
    (layout : QubitLayout (encoding width).width) :
    UnitaryCircuit AlgorithmGate.model .empty layout.toQuantum :=
  programList layout .empty (gates width active source)

/-- Coherent action preserves the exact relative phase of both control sectors. -/
lemma nativeFrameControl_realizes (width : Nat) (active : Bool)
    (source : List (GateSpec (frameEncoding width)))
    (layout : QubitLayout (encoding width).width) :
    UnitaryCircuit.Realizes (layout := layout) (encoding width)
      (program width active source layout) environment (step width active (stepList source)) :=
  realizesList_congrStep layout .empty _ (nativeFrameControl_gates_step width active source)
    environment

/-- Physical selection uses the original final control position even at width zero. -/
lemma nativeFrameControl_control_position (width : Nat) :
    (control width).wire.val = (frameEncoding width).width := by
  change (frameEncoding width).width + 0 = _
  omega

/-- Ordered trace records every emitted gate, including the negative-control wrappers. -/
lemma nativeFrameControl_trace (width : Nat) (active : Bool)
    (source : List (GateSpec (frameEncoding width)))
    (layout : QubitLayout (encoding width).width) :
    (program width active source layout).eventTrace =
      (gates width active source).map (event .empty) :=
  programList_eventTrace layout .empty _

/-- Exact native coordinates charge the complete arbitrary-dirty expansion. -/
lemma nativeFrameControl_counts (width : Nat) (active : Bool)
    (source : List (GateSpec (frameEncoding width))) :
    ((gates width active source).map xMultiplicity).sum = (if active then 0 else 2) ∧
      ((gates width active source).map cnotMultiplicity).sum =
        ((lifted width source).map xMultiplicity).sum ∧
      ((gates width active source).map toffoliMultiplicity).sum =
        ((lifted width source).map cnotMultiplicity).sum +
          4 * ((lifted width source).map toffoliMultiplicity).sum := by
  have counts := controlWithin_native_counts (bits width) (nativeFrameControl_bits_wire width)
    (nativeFrameControl_capacity width) (control width) (lifted width source)
    (lifted_disjoint width source)
  change ((positiveGates width source).map xMultiplicity).sum = 0 ∧
    ((positiveGates width source).map cnotMultiplicity).sum = _ ∧
    ((positiveGates width source).map toffoliMultiplicity).sum = _ at counts
  cases active <;> simp [gates, counts.1, counts.2.1, counts.2.2]

/-- The independent source length bounds both positive and negative native expansions. -/
lemma nativeFrameControl_length_bound (width : Nat) (active : Bool)
    (source : List (GateSpec (frameEncoding width))) :
    (gates width active source).length ≤ 4 * source.length + (if active then 0 else 2) := by
  have bound := controlWithin_length_bound (bits width) (nativeFrameControl_bits_wire width)
    (nativeFrameControl_capacity width) (control width) (lifted width source)
    (lifted_disjoint width source)
  change (positiveGates width source).length ≤ 4 * (lifted width source).length at bound
  simp only [lifted, List.length_map] at bound
  cases active <;> simp only [gates, Bool.false_eq_true, ↓reduceIte, List.length_append,
    List.length_cons, List.length_nil] <;> omega

end

end QuantumAlg.MeasuredUncompute.NativeFrameControl
