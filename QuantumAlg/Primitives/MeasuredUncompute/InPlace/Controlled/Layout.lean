/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.OperatorAgreement
import all QuantumAlg.Core.Execution.Context.Union.Store.Laws
import all QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Primitives.MeasuredUncompute.Native.Frame.Controlled
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Inverse.Runtime.Frame
import all QuantumAlg.Core.Base.Layout.Quantum.IdentityPosition
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Entries
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Runtime
import all QuantumAlg.Util.FinPow.BinaryBasis.Append

/-!
# One actual owned control beside the measured arithmetic frame

The original X/Y/A wires, complete EEA history and retained finite result
cells keep their identities. A separate supplied owned control occupies the
next physical address. The complete runtime basis follows those actual wire
records, so coherent control is not a classical store value or an uncharged
external reference. The three-field-register arithmetic is the existing
measured sequence [LYL+26, sec_point_add/sec_point_add.tex:24-36,52-121].
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceControlled

noncomputable section

open Execution MAU.Inversion.SharedEEA ContextUnion

/-- The original complete three-word native width, including all EEA history. -/
@[reducible] def frameWidth (width : Nat) : Nat := (OutputCopy.encoding width).width

/-- The new owned control follows every original native wire. -/
def controlWire (width : Nat) : Nat := frameWidth width

private lemma original_bounded (width : Nat) (wire : Nat)
    (present : wire ∈ (NumeratorMeasurement.context width).physicalIdx) :
    wire < frameWidth width := by
  rw [NumeratorMeasurement.context_physical, InverseRuntimeFrame.after_physical] at present
  rcases List.mem_append.mp present with auxiliary | supplied
  · change wire ∈ List.ofFn (InputPreparation.auxiliaryPhysicalIndex width) at auxiliary
    obtain ⟨index, same⟩ := List.mem_ofFn.mp auxiliary
    have bound := (InputAssembly.auxiliaryPosition width index).isLt
    change InputPreparation.auxiliaryPhysicalIndex width index < (encoding width).width at bound
    rw [← same]
    change InputPreparation.auxiliaryPhysicalIndex width index < (encoding width).width + width
    omega
  · change wire ∈ List.ofFn
      (fun index : Fin (width + width) => InversePreparation.physicalIndex width index.val)
        at supplied
    obtain ⟨index, same⟩ := List.mem_ofFn.mp supplied
    have bound := index.isLt
    rw [← same]
    change InversePreparation.physicalIndex width index.val < (encoding width).width + width
    unfold InversePreparation.physicalIndex
    have complete := InputPreparation.complete_width width
    unfold InputPreparation.auxiliaryWidth InputPreparation.suffixWidth at complete
    split <;> omega

/-- The supplied control is one actual dimension-two system. -/
def controlQubitLayout (width : Nat) : QubitLayout 1 where
  physical_idx _ := controlWire width
  physical_idx_injective := fun _ _ _ => Subsingleton.elim _ _

def controlLayout (width : Nat) : QuantumLayout 1 :=
  (controlQubitLayout width).toQuantumLayout

/-- Its storage identity is fresh for all retained measurement cells. -/
def controlKey (width : Nat) : StorageKey :=
  (NumeratorMeasurement.context width).canonicalFreshKey

/-- A genuinely supplied owned control, without an initialization promise. -/
def controlContext (width : Nat) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addOwnedLayout (controlKey width) (controlLayout width) (by exact
    List.not_mem_nil)
    (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])

lemma controlContext_physical (width : Nat) :
    (controlContext width).physicalIdx = [controlWire width] := by
  change ((controlLayout width).wires ++ []).map QuantumWire.identity = _
  simp only [List.append_nil, QuantumLayout.wires, List.map_ofFn]
  change List.ofFn (fun _ : Fin 1 => controlWire width) = _
  simp

lemma control_disjoint (width : Nat) :
    RuntimeCtx.StorageDisjoint (NumeratorMeasurement.context width) (controlContext width) := by
  constructor
  · apply (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mpr
    change List.Disjoint (NumeratorMeasurement.context width).keys [controlKey width]
    apply List.disjoint_left.mpr
    intro key present singleton
    have same := List.mem_singleton.mp singleton
    rw [same] at present
    exact (NumeratorMeasurement.context width).canonicalFreshKey_fresh present
  · apply (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mpr
    rw [controlContext_physical]
    apply List.disjoint_left.mpr
    intro wire present singleton
    have same := List.mem_singleton.mp singleton
    rw [same] at present
    have bound := original_bounded width (controlWire width) present
    exact (Nat.lt_irrefl (frameWidth width)) bound

/-- The already allocated measured body and its physically charged quantum control. -/
@[reducible] def context (width : Nat) : RuntimeCtx .quantum :=
  (NumeratorMeasurement.context width).disjointUnion (controlContext width)
    (control_disjoint width)

lemma context_physical (width : Nat) :
    (context width).physicalIdx =
      (NumeratorMeasurement.context width).physicalIdx ++ [controlWire width] := by
  rw [context, RuntimeCtx.physicalIdx_disjointUnion, controlContext_physical]

private lemma control_wires (width : Nat) :
    (controlLayout width).wires = (controlContext width).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change (controlLayout width).wires = (controlLayout width).wires ++ []
  exact (List.append_nil _).symm

/-- The real owned control has the canonical finite one-bit basis. -/
def controlBasis (width : Nat) : (controlContext width).register.Index ≃ Fin 2 :=
  (basisOfEqualWires (controlLayout width) (controlContext width).quantumLayout
    (control_wires width)).symm.trans (controlQubitLayout width).binaryIndexEquiv

/-- Exact binary assembly: the leading logical control is the appended physical control. -/
def basis (width : Nat) : (context width).register.Index ≃ Fin (2 ^ (1 + frameWidth width)) :=
  (unionBasisEquiv (NumeratorMeasurement.context width) (controlContext width)
    (control_disjoint width)).trans
      ((Equiv.prodCongr (NumeratorMeasurement.frameBasis width) (controlBasis width)).trans
        ((Equiv.prodComm _ _).trans (prodEquiv (m := 1) (n := frameWidth width))))

/-- Native basis labels retain every real control, arithmetic and history coordinate. -/
def label (width : Nat) (control : Fin 2)
    (original : (NumeratorMeasurement.context width).register.Index) :
    (context width).register.Index :=
  (unionBasisEquiv (NumeratorMeasurement.context width) (controlContext width)
    (control_disjoint width)).symm (original, (controlBasis width).symm control)

lemma basis_label (width : Nat) (control : Fin 2)
    (original : (NumeratorMeasurement.context width).register.Index) :
    basis width (label width control original) =
      prodEquiv (control, NumeratorMeasurement.frameBasis width original) := by
  change (prodEquiv (m := 1) (n := frameWidth width))
    (controlBasis width ((unionBasisEquiv _ _ (control_disjoint width))
      ((unionBasisEquiv _ _ (control_disjoint width)).symm
        (original, (controlBasis width).symm control))).2,
     NumeratorMeasurement.frameBasis width
      ((unionBasisEquiv _ _ (control_disjoint width))
        ((unionBasisEquiv _ _ (control_disjoint width)).symm
          (original, (controlBasis width).symm control))).1) = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The original actual finite-result read survives the union unchanged. -/
def resultInput (width : Nat) : CInputRef (context width) (.fixedVector width (.finite 2)) :=
  inputLeft (control_disjoint width) (NumeratorMeasurement.input width)

/-- Every retained classical cell belongs to the original source store. -/
lemma resultInput_read (width : Nat) (store : Store (context width)) :
    store.read (resultInput width) =
      ((storeEquiv (control_disjoint width) store).1).read (NumeratorMeasurement.input width) := by
  obtain ⟨⟨first, second⟩, rfl⟩ := (storeEquiv (control_disjoint width)).symm.surjective store
  rw [Equiv.apply_symm_apply]
  exact contextUnion_read_join_left (control_disjoint width) first second _

/-- Every native address and the real control occurs in the complete actual context. -/
lemma native_contained (width : Nat) :
    List.range (1 + frameWidth width) ⊆ (context width).physicalIdx := by
  intro wire present
  have bound := List.mem_range.mp present
  rw [context_physical]
  by_cases original : wire < frameWidth width
  · apply List.mem_append_left
    rw [NumeratorMeasurement.context_physical]
    exact InverseRuntimeFrame.range_contained width (List.mem_range.mpr original)
  · apply List.mem_append_right
    have same : wire = controlWire width := by unfold controlWire; omega
    exact List.mem_singleton.mpr same

/-- The native arithmetic frame followed by its actual final control, with original addresses. -/
abbrev nativeLayout (width : Nat) :=
  QubitLayout.canonical (NativeFrameControl.encoding width).width

private lemma native_identities_contained (width : Nat) :
    (nativeLayout width).toQuantum.identities ⊆ (context width).quantumLayout.identities := by
  rw [RuntimeCtx.runtimeCtx_quantumLayout_identities]
  change (nativeLayout width).systemIdx ⊆ _
  rw [QubitLayout.canonical_systemIdx]
  change List.range ((ProductPlacement.frameEncoding width).width + 1) ⊆ _
  have contained := native_contained width
  change List.range (1 + (ProductPlacement.frameEncoding width).width) ⊆ _ at contained
  simpa only [Nat.add_comm] using contained

private lemma context_identities_contained (width : Nat) :
    (context width).quantumLayout.identities ⊆ (nativeLayout width).toQuantum.identities := by
  rw [RuntimeCtx.runtimeCtx_quantumLayout_identities]
  change (context width).physicalIdx ⊆ (nativeLayout width).systemIdx
  rw [QubitLayout.canonical_systemIdx]
  intro identity present
  rw [context_physical] at present
  apply List.mem_range.mpr
  rcases List.mem_append.mp present with original | control
  · have bound := original_bounded width identity original
    change identity < (ProductPlacement.frameEncoding width).width + 1
    change identity < (ProductPlacement.frameEncoding width).width at bound
    omega
  · have same := List.mem_singleton.mp control
    rw [same]
    change (ProductPlacement.frameEncoding width).width <
      (ProductPlacement.frameEncoding width).width + 1
    omega

/-- Every native address selects the runtime wire bearing that same physical identity. -/
def nativePosition (width : Nat) :
    Fin (NativeFrameControl.encoding width).width ↪ Fin (context width).systemCount :=
  QuantumLayout.positionOfIdentity (nativeLayout width).toQuantum (context width).quantumLayout
    (native_identities_contained width)

/-- The physical placement covers every live wire, including every dirty history position. -/
lemma nativePosition_surjective (width : Nat) : Function.Surjective (nativePosition width) :=
  QuantumLayout.positionOfIdentity_surjective (nativeLayout width).toQuantum
    (context width).quantumLayout (native_identities_contained width)
    (context_identities_contained width)

/-- The native placement never relabels a physical address. -/
lemma nativePosition_identity (width : Nat)
    (index : Fin (NativeFrameControl.encoding width).width) :
    ((context width).quantumLayout.wire (nativePosition width index)).identity = index.val :=
  QuantumLayout.positionOfIdentity_identity (nativeLayout width).toQuantum
    (context width).quantumLayout (native_identities_contained width) index

private lemma context_dimension (width : Nat) (index : Fin (context width).systemCount) :
    ((context width).quantumLayout.wire index).dimension = 2 := by
  obtain ⟨position, rfl⟩ :=
    (unionPositionEquiv (NumeratorMeasurement.context width) (controlContext width)
      (control_disjoint width)).surjective index
  cases position with
  | inl original =>
      change (((NumeratorMeasurement.context width).disjointUnion (controlContext width)
        (control_disjoint width)).quantumLayout.wire
        (leftPosition (NumeratorMeasurement.context width) (controlContext width)
          (control_disjoint width) original)).dimension = 2
      rw [contextUnion_left_wire]
      obtain ⟨old, rfl⟩ :=
        (MeasurementCells.wireEquiv (InversePreparation.after width) 2 width).surjective original
      change ((MeasurementCells.context (InversePreparation.after width) 2 width).quantumLayout.wire
        (MeasurementCells.wireEquiv (InversePreparation.after width) 2 width old)).dimension = 2
      rw [MeasurementCells.wireEquiv_preserved]
      exact InverseRuntimeFrame.after_dimension width old
  | inr control =>
      change (((NumeratorMeasurement.context width).disjointUnion (controlContext width)
        (control_disjoint width)).quantumLayout.wire
        (rightPosition (NumeratorMeasurement.context width) (controlContext width)
          (control_disjoint width) control)).dimension = 2
      rw [contextUnion_right_wire]
      obtain ⟨old, rfl⟩ := (positionsOfEqualWires (controlLayout width)
        (controlContext width).quantumLayout (control_wires width)).surjective control
      rw [wireAtCorrespondingPosition (controlLayout width)
        (controlContext width).quantumLayout (control_wires width) old]
      rfl

/-- The same identity placement retains the certified dimension of every original qubit. -/
lemma nativePosition_dimensions (width : Nat)
    (index : Fin (NativeFrameControl.encoding width).width) :
    ((nativeLayout width).toQuantum.wire index).dimension =
      ((context width).quantumLayout.wire (nativePosition width index)).dimension := by
  rw [context_dimension]
  rfl

/-- Read precisely the native coordinates selected by the actual complete physical placement. -/
def nativeBasis (width : Nat) (state : (context width).register.Index) :
    (nativeLayout width).toQuantum.register.Index :=
  UnitaryCircuit.basisAt (nativeLayout width).toQuantum (context width).quantumLayout
    (nativePosition width) (nativePosition_dimensions width) state

private lemma nativePosition_left (width : Nat)
    (index : Fin (ProductPlacement.frameEncoding width).width) :
    nativePosition width (Fin.castAdd 1 index) =
      ContextUnion.leftPosition (NumeratorMeasurement.context width) (controlContext width)
        (control_disjoint width)
        (MeasurementCells.wireEquiv (InversePreparation.after width) 2 width
          (InverseRuntimeFrame.position width index)) := by
  apply (context width).quantumLayout.identityInjective
  have joined := ContextUnion.contextUnion_left_wire (NumeratorMeasurement.context width)
    (controlContext width) (control_disjoint width)
    (MeasurementCells.wireEquiv (InversePreparation.after width) 2 width
      (InverseRuntimeFrame.position width index))
  have retained := MeasurementCells.wireEquiv_preserved (InversePreparation.after width) 2 width
    (InverseRuntimeFrame.position width index)
  exact (nativePosition_identity width (Fin.castAdd 1 index)).trans
    ((congrArg QuantumWire.identity joined).trans
      ((congrArg QuantumWire.identity retained).trans
        (InverseRuntimeFrame.position_identity width index))).symm

private lemma nativeBasis_label_left (width : Nat) (control : Fin 2)
    (original : (NumeratorMeasurement.context width).register.Index)
    (index : Fin (ProductPlacement.frameEncoding width).width) :
    (nativeBasis width (label width control original) (Fin.castAdd 1 index)).val =
      ((QubitLayout.canonical (ProductPlacement.frameEncoding width).width).basisEquiv.symm
        (NumeratorMeasurement.frameBasis width original) index).val := by
  have split := ContextUnion.contextUnion_split_left_value
    (NumeratorMeasurement.context width) (controlContext width) (control_disjoint width)
    (label width control original)
    (MeasurementCells.wireEquiv (InversePreparation.after width) 2 width
      (InverseRuntimeFrame.position width index))
  simp only [label, Equiv.apply_symm_apply] at split
  have retained := MeasurementCells.basisEquiv_value (InversePreparation.after width) 2 width
    ((MeasurementCells.basisEquiv (InversePreparation.after width) 2 width).symm original)
    (InverseRuntimeFrame.position width index)
  have roundtrip := congrArg
    (fun basis => (basis (MeasurementCells.wireEquiv (InversePreparation.after width) 2 width
      (InverseRuntimeFrame.position width index))).val)
    ((MeasurementCells.basisEquiv (InversePreparation.after width) 2 width).apply_symm_apply
      original)
  have selected := congrArg (fun basis => (basis index).val)
    (NumeratorRuntime.selected_basis width original)
  rw [NumeratorRuntime.frameCoordinates_eq_cells] at selected
  change (label width control original (nativePosition width (Fin.castAdd 1 index))).val = _
  rw [nativePosition_left]
  exact split.trans (roundtrip.symm.trans (retained.trans selected))

private lemma nativePosition_right (width : Nat) (index : Fin 1) :
    nativePosition width (Fin.natAdd (ProductPlacement.frameEncoding width).width index) =
      ContextUnion.rightPosition (NumeratorMeasurement.context width) (controlContext width)
        (control_disjoint width)
        (positionsOfEqualWires (controlLayout width) (controlContext width).quantumLayout
          (control_wires width) index) := by
  have zero : index = 0 := Subsingleton.elim _ _
  subst index
  apply (context width).quantumLayout.identityInjective
  have joined := ContextUnion.contextUnion_right_wire (NumeratorMeasurement.context width)
    (controlContext width) (control_disjoint width)
    (positionsOfEqualWires (controlLayout width) (controlContext width).quantumLayout
      (control_wires width) 0)
  have retained := wireAtCorrespondingPosition (controlLayout width)
    (controlContext width).quantumLayout (control_wires width) 0
  exact (nativePosition_identity width
    (Fin.natAdd (ProductPlacement.frameEncoding width).width (0 : Fin 1))).trans
      ((congrArg QuantumWire.identity joined).trans
        (congrArg QuantumWire.identity retained)).symm

private lemma nativeBasis_label_right (width : Nat) (control : Fin 2)
    (original : (NumeratorMeasurement.context width).register.Index) (index : Fin 1) :
    (nativeBasis width (label width control original)
      (Fin.natAdd (ProductPlacement.frameEncoding width).width index)).val =
      ((QubitLayout.canonical 1).basisEquiv.symm control index).val := by
  have split := ContextUnion.contextUnion_split_right_value
    (NumeratorMeasurement.context width) (controlContext width) (control_disjoint width)
    (label width control original)
    (positionsOfEqualWires (controlLayout width) (controlContext width).quantumLayout
      (control_wires width) index)
  simp only [label, Equiv.apply_symm_apply] at split
  have retained := basisOfEqualWires_value (controlLayout width)
    (controlContext width).quantumLayout (control_wires width)
    ((controlQubitLayout width).binaryIndexEquiv.symm control) index
  change (label width control original
    (nativePosition width (Fin.natAdd (ProductPlacement.frameEncoding width).width index))).val = _
  rw [nativePosition_right]
  exact split.trans retained

/-- The exact native readout appends the supplied control after the entire original frame. -/
lemma controlledNativeBasis_label (width : Nat) (control : Fin 2)
    (original : (NumeratorMeasurement.context width).register.Index) :
    nativeBasis width (label width control original) =
      (nativeLayout width).basisEquiv.symm
        (prodEquiv (NumeratorMeasurement.frameBasis width original, control)) := by
  let originalLabel : Fin (2 ^ (ProductPlacement.frameEncoding width).width) :=
    NumeratorMeasurement.frameBasis width original
  change (fun index : Fin ((ProductPlacement.frameEncoding width).width + 1) =>
    nativeBasis width (label width control original) index) =
      (BinaryBasis.bigEndianEquiv ((ProductPlacement.frameEncoding width).width + 1)).symm
        (prodEquiv (originalLabel, control))
  rw [BinaryBasis.bigEndianEquiv_symm_prod
    (leftWidth := (ProductPlacement.frameEncoding width).width) (rightWidth := 1)]
  funext index
  refine Fin.addCases (m := (ProductPlacement.frameEncoding width).width) (n := 1)
    (fun first => ?_) (fun last => ?_) index
  · simp only [Fin.addCases_left]
    apply Fin.ext
    exact nativeBasis_label_left width control original first
  · simp only [Fin.addCases_right]
    apply Fin.ext
    exact nativeBasis_label_right width control original last



end

end QuantumAlg.MeasuredUncompute.InPlaceControlled
