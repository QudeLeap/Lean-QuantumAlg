/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Field
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Controlled.Layout
import all QuantumAlg.Primitives.MeasuredUncompute.Frame.Ports

/-!
# Actual measured affine point-addition boundary

The supplied coherent control activates ordinary affine addition by one fixed
classical point. Only the active input excludes that point and its inverse.
The exceptional second multiplier is handled internally, without imposing a
reverse-addition domain [LYL+26, sec_point_add/sec_point_add.tex:24-36,119-123].
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition

noncomputable section

open Execution ContextUnion MeasuredUncompute

/-- The complete original field frame and both real quantum control bits. -/
abbrev Raw (width : Nat) := (ProductPlacement.Frame width × Bool) × Bool

/-- Logical bits follow their original physical frame order, then C and then N. -/
def encoding (width : Nat) : BinaryLabelEncoding (Raw width) :=
  BinaryLabelEncoding.prod
    (BinaryLabelEncoding.prod (ProductPlacement.frameEncoding width) BinaryLabelEncoding.bool)
    BinaryLabelEncoding.bool

/-- The only new qubit follows the frozen arithmetic body's supplied control. -/
def selectorWire (width : Nat) : Nat := InPlaceControlled.frameWidth width + 1

def selectorQubitLayout (width : Nat) : QubitLayout 1 where
  physical_idx _ := selectorWire width
  physical_idx_injective := fun _ _ _ => Subsingleton.elim _ _

def selectorLayout (width : Nat) : QuantumLayout 1 :=
  (selectorQubitLayout width).toQuantumLayout

/-- The internal selector owns a real key distinct from every original outcome and control. -/
def selectorKey (width : Nat) : StorageKey := (InPlaceControlled.context width).canonicalFreshKey

/-- This body receives the allocated selector; its enclosing preparation establishes zero. -/
def selectorContext (width : Nat) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addOwnedLayout (selectorKey width) (selectorLayout width)
    (by exact List.not_mem_nil)
    (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])

lemma selectorContext_physical (width : Nat) :
    (selectorContext width).physicalIdx = [selectorWire width] := by
  change ((selectorLayout width).wires ++ []).map QuantumWire.identity = _
  simp only [List.append_nil, QuantumLayout.wires, List.map_ofFn]
  change List.ofFn (fun _ : Fin 1 => selectorWire width) = _
  simp

lemma selector_disjoint (width : Nat) :
    RuntimeCtx.StorageDisjoint (InPlaceControlled.context width) (selectorContext width) := by
  constructor
  · apply (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mpr
    change List.Disjoint (InPlaceControlled.context width).keys [selectorKey width]
    apply List.disjoint_left.mpr
    intro key present singleton
    have same := List.mem_singleton.mp singleton
    rw [same] at present
    exact (InPlaceControlled.context width).canonicalFreshKey_fresh present
  · apply (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mpr
    rw [selectorContext_physical]
    apply List.disjoint_left.mpr
    intro wire present singleton
    have same := List.mem_singleton.mp singleton
    rw [same, InPlaceControlled.context_physical] at present
    rcases List.mem_append.mp present with original | control
    · have bound := InPlaceControlled.original_bounded width (selectorWire width) original
      unfold selectorWire at bound
      omega
    · have equal := List.mem_singleton.mp control
      unfold selectorWire InPlaceControlled.controlWire at equal
      omega

/-- Actual storage union keeps all field/history wires and reuses the same n finite cells. -/
@[reducible] def context (width : Nat) : RuntimeCtx .quantum :=
  (InPlaceControlled.context width).disjointUnion (selectorContext width)
    (selector_disjoint width)

lemma context_physical (width : Nat) :
    (context width).physicalIdx =
      (InPlaceControlled.context width).physicalIdx ++ [selectorWire width] := by
  rw [context, RuntimeCtx.physicalIdx_disjointUnion, selectorContext_physical]

private lemma selector_wires (width : Nat) :
    (selectorLayout width).wires = (selectorContext width).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change (selectorLayout width).wires = (selectorLayout width).wires ++ []
  exact (List.append_nil _).symm

/-- The real owned selector contributes precisely one binary quantum coordinate. -/
def selectorBasis (width : Nat) : (selectorContext width).register.Index ≃ Fin 2 :=
  (basisOfEqualWires (selectorLayout width) (selectorContext width).quantumLayout
    (selector_wires width)).symm.trans (selectorQubitLayout width).binaryIndexEquiv

private def frameControlBasis (width : Nat) :
    (InPlaceControlled.context width).register.Index ≃
      Fin (2 ^ (InPlaceControlled.frameWidth width + 1)) :=
  (unionBasisEquiv (NumeratorMeasurement.context width) (InPlaceControlled.controlContext width)
    (InPlaceControlled.control_disjoint width)).trans
      ((Equiv.prodCongr (NumeratorMeasurement.frameBasis width)
        (InPlaceControlled.controlBasis width)).trans
          (prodEquiv (m := InPlaceControlled.frameWidth width) (n := 1)))

/-- Complete runtime placement reads Frame,C,N in their actual physical bit order. -/
def basis (width : Nat) : (context width).register.Index ≃ Fin (2 ^ (encoding width).width) :=
  (unionBasisEquiv (InPlaceControlled.context width) (selectorContext width)
    (selector_disjoint width)).trans
      ((Equiv.prodCongr (frameControlBasis width) (selectorBasis width)).trans
        (prodEquiv (m := InPlaceControlled.frameWidth width + 1) (n := 1)))

/-- Full labels retain the old measured body basis and both quantum control values. -/
def label (width : Nat) (control selector : Fin 2)
    (original : (NumeratorMeasurement.context width).register.Index) :
    (context width).register.Index :=
  (unionBasisEquiv (InPlaceControlled.context width) (selectorContext width)
    (selector_disjoint width)).symm
      (InPlaceControlled.label width control original, (selectorBasis width).symm selector)

lemma basis_label (width : Nat) (control selector : Fin 2)
    (original : (NumeratorMeasurement.context width).register.Index) :
    basis width (label width control selector original) =
      prodEquiv (prodEquiv (NumeratorMeasurement.frameBasis width original, control),
        selector) := by
  change prodEquiv (m := InPlaceControlled.frameWidth width + 1) (n := 1)
    (frameControlBasis width
      ((unionBasisEquiv _ _ (selector_disjoint width))
        ((unionBasisEquiv _ _ (selector_disjoint width)).symm
          (InPlaceControlled.label width control original, (selectorBasis width).symm selector))).1,
    selectorBasis width ((unionBasisEquiv _ _ (selector_disjoint width))
      ((unionBasisEquiv _ _ (selector_disjoint width)).symm
        (InPlaceControlled.label width control original,
          (selectorBasis width).symm selector))).2) = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change prodEquiv (m := InPlaceControlled.frameWidth width + 1) (n := 1)
    (prodEquiv (m := InPlaceControlled.frameWidth width) (n := 1)
    (NumeratorMeasurement.frameBasis width
      ((unionBasisEquiv _ _ (InPlaceControlled.control_disjoint width))
        ((unionBasisEquiv _ _ (InPlaceControlled.control_disjoint width)).symm
          (original, (InPlaceControlled.controlBasis width).symm control))).1,
      InPlaceControlled.controlBasis width
        ((unionBasisEquiv _ _ (InPlaceControlled.control_disjoint width))
          ((unionBasisEquiv _ _ (InPlaceControlled.control_disjoint width)).symm
            (original, (InPlaceControlled.controlBasis width).symm control))).2), selector) = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- The same real finite result cells are read by both measured arithmetic calls. -/
def resultInput (width : Nat) : CInputRef (context width) (.fixedVector width (.finite 2)) :=
  inputLeft (selector_disjoint width) (InPlaceControlled.resultInput width)

/-- Every native physical position is an already resident owned qubit. -/
lemma native_contained (width : Nat) :
    List.range (encoding width).width ⊆ (context width).physicalIdx := by
  intro wire present
  have bound := List.mem_range.mp present
  rw [context_physical]
  by_cases old : wire < 1 + InPlaceControlled.frameWidth width
  · exact List.mem_append_left _ (InPlaceControlled.native_contained width (List.mem_range.mpr old))
  · have same : wire = selectorWire width := by
      change wire < (InPlaceControlled.frameWidth width + 1) + 1 at bound
      unfold selectorWire
      omega
    exact List.mem_append_right _ (List.mem_singleton.mpr same)

/-- Canonical physical coordinates cover the original frame, C, and N. -/
abbrev nativeLayout (width : Nat) := QubitLayout.canonical (encoding width).width

private lemma native_identities_contained (width : Nat) :
    (nativeLayout width).toQuantum.identities ⊆ (context width).quantumLayout.identities := by
  rw [RuntimeCtx.runtimeCtx_quantumLayout_identities]
  change (nativeLayout width).systemIdx ⊆ _
  rw [QubitLayout.canonical_systemIdx]
  exact native_contained width

private lemma context_identities_contained (width : Nat) :
    (context width).quantumLayout.identities ⊆ (nativeLayout width).toQuantum.identities := by
  rw [RuntimeCtx.runtimeCtx_quantumLayout_identities]
  change (context width).physicalIdx ⊆ (nativeLayout width).systemIdx
  rw [QubitLayout.canonical_systemIdx]
  intro identity present
  rw [context_physical] at present
  apply List.mem_range.mpr
  rcases List.mem_append.mp present with original | selector
  · rw [InPlaceControlled.context_physical] at original
    rcases List.mem_append.mp original with frame | control
    · have bound := InPlaceControlled.original_bounded width identity frame
      change identity < (InPlaceControlled.frameWidth width + 1) + 1
      omega
    · have same := List.mem_singleton.mp control
      rw [same]
      change InPlaceControlled.frameWidth width <
        (InPlaceControlled.frameWidth width + 1) + 1
      omega
  · have same := List.mem_singleton.mp selector
    rw [same]
    change InPlaceControlled.frameWidth width + 1 <
      (InPlaceControlled.frameWidth width + 1) + 1
    omega

/-- The runtime placement identifies the same owned wire at every native coordinate. -/
def nativePosition (width : Nat) :
    Fin (encoding width).width ↪ Fin (context width).systemCount :=
  QuantumLayout.positionOfIdentity (nativeLayout width).toQuantum (context width).quantumLayout
    (native_identities_contained width)

/-- Complete placement covers every original quantum coordinate, including arbitrary history. -/
lemma nativePosition_surjective (width : Nat) : Function.Surjective (nativePosition width) :=
  QuantumLayout.positionOfIdentity_surjective (nativeLayout width).toQuantum
    (context width).quantumLayout (native_identities_contained width)
    (context_identities_contained width)

/-- Every native wire keeps its original physical identity. -/
lemma nativePosition_identity (width : Nat) (index : Fin (encoding width).width) :
    ((context width).quantumLayout.wire (nativePosition width index)).identity = index.val :=
  QuantumLayout.positionOfIdentity_identity (nativeLayout width).toQuantum
    (context width).quantumLayout (native_identities_contained width) index

private lemma context_dimension (width : Nat) (index : Fin (context width).systemCount) :
    ((context width).quantumLayout.wire index).dimension = 2 := by
  obtain ⟨position, rfl⟩ :=
    (unionPositionEquiv (InPlaceControlled.context width) (selectorContext width)
      (selector_disjoint width)).surjective index
  cases position with
  | inl original =>
      change (((InPlaceControlled.context width).disjointUnion (selectorContext width)
        (selector_disjoint width)).quantumLayout.wire
        (leftPosition (InPlaceControlled.context width) (selectorContext width)
          (selector_disjoint width) original)).dimension = 2
      rw [contextUnion_left_wire]
      exact InPlaceControlled.context_dimension width original
  | inr selector =>
      change (((InPlaceControlled.context width).disjointUnion (selectorContext width)
        (selector_disjoint width)).quantumLayout.wire
        (rightPosition (InPlaceControlled.context width) (selectorContext width)
          (selector_disjoint width) selector)).dimension = 2
      rw [contextUnion_right_wire]
      obtain ⟨old, rfl⟩ := (positionsOfEqualWires (selectorLayout width)
        (selectorContext width).quantumLayout (selector_wires width)).surjective selector
      rw [wireAtCorrespondingPosition (selectorLayout width)
        (selectorContext width).quantumLayout (selector_wires width) old]
      rfl

/-- The physical embedding retains the certified dimension of every resident qubit. -/
lemma nativePosition_dimensions (width : Nat) (index : Fin (encoding width).width) :
    ((nativeLayout width).toQuantum.wire index).dimension =
      ((context width).quantumLayout.wire (nativePosition width index)).dimension := by
  rw [context_dimension]
  rfl

/-- Read every native value through the same complete physical placement. -/
def nativeBasis (width : Nat) (state : (context width).register.Index) :
    (nativeLayout width).toQuantum.register.Index :=
  UnitaryCircuit.basisAt (nativeLayout width).toQuantum (context width).quantumLayout
    (nativePosition width) (nativePosition_dimensions width) state

private lemma nativePosition_left (width : Nat)
    (index : Fin (NativeFrameControl.encoding width).width) :
    nativePosition width (Fin.castAdd 1 index) =
      leftPosition (InPlaceControlled.context width) (selectorContext width)
        (selector_disjoint width) (InPlaceControlled.nativePosition width index) := by
  apply (context width).quantumLayout.identityInjective
  have joined := contextUnion_left_wire (InPlaceControlled.context width) (selectorContext width)
    (selector_disjoint width) (InPlaceControlled.nativePosition width index)
  exact (nativePosition_identity width (Fin.castAdd 1 index)).trans
    ((congrArg QuantumWire.identity joined).trans
      (InPlaceControlled.nativePosition_identity width index)).symm

private lemma nativeBasis_label_left (width : Nat) (control selector : Fin 2)
    (original : (NumeratorMeasurement.context width).register.Index)
    (index : Fin (NativeFrameControl.encoding width).width) :
    (nativeBasis width (label width control selector original) (Fin.castAdd 1 index)).val =
      ((InPlaceControlled.nativeLayout width).basisEquiv.symm
        (prodEquiv (NumeratorMeasurement.frameBasis width original, control)) index).val := by
  have split := contextUnion_split_left_value
    (InPlaceControlled.context width) (selectorContext width) (selector_disjoint width)
    (label width control selector original) (InPlaceControlled.nativePosition width index)
  simp only [label, Equiv.apply_symm_apply] at split
  have originalBasis := congrArg (fun basis => (basis index).val)
    (InPlaceControlled.controlledNativeBasis_label width control original)
  change (label width control selector original
    (nativePosition width (Fin.castAdd 1 index))).val = _
  rw [nativePosition_left]
  exact split.trans originalBasis

private lemma nativePosition_right (width : Nat) (index : Fin 1) :
    nativePosition width (Fin.natAdd (NativeFrameControl.encoding width).width index) =
      rightPosition (InPlaceControlled.context width) (selectorContext width)
        (selector_disjoint width)
        (positionsOfEqualWires (selectorLayout width) (selectorContext width).quantumLayout
          (selector_wires width) index) := by
  have zero : index = 0 := Subsingleton.elim _ _
  subst index
  apply (context width).quantumLayout.identityInjective
  have joined := contextUnion_right_wire (InPlaceControlled.context width) (selectorContext width)
    (selector_disjoint width)
    (positionsOfEqualWires (selectorLayout width) (selectorContext width).quantumLayout
      (selector_wires width) 0)
  have retained := wireAtCorrespondingPosition (selectorLayout width)
    (selectorContext width).quantumLayout (selector_wires width) 0
  exact (nativePosition_identity width
    (Fin.natAdd (NativeFrameControl.encoding width).width (0 : Fin 1))).trans
      ((congrArg QuantumWire.identity joined).trans
        (congrArg QuantumWire.identity retained)).symm

private lemma nativeBasis_label_right (width : Nat) (control selector : Fin 2)
    (original : (NumeratorMeasurement.context width).register.Index) (index : Fin 1) :
    (nativeBasis width (label width control selector original)
      (Fin.natAdd (NativeFrameControl.encoding width).width index)).val =
      ((QubitLayout.canonical 1).basisEquiv.symm selector index).val := by
  have split := contextUnion_split_right_value
    (InPlaceControlled.context width) (selectorContext width) (selector_disjoint width)
    (label width control selector original)
    (positionsOfEqualWires (selectorLayout width) (selectorContext width).quantumLayout
      (selector_wires width) index)
  simp only [label, Equiv.apply_symm_apply] at split
  have retained := basisOfEqualWires_value (selectorLayout width)
    (selectorContext width).quantumLayout (selector_wires width)
    ((selectorQubitLayout width).binaryIndexEquiv.symm selector) index
  change (label width control selector original
    (nativePosition width (Fin.natAdd (NativeFrameControl.encoding width).width index))).val = _
  rw [nativePosition_right]
  exact split.trans retained

/-- All runtime labels read exactly the original frame followed by C and N. -/
lemma pointNativeBasis_label (width : Nat) (control selector : Fin 2)
    (original : (NumeratorMeasurement.context width).register.Index) :
    nativeBasis width (label width control selector original) =
      (nativeLayout width).basisEquiv.symm
        (prodEquiv (prodEquiv (NumeratorMeasurement.frameBasis width original, control),
          selector)) := by
  let originalLabel : Fin (2 ^ (NativeFrameControl.encoding width).width) :=
    prodEquiv (NumeratorMeasurement.frameBasis width original, control)
  change (fun index : Fin ((NativeFrameControl.encoding width).width + 1) =>
    nativeBasis width (label width control selector original) index) =
      (BinaryBasis.bigEndianEquiv ((NativeFrameControl.encoding width).width + 1)).symm
        (prodEquiv (originalLabel, selector))
  rw [BinaryBasis.bigEndianEquiv_symm_prod
    (leftWidth := (NativeFrameControl.encoding width).width) (rightWidth := 1)]
  funext index
  refine Fin.addCases (m := (NativeFrameControl.encoding width).width) (n := 1)
    (fun first => ?_) (fun last => ?_) index
  · simp only [Fin.addCases_left]
    apply Fin.ext
    exact nativeBasis_label_left width control selector original first
  · simp only [Fin.addCases_right]
    apply Fin.ext
    exact nativeBasis_label_right width control selector original last

/-- Complete physical placement and the original binary grouping agree for every runtime state. -/
lemma pointNativeBasis_eq_basis (width : Nat) (state : (context width).register.Index) :
    nativeBasis width state = (nativeLayout width).basisEquiv.symm (basis width state) := by
  obtain ⟨⟨frameControl, selector⟩, same⟩ :=
    (prodEquiv (m := (NativeFrameControl.encoding width).width) (n := 1)).surjective
      (basis width state)
  obtain ⟨⟨frame, control⟩, rfl⟩ :=
    (prodEquiv (m := (ProductPlacement.frameEncoding width).width) (n := 1)).surjective
      frameControl
  obtain ⟨original, rfl⟩ := (NumeratorMeasurement.frameBasis width).surjective frame
  have equal : label width control selector original = state :=
    (basis width).injective ((basis_label width control selector original).trans same)
  rw [← equal, pointNativeBasis_label, basis_label]
  rfl

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition
