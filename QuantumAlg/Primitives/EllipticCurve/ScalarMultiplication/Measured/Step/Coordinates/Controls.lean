/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step.Coordinates.Shared

/-!
# The selected exponent and common selector on their actual physical systems

Each indexed point call reads its control from the prescribed original
exponent and reads the one shared selector beyond every exponent. The
finite values follow actual wire identities through all placement and
context coordinates; no input preparation premise is used for these laws.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement

noncomputable section

open Execution MeasuredUncompute

private lemma oneBit_value (layout : QubitLayout 1)
    (value : layout.toQuantumLayout.register.Index) : layout.binaryIndexEquiv value = value 0 := by
  apply finTwoEquiv.injective
  have actual := layout.binaryIndexEquiv_bit value (0 : Fin 1)
  change (layout.binaryIndexEquiv value).val.testBit 0 = finTwoEquiv (value 0) at actual
  have bit (index : Fin 2) : index.val.testBit 0 = finTwoEquiv index := by
    fin_cases index <;> rfl
  rw [bit] at actual
  exact actual

private lemma oneContext_value (layout : QubitLayout 1) (ctx : RuntimeCtx .quantum)
    (same : layout.toQuantumLayout.wires = ctx.quantumLayout.wires)
    (value : ctx.register.Index) :
    (layout.binaryIndexEquiv ((basisOfEqualWires _ _ same).symm value)).val =
      (value (positionsOfEqualWires _ _ same 0)).val := by
  let coordinates := basisOfEqualWires layout.toQuantumLayout ctx.quantumLayout same
  have binary := oneBit_value layout (coordinates.symm value)
  have actual := basisOfEqualWires_value layout.toQuantumLayout ctx.quantumLayout same
    (coordinates.symm value) 0
  change (coordinates (coordinates.symm value) (positionsOfEqualWires _ _ same 0)).val =
    (coordinates.symm value 0).val at actual
  rw [Equiv.apply_symm_apply] at actual
  exact (congrArg Fin.val binary).trans actual.symm

private def controlPosition (width : Nat) : Fin (MeasuredPointAddition.context width).systemCount :=
  ContextUnion.leftPosition (InPlaceControlled.context width)
    (MeasuredPointAddition.selectorContext width) (MeasuredPointAddition.selector_disjoint width)
    (ContextUnion.rightPosition (NumeratorMeasurement.context width)
      (InPlaceControlled.controlContext width) (InPlaceControlled.control_disjoint width)
      (positionsOfEqualWires (InPlaceControlled.controlLayout width)
        (InPlaceControlled.controlContext width).quantumLayout
        (InPlaceControlled.control_wires width) 0))

private def selectorPosition (width : Nat) :
    Fin (MeasuredPointAddition.context width).systemCount :=
  ContextUnion.rightPosition (InPlaceControlled.context width)
    (MeasuredPointAddition.selectorContext width) (MeasuredPointAddition.selector_disjoint width)
    (positionsOfEqualWires (MeasuredPointAddition.selectorLayout width)
      (MeasuredPointAddition.selectorContext width).quantumLayout
      (MeasuredPointAddition.selector_wires width) 0)

/-- Read an exponent or the shared selector from its actual common-context segment. -/
def indexedValue (width count : Nat) (value : (readyContext width count).register.Index)
    (index : Fin (count + 1)) : Fin 2 :=
  rangeBasis width (count + 1)
    (ContextUnion.unionBasisEquiv (NumeratorMeasurement.context width)
      (indexedContext width (List.range (count + 1)) List.nodup_range)
      (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range) value).2 index

private def indexedPosition (width count : Nat) (index : Fin (count + 1)) :
    Fin (readyContext width count).systemCount :=
  ContextUnion.rightPosition (NumeratorMeasurement.context width)
    (indexedContext width (List.range (count + 1)) List.nodup_range)
    (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)
    (rangePosition width (count + 1) index)

private lemma indexedValue_value (width count : Nat)
    (value : (readyContext width count).register.Index) (index : Fin (count + 1)) :
    (indexedValue width count value index).val = (value (indexedPosition width count index)).val :=
  (rangeBasis_value width (count + 1) _ index).trans
    (ContextUnion.contextUnion_split_right_value (NumeratorMeasurement.context width)
      (indexedContext width (List.range (count + 1)) List.nodup_range)
      (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range) value
      (rangePosition width (count + 1) index)).symm

/-- The original point control is read from its complete point-context coordinate. -/
def pointControl (width : Nat) (value : (MeasuredPointAddition.context width).register.Index) :
    Fin 2 :=
  InPlaceControlled.controlBasis width
    (ContextUnion.unionBasisEquiv (NumeratorMeasurement.context width)
      (InPlaceControlled.controlContext width) (InPlaceControlled.control_disjoint width)
      (ContextUnion.unionBasisEquiv (InPlaceControlled.context width)
        (MeasuredPointAddition.selectorContext width)
        (MeasuredPointAddition.selector_disjoint width)
        value).1).2

/-- The original point selector is read from its actual outer selector segment. -/
def pointSelector (width : Nat) (value : (MeasuredPointAddition.context width).register.Index) :
    Fin 2 :=
  MeasuredPointAddition.selectorBasis width
    (ContextUnion.unionBasisEquiv (InPlaceControlled.context width)
      (MeasuredPointAddition.selectorContext width) (MeasuredPointAddition.selector_disjoint width)
      value).2

private lemma pointControl_value (width : Nat)
    (value : (MeasuredPointAddition.context width).register.Index) :
    (pointControl width value).val = (value (controlPosition width)).val := by
  let outer := ContextUnion.unionBasisEquiv (InPlaceControlled.context width)
    (MeasuredPointAddition.selectorContext width) (MeasuredPointAddition.selector_disjoint width)
    value
  let inner := ContextUnion.unionBasisEquiv (NumeratorMeasurement.context width)
    (InPlaceControlled.controlContext width) (InPlaceControlled.control_disjoint width) outer.1
  let position := positionsOfEqualWires (InPlaceControlled.controlLayout width)
    (InPlaceControlled.controlContext width).quantumLayout
    (InPlaceControlled.control_wires width) 0
  have first := oneContext_value (InPlaceControlled.controlQubitLayout width)
    (InPlaceControlled.controlContext width) (InPlaceControlled.control_wires width) inner.2
  have second := ContextUnion.contextUnion_split_right_value (NumeratorMeasurement.context width)
    (InPlaceControlled.controlContext width) (InPlaceControlled.control_disjoint width)
    outer.1 position
  have third := ContextUnion.contextUnion_split_left_value (InPlaceControlled.context width)
    (MeasuredPointAddition.selectorContext width) (MeasuredPointAddition.selector_disjoint width)
    value (ContextUnion.rightPosition (NumeratorMeasurement.context width)
      (InPlaceControlled.controlContext width) (InPlaceControlled.control_disjoint width) position)
  exact first.trans (second.symm.trans third.symm)

private lemma pointSelector_value (width : Nat)
    (value : (MeasuredPointAddition.context width).register.Index) :
    (pointSelector width value).val = (value (selectorPosition width)).val := by
  let outer := ContextUnion.unionBasisEquiv (InPlaceControlled.context width)
    (MeasuredPointAddition.selectorContext width) (MeasuredPointAddition.selector_disjoint width)
    value
  have first := oneContext_value (MeasuredPointAddition.selectorQubitLayout width)
    (MeasuredPointAddition.selectorContext width) (MeasuredPointAddition.selector_wires width)
    outer.2
  have second := ContextUnion.contextUnion_split_right_value (InPlaceControlled.context width)
    (MeasuredPointAddition.selectorContext width) (MeasuredPointAddition.selector_disjoint width)
    value (positionsOfEqualWires (MeasuredPointAddition.selectorLayout width)
      (MeasuredPointAddition.selectorContext width).quantumLayout
      (MeasuredPointAddition.selector_wires width) 0)
  exact first.trans second.symm

private lemma control_position (width : Nat) {count : Nat} (active : Fin count) :
    pointPosition width active (controlPosition width) =
      indexedPosition width count active.castSucc := by
  apply (readyContext width count).quantumLayout.position_eq_of_identity_eq
  apply congrArg QuantumWire.identity
  rw [pointPosition_wire, controlPosition, ContextUnion.contextUnion_left_wire,
    ContextUnion.contextUnion_right_wire, wireAtCorrespondingPosition, indexedPosition,
    ContextUnion.contextUnion_right_wire, rangePosition_wire]
  change QuantumWire.mk (physicalMap width active (InPlaceControlled.controlWire width)) 2 =
    QuantumWire.mk (InPlaceControlled.frameWidth width + active.val) 2
  exact congrArg (fun identity => QuantumWire.mk identity 2) (physicalMap_control width active)

private lemma selector_position (width : Nat) {count : Nat} (active : Fin count) :
    pointPosition width active (selectorPosition width) =
      indexedPosition width count (Fin.last count) := by
  apply (readyContext width count).quantumLayout.position_eq_of_identity_eq
  apply congrArg QuantumWire.identity
  rw [pointPosition_wire, selectorPosition, ContextUnion.contextUnion_right_wire,
    wireAtCorrespondingPosition, indexedPosition, ContextUnion.contextUnion_right_wire,
    rangePosition_wire]
  change QuantumWire.mk (physicalMap width active (MeasuredPointAddition.selectorWire width)) 2 =
    QuantumWire.mk (InPlaceControlled.frameWidth width + count) 2
  exact congrArg (fun identity => QuantumWire.mk identity 2) (physicalMap_selector width active)

/-- The actual point control reads exactly the selected original exponent value. -/
lemma pointBasis_control (width : Nat) {count : Nat} (active : Fin count)
    (value : (readyContext width count).register.Index) :
    pointControl width (pointBasis width active value).1 =
      indexedValue width count value active.castSucc := by
  apply Fin.ext
  have selected := pointBasis_value width active value (controlPosition width)
  rw [control_position] at selected
  exact (pointControl_value width (pointBasis width active value).1).trans
    (selected.trans (indexedValue_value width count value active.castSucc).symm)

/-- Every actual point step reads the same single final selector value. -/
lemma pointBasis_selector (width : Nat) {count : Nat} (active : Fin count)
    (value : (readyContext width count).register.Index) :
    pointSelector width (pointBasis width active value).1 =
      indexedValue width count value (Fin.last count) := by
  apply Fin.ext
  have selected := pointBasis_value width active value (selectorPosition width)
  rw [selector_position] at selected
  exact (pointSelector_value width (pointBasis width active value).1).trans
    (selected.trans (indexedValue_value width count value (Fin.last count)).symm)

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
