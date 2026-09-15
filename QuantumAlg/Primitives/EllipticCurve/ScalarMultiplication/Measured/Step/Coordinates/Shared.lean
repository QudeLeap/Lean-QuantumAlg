/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step.Coordinates

/-!
# The same arithmetic values in every actual indexed point step

The original arithmetic systems retain all physical identities through
indexed placement. Reading the arithmetic part of any selected point basis
therefore returns exactly the common ready context's original arithmetic
basis, including every original auxiliary and history system.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement

noncomputable section

open Execution MeasuredUncompute

/-- The common complete arithmetic basis is read from its actual resident union segment. -/
def sharedBasis (width count : Nat) (value : (readyContext width count).register.Index) :
    (NumeratorMeasurement.context width).register.Index :=
  (ContextUnion.unionBasisEquiv (NumeratorMeasurement.context width)
    (indexedContext width (List.range (count + 1)) List.nodup_range)
    (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range) value).1

private def originalPosition (width : Nat)
    (index : Fin (NumeratorMeasurement.context width).systemCount) :
    Fin (MeasuredPointAddition.context width).systemCount :=
  ContextUnion.leftPosition (InPlaceControlled.context width)
    (MeasuredPointAddition.selectorContext width) (MeasuredPointAddition.selector_disjoint width)
    (ContextUnion.leftPosition (NumeratorMeasurement.context width)
      (InPlaceControlled.controlContext width) (InPlaceControlled.control_disjoint width) index)

private def readyPosition (width count : Nat)
    (index : Fin (NumeratorMeasurement.context width).systemCount) :
    Fin (readyContext width count).systemCount :=
  ContextUnion.leftPosition (NumeratorMeasurement.context width)
    (indexedContext width (List.range (count + 1)) List.nodup_range)
    (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range) index

/-- The original arithmetic segment of the point context keeps all its original basis values. -/
def pointSharedBasis (width : Nat) (value : (MeasuredPointAddition.context width).register.Index) :
    (NumeratorMeasurement.context width).register.Index :=
  (ContextUnion.unionBasisEquiv (NumeratorMeasurement.context width)
    (InPlaceControlled.controlContext width) (InPlaceControlled.control_disjoint width)
    (ContextUnion.unionBasisEquiv (InPlaceControlled.context width)
      (MeasuredPointAddition.selectorContext width) (MeasuredPointAddition.selector_disjoint width)
      value).1).1

private theorem original_wire_fixed (width : Nat) {count : Nat} (active : Fin count)
    (index : Fin (NumeratorMeasurement.context width).systemCount) :
    QuantumWire.relabel (physicalMap width active)
      ((NumeratorMeasurement.context width).quantumLayout.wire index) =
        (NumeratorMeasurement.context width).quantumLayout.wire index := by
  have present : ((NumeratorMeasurement.context width).quantumLayout.wire index).identity ∈
      (NumeratorMeasurement.context width).physicalIdx := by
    rw [← RuntimeCtx.quantumLayout_identities]
    exact List.mem_ofFn.mpr ⟨index, rfl⟩
  have fixed := physicalMap_original width active _ present
  cases wire : (NumeratorMeasurement.context width).quantumLayout.wire index with
  | mk identity dimension =>
      rw [wire] at fixed
      change QuantumWire.mk (physicalMap width active identity) dimension =
        QuantumWire.mk identity dimension
      exact congrArg (fun value => QuantumWire.mk value dimension) fixed

/-- Every point step uses precisely the common original arithmetic system at each position. -/
theorem pointPosition_shared (width : Nat) {count : Nat} (active : Fin count)
    (index : Fin (NumeratorMeasurement.context width).systemCount) :
    pointPosition width active (originalPosition width index) =
      readyPosition width count index := by
  apply (readyContext width count).quantumLayout.position_eq_of_identity_eq
  apply congrArg QuantumWire.identity
  rw [pointPosition_wire, originalPosition, ContextUnion.contextUnion_left_wire,
    ContextUnion.contextUnion_left_wire, original_wire_fixed, readyPosition,
    ContextUnion.contextUnion_left_wire]

/-- The selected point view reads the unchanged complete common arithmetic basis exactly. -/
theorem pointBasis_shared (width : Nat) {count : Nat} (active : Fin count)
    (value : (readyContext width count).register.Index) :
    pointSharedBasis width (pointBasis width active value).1 = sharedBasis width count value := by
  funext index
  apply Fin.ext
  have selected := pointBasis_value width active value (originalPosition width index)
  rw [pointPosition_shared] at selected
  have first := ContextUnion.contextUnion_split_left_value (InPlaceControlled.context width)
    (MeasuredPointAddition.selectorContext width) (MeasuredPointAddition.selector_disjoint width)
    (pointBasis width active value).1
    (ContextUnion.leftPosition (NumeratorMeasurement.context width)
      (InPlaceControlled.controlContext width) (InPlaceControlled.control_disjoint width) index)
  have second := ContextUnion.contextUnion_split_left_value (NumeratorMeasurement.context width)
    (InPlaceControlled.controlContext width) (InPlaceControlled.control_disjoint width)
    (ContextUnion.unionBasisEquiv (InPlaceControlled.context width)
      (MeasuredPointAddition.selectorContext width) (MeasuredPointAddition.selector_disjoint width)
      (pointBasis width active value).1).1 index
  have common := ContextUnion.contextUnion_split_left_value (NumeratorMeasurement.context width)
    (indexedContext width (List.range (count + 1)) List.nodup_range)
    (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range) value index
  exact second.symm.trans (first.symm.trans (selected.trans common))

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
