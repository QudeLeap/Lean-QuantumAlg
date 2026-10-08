/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Workspace

/-!
# Exact indexed exponent values on their actual physical systems

The ordered owned entries give one dimension-two system for each prescribed
index. The basis correspondence reads those actual finite values in list
order. In particular, the increasing-index context exposes each original
exponent value at its prescribed physical identity.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement

noncomputable section

open Execution MeasuredUncompute

/-- Each prescribed indexed entry contributes exactly one actual system. -/
theorem indexedContext_systemCount (width : Nat) (indices : List Nat) (distinct : indices.Nodup) :
    (indexedContext width indices distinct).systemCount = indices.length := by
  change ((indices.map (indexedEntry width)).flatMap RuntimeEntry.quantumWires).length = _
  rw [indexed_wires, List.length_map]

/-- List positions correspond to the actual owned quantum-system positions. -/
def indexedPositions (width : Nat) (indices : List Nat) (distinct : indices.Nodup) :
    Fin indices.length ≃ Fin (indexedContext width indices distinct).systemCount :=
  finCongr (indexedContext_systemCount width indices distinct).symm

/-- Every corresponding actual wire has its prescribed physical identity and dimension two. -/
theorem indexedPositions_wire (width : Nat) (indices : List Nat) (distinct : indices.Nodup)
    (index : Fin indices.length) :
    (indexedContext width indices distinct).quantumLayout.wire
      (indexedPositions width indices distinct index) =
        QuantumWire.mk (InPlaceControlled.frameWidth width + indices[index.val]'index.isLt) 2 := by
  have bound : index.val <
      (indexedContext width indices distinct).quantumWires.length := by
    change index.val < (indexedContext width indices distinct).systemCount
    rw [indexedContext_systemCount]
    exact index.isLt
  change ((indices.map (indexedEntry width)).flatMap
    RuntimeEntry.quantumWires)[index.val]'bound = _
  simp only [indexed_wires, List.getElem_map]

private theorem indexed_dimension (width : Nat) (indices : List Nat) (distinct : indices.Nodup)
    (index : Fin indices.length) :
    ((indexedContext width indices distinct).quantumLayout.wire
      (indexedPositions width indices distinct index)).dimension = 2 :=
  congrArg QuantumWire.dimension (indexedPositions_wire width indices distinct index)

/-- The original indexed values are read from the actual dependent finite-system basis. -/
def indexedBasis (width : Nat) (indices : List Nat) (distinct : indices.Nodup) :
    (indexedContext width indices distinct).register.Index ≃ (Fin indices.length → Fin 2) :=
  ((indexedPositions width indices distinct).piCongr fun index =>
    finCongr (congrArg PNat.val (indexed_dimension width indices distinct index)).symm).symm

/-- Reading an indexed value returns exactly the finite value on that owned physical system. -/
theorem indexedBasis_value (width : Nat) (indices : List Nat) (distinct : indices.Nodup)
    (value : (indexedContext width indices distinct).register.Index) (index : Fin indices.length) :
    (indexedBasis width indices distinct value index).val =
      (value (indexedPositions width indices distinct index)).val := by
  have actual := Equiv.piCongr_apply_apply
    (W := fun _ : Fin indices.length => Fin 2)
    (Z := fun position : Fin (indexedContext width indices distinct).systemCount =>
      Fin ((indexedContext width indices distinct).quantumLayout.wire position).dimension)
    (indexedPositions width indices distinct)
    (fun position => finCongr
      (congrArg PNat.val (indexed_dimension width indices distinct position)).symm)
    (indexedBasis width indices distinct value) index
  have values := congrArg Fin.val actual
  have roundtrip := (indexedBasis width indices distinct).symm_apply_apply value
  change ((indexedBasis width indices distinct).symm
    (indexedBasis width indices distinct value)
      (indexedPositions width indices distinct index)).val =
        (indexedBasis width indices distinct value index).val at values
  rw [roundtrip] at values
  exact values.symm

/-- Increasing-index storage reads the original exponent values in their exact indexed order. -/
def rangeBasis (width count : Nat) :
    (indexedContext width (List.range count) List.nodup_range).register.Index ≃
      (Fin count → Fin 2) :=
  (indexedBasis width (List.range count) List.nodup_range).trans
    ((finCongr List.length_range).arrowCongr (Equiv.refl (Fin 2)))

/-- The original finite exponent index names its real owned-system position. -/
def rangePosition (width count : Nat) (index : Fin count) :
    Fin (indexedContext width (List.range count) List.nodup_range).systemCount :=
  indexedPositions width (List.range count) List.nodup_range
    ((finCongr List.length_range).symm index)

/-- Exponent index i is exactly the dimension-two system at physical identity frameWidth+i. -/
theorem rangePosition_wire (width count : Nat) (index : Fin count) :
    (indexedContext width (List.range count) List.nodup_range).quantumLayout.wire
      (rangePosition width count index) =
        QuantumWire.mk (InPlaceControlled.frameWidth width + index.val) 2 := by
  have actual := indexedPositions_wire width (List.range count)
    List.nodup_range ((finCongr List.length_range).symm index)
  rw [List.getElem_range] at actual
  exact actual

/-- The indexed exponent read is exactly the value on that original physical system. -/
theorem rangeBasis_value (width count : Nat)
    (value : (indexedContext width (List.range count) List.nodup_range).register.Index)
    (index : Fin count) :
    (rangeBasis width count value index).val = (value (rangePosition width count index)).val :=
  indexedBasis_value width (List.range count) List.nodup_range value
    ((finCongr List.length_range).symm index)

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
