/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Placement.Geometry

/-!
# Actual exponent and selector entries beside the shared arithmetic workspace

Every indexed exponent or selector system owns one distinct dimension-two
physical wire and one distinct storage identity. The finite context builder
retains exactly the prescribed index list. The complete arithmetic/history
workspace and its result cells are disjoint from this indexed region, so the
actual union contains every original and indexed system together.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement

noncomputable section

open MeasuredUncompute Execution

/-- The indexed control region uses consecutive keys after every original arithmetic entry. -/
def indexedKey (width index : Nat) : StorageKey :=
  ⟨(InPlaceControlled.controlKey width).id + index⟩

private theorem indexedKey_injective (width : Nat) : Function.Injective (indexedKey width) := by
  intro first second same
  exact Nat.add_left_cancel (congrArg StorageKey.id same)

/-- Every indexed system is one real qubit at its position beyond the original arithmetic frame. -/
def indexedLayout (width index : Nat) : QuantumLayout 1 :=
  QuantumLayout.uniform 1 2 (fun _ => InPlaceControlled.frameWidth width + index)
    (fun _ _ _ => Subsingleton.elim _ _)

private theorem indexedLayout_wires (width index : Nat) :
    (indexedLayout width index).wires = [⟨InPlaceControlled.frameWidth width + index, 2⟩] := by
  simp only [indexedLayout, QuantumLayout.uniform, QuantumLayout.wires, List.ofFn_const]
  rfl

/-- The indexed system remains an actual owned entry in the complete runtime context. -/
def indexedEntry (width index : Nat) : RuntimeEntry .quantum :=
  .ownedLayout (indexedKey width index) (indexedLayout width index)

private theorem indexed_wires (width : Nat) (indices : List Nat) :
    (indices.map (indexedEntry width)).flatMap RuntimeEntry.quantumWires =
      indices.map (fun index => QuantumWire.mk (InPlaceControlled.frameWidth width + index) 2) := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      simp only [List.map_cons, List.flatMap_cons, indexedEntry, RuntimeEntry.quantumWires,
        indexedLayout_wires, List.singleton_append, ih]

/-- Build the prescribed distinct indexed systems with their global ownership certificates. -/
@[reducible] def indexedContext (width : Nat) (indices : List Nat) (distinct : indices.Nodup) :
    RuntimeCtx .quantum where
  entries := indices.map (indexedEntry width)
  keysNodup := by
    simpa only [List.map_map, indexedEntry, RuntimeEntry.key, Function.comp_def] using
      (List.nodup_map_iff (indexedKey_injective width)).mpr distinct
  identitiesNodup := by
    rw [indexed_wires, List.map_map]
    exact (List.nodup_map_iff
      (f := fun index : Nat => InPlaceControlled.frameWidth width + index)
      (fun _ _ same => Nat.add_left_cancel same)).mpr distinct

/-- Every prescribed indexed storage identity is present in its original order. -/
theorem indexedContext_keys (width : Nat) (indices : List Nat) (distinct : indices.Nodup) :
    (indexedContext width indices distinct).keys = indices.map (indexedKey width) := by
  simp only [RuntimeCtx.keys, List.map_map, indexedEntry, RuntimeEntry.key,
    Function.comp_def]

/-- Every prescribed physical system is present once, in its original indexed order. -/
theorem indexedContext_physical (width : Nat) (indices : List Nat) (distinct : indices.Nodup) :
    (indexedContext width indices distinct).physicalIdx =
      indices.map (fun index => InPlaceControlled.frameWidth width + index) := by
  change ((indices.map (indexedEntry width)).flatMap RuntimeEntry.quantumWires).map
    QuantumWire.identity = _
  rw [indexed_wires, List.map_map]
  rfl

/-- None of the indexed systems or keys overlaps any original arithmetic or result-cell entry. -/
theorem indexedContext_disjoint (width : Nat) (indices : List Nat) (distinct : indices.Nodup) :
    RuntimeCtx.StorageDisjoint (NumeratorMeasurement.context width)
      (indexedContext width indices distinct) := by
  constructor
  · apply (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mpr
    apply List.disjoint_left.mpr
    intro key old indexed
    rw [indexedContext_keys] at indexed
    obtain ⟨index, _present, equal⟩ := List.mem_map.mp indexed
    have bound := original_key_bound width key old
    have identity := congrArg StorageKey.id equal
    change (InPlaceControlled.controlKey width).id + index = key.id at identity
    omega
  · apply (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mpr
    apply List.disjoint_left.mpr
    intro wire old indexed
    rw [indexedContext_physical] at indexed
    obtain ⟨index, _present, equal⟩ := List.mem_map.mp indexed
    have bound := InPlaceControlled.original_bounded width wire old
    omega

/-- All exponent systems and the final internal selector are physically resident together. -/
@[reducible] def readyContext (width count : Nat) : RuntimeCtx .quantum :=
  (NumeratorMeasurement.context width).disjointUnion
    (indexedContext width (List.range (count + 1)) List.nodup_range)
    (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
