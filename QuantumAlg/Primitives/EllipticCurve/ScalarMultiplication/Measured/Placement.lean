/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Placement
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Controlled.Layout
import all QuantumAlg.Core.Base.Accounting.Context.Relabeling.Fixed

/-!
# Indexed control placement with one shared measured point workspace

The original point control is placed at one selected exponent system. The
internal selector is placed after the entire exponent interval. Every earlier
arithmetic address and finite measurement-cell key stays fixed. The maps are
global bijections used by the actual native placement compiler; they introduce
no runtime exchanges or extra quantum state transformations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement

noncomputable section

open MeasuredUncompute

/-- Move the selector beyond all exponent slots, then place the supplied control at its slot. -/
def indexMap (base : Nat) {count : Nat} (active : Fin count) : Nat ≃ Nat :=
  (Equiv.swap (base + 1) (base + count)).trans (Equiv.swap base (base + active.val))

/-- The supplied control reaches exactly the selected exponent address. -/
theorem indexMap_control (base : Nat) {count : Nat} (active : Fin count) :
    indexMap base active base = base + active.val := by
  have positive : 0 < count := Nat.zero_lt_of_lt active.isLt
  rw [indexMap, Equiv.trans_apply,
    Equiv.swap_apply_of_ne_of_ne (by omega : base ≠ base + 1) (by omega : base ≠ base + count),
    Equiv.swap_apply_left]

/-- The internal selector reaches the first address after the entire exponent interval. -/
theorem indexMap_selector (base : Nat) {count : Nat} (active : Fin count) :
    indexMap base active (base + 1) = base + count := by
  have positive : 0 < count := Nat.zero_lt_of_lt active.isLt
  rw [indexMap, Equiv.trans_apply, Equiv.swap_apply_left]
  exact Equiv.swap_apply_of_ne_of_ne (by omega) (by have bounded := active.isLt; omega)

/-- Every original arithmetic address or measurement-cell key below the interval stays fixed. -/
theorem indexMap_prefix (base : Nat) {count : Nat} (active : Fin count)
    (index : Nat) (before : index < base) : indexMap base active index = index := by
  rw [indexMap, Equiv.trans_apply,
    Equiv.swap_apply_of_ne_of_ne (by omega : index ≠ base + 1) (by omega : index ≠ base + count)]
  exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)

/-- Actual native point-control and selector systems use the complete injective physical map. -/
def physicalMap (width : Nat) {count : Nat} (active : Fin count) : Nat ↪ Nat :=
  (indexMap (InPlaceControlled.frameWidth width) active).toEmbedding

/-- The original supplied control becomes the selected actual exponent system. -/
theorem physicalMap_control (width : Nat) {count : Nat} (active : Fin count) :
    physicalMap width active (InPlaceControlled.controlWire width) =
      InPlaceControlled.frameWidth width + active.val :=
  indexMap_control _ active

/-- Every call places the selector at the same address beyond the complete exponent interval. -/
theorem physicalMap_selector (width : Nat) {count : Nat} (active : Fin count) :
    physicalMap width active (MeasuredPointAddition.selectorWire width) =
      InPlaceControlled.frameWidth width + count :=
  indexMap_selector _ active

/-- Original arithmetic and history systems stay on the same physical wires in every call. -/
theorem physicalMap_original (width : Nat) {count : Nat} (active : Fin count)
    (wire : Nat) (present : wire ∈ (NumeratorMeasurement.context width).physicalIdx) :
    physicalMap width active wire = wire :=
  indexMap_prefix _ active wire (InPlaceControlled.original_bounded width wire present)

private theorem original_key_bound (width : Nat) (key : StorageKey)
    (present : key ∈ (NumeratorMeasurement.context width).keys) :
    key.id < (InPlaceControlled.controlKey width).id := by
  have member : key.id ∈ (NumeratorMeasurement.context width).keys.map StorageKey.id :=
    List.mem_map_of_mem present
  have bounded := List.le_max_of_le' 0 member le_rfl
  change key.id ≤
    ((NumeratorMeasurement.context width).keys.map StorageKey.id).foldr Nat.max 0 at bounded
  change key.id <
    ((NumeratorMeasurement.context width).keys.map StorageKey.id).foldr Nat.max 0 + 1
  omega

private theorem fold_max_bounded (indices : List Nat) (bound : Nat)
    (bounded : ∀ index ∈ indices, index ≤ bound) : indices.foldr Nat.max bound = bound := by
  induction indices with
  | nil => rfl
  | cons first rest ih =>
      rw [List.foldr_cons, ih (fun index present => bounded index (.tail _ present))]
      exact Nat.max_eq_right (bounded first (.head _))

/-- The original selector's fresh key immediately follows the supplied control's fresh key. -/
theorem selectorKey_succ (width : Nat) :
    (MeasuredPointAddition.selectorKey width).id = (InPlaceControlled.controlKey width).id + 1 := by
  change ((InPlaceControlled.context width).keys.map StorageKey.id).foldr Nat.max 0 + 1 = _
  rw [InPlaceControlled.context, RuntimeCtx.keys_disjointUnion]
  change ((((NumeratorMeasurement.context width).keys ++
    [InPlaceControlled.controlKey width]).map StorageKey.id).foldr Nat.max 0) + 1 = _
  rw [List.map_append, List.foldr_append]
  change ((NumeratorMeasurement.context width).keys.map StorageKey.id).foldr Nat.max
    (Nat.max (InPlaceControlled.controlKey width).id 0) + 1 = _
  have seed : Nat.max (InPlaceControlled.controlKey width).id 0 =
      (InPlaceControlled.controlKey width).id := Nat.max_zero _
  rw [seed, fold_max_bounded]
  intro index present
  obtain ⟨key, inKeys, equal⟩ := List.mem_map.mp present
  rw [← equal]
  exact (original_key_bound width key inKeys).le

/-- Map actual storage identities with the same interval geometry as the physical control slots. -/
def storageMap (width : Nat) {count : Nat} (active : Fin count) : StorageKey ↪ StorageKey where
  toFun key := ⟨indexMap (InPlaceControlled.controlKey width).id active key.id⟩
  inj' := by
    intro first second same
    have ids := (indexMap (InPlaceControlled.controlKey width).id active).injective
      (congrArg StorageKey.id same)
    cases first
    cases second
    exact congrArg StorageKey.mk ids

/-- The original control's storage identity becomes exactly its selected exponent key. -/
theorem storageMap_control (width : Nat) {count : Nat} (active : Fin count) :
    (storageMap width active (InPlaceControlled.controlKey width)).id =
      (InPlaceControlled.controlKey width).id + active.val :=
  indexMap_control _ active

/-- Every call uses the same unique selector key after all exponent keys. -/
theorem storageMap_selector (width : Nat) {count : Nat} (active : Fin count) :
    (storageMap width active (MeasuredPointAddition.selectorKey width)).id =
      (InPlaceControlled.controlKey width).id + count := by
  change indexMap _ active (MeasuredPointAddition.selectorKey width).id = _
  rw [selectorKey_succ]
  exact indexMap_selector _ active

/-- Every original measurement result and arithmetic entry keeps its exact storage key. -/
theorem storageMap_original (width : Nat) {count : Nat} (active : Fin count)
    (key : StorageKey) (present : key ∈ (NumeratorMeasurement.context width).keys) :
    storageMap width active key = key := by
  have fixed := indexMap_prefix (InPlaceControlled.controlKey width).id active key.id
    (original_key_bound width key present)
  cases key
  exact congrArg StorageKey.mk fixed

/-- Every indexed call reuses the identical complete arithmetic/history and result-cell context. -/
theorem originalContext_fixed (width : Nat) {count : Nat} (active : Fin count) :
    (NumeratorMeasurement.context width).relabel (storageMap width active)
      (physicalMap width active) = NumeratorMeasurement.context width :=
  RuntimeCtx.relabel_eq_self _ _ _ (storageMap_original width active)
    (physicalMap_original width active)

/-- The actual selected body rewrites native addresses and finite operands with these exact maps. -/
def body {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count) :
    Circuit
      (MeasuredPointAddition.Placement.context p.size (storageMap p.size active)
        (physicalMap p.size active))
      (MeasuredPointAddition.Placement.context p.size (storageMap p.size active)
        (physicalMap p.size active)) :=
  MeasuredPointAddition.Placement.body E Q (storageMap p.size active) (physicalMap p.size active)

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
