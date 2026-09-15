/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Workspace
import Mathlib.Data.List.Perm.Basic

/-!
# The same actual workspace entries in every indexed point call

The mapped point body contains the unchanged arithmetic/history and finite
result-cell context, the selected exponent entry and the common selector
entry. All remaining exponent entries form its actual resident frame. The
entry descriptions keep keys, roles, shapes and physical dimensions together.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement

noncomputable section

open MeasuredUncompute Execution

private theorem layout_eq {count : Nat} (first second : QuantumLayout count)
    (same : first.wire = second.wire) : first = second := by
  cases first
  cases second
  cases same
  rfl

private theorem mapped_control_layout (width : Nat) {count : Nat} (active : Fin count) :
    (InPlaceControlled.controlLayout width).relabel (physicalMap width active) =
      indexedLayout width active.val := by
  apply layout_eq
  funext index
  change QuantumWire.mk (physicalMap width active (InPlaceControlled.controlWire width)) 2 =
    QuantumWire.mk (InPlaceControlled.frameWidth width + active.val) 2
  exact congrArg (fun identity => QuantumWire.mk identity 2) (physicalMap_control width active)

private theorem mapped_selector_layout (width : Nat) {count : Nat} (active : Fin count) :
    (MeasuredPointAddition.selectorLayout width).relabel (physicalMap width active) =
      indexedLayout width count := by
  apply layout_eq
  funext index
  change QuantumWire.mk (physicalMap width active (MeasuredPointAddition.selectorWire width)) 2 =
    QuantumWire.mk (InPlaceControlled.frameWidth width + count) 2
  exact congrArg (fun identity => QuantumWire.mk identity 2) (physicalMap_selector width active)

private theorem mapped_control_key (width : Nat) {count : Nat} (active : Fin count) :
    storageMap width active (InPlaceControlled.controlKey width) = indexedKey width active.val :=
  congrArg StorageKey.mk (storageMap_control width active)

private theorem mapped_selector_key (width : Nat) {count : Nat} (active : Fin count) :
    storageMap width active (MeasuredPointAddition.selectorKey width) = indexedKey width count :=
  congrArg StorageKey.mk (storageMap_selector width active)

/-- Every indexed body retains the common arithmetic entries and its two prescribed controls. -/
theorem placed_entries (width : Nat) {count : Nat} (active : Fin count) :
    (MeasuredPointAddition.Placement.context width (storageMap width active)
      (physicalMap width active)).entries =
        (NumeratorMeasurement.context width).entries ++
          [indexedEntry width active.val, indexedEntry width count] := by
  have originalEntries := congrArg RuntimeCtx.entries (originalContext_fixed width active)
  change (NumeratorMeasurement.context width).entries.map
    (RuntimeEntry.relabel (storageMap width active) (physicalMap width active)) =
      (NumeratorMeasurement.context width).entries at originalEntries
  change (((NumeratorMeasurement.context width).entries ++
    [RuntimeEntry.ownedLayout (InPlaceControlled.controlKey width)
      (InPlaceControlled.controlLayout width)]) ++
    [RuntimeEntry.ownedLayout (MeasuredPointAddition.selectorKey width)
      (MeasuredPointAddition.selectorLayout width)]).map
        (RuntimeEntry.relabel (storageMap width active) (physicalMap width active)) = _
  rw [List.map_append, List.map_append, originalEntries]
  simp only [List.map_cons, List.map_nil, RuntimeEntry.relabel,
    mapped_control_key, mapped_selector_key, mapped_control_layout, mapped_selector_layout,
    List.append_assoc, List.singleton_append, indexedEntry]

/-- All exponent entries except the current control remain in the actual resident frame. -/
@[reducible] def ambientContext (width : Nat) {count : Nat} (active : Fin count) :
    RuntimeCtx .quantum :=
  indexedContext width ((List.range count).erase active.val) (List.nodup_range.erase _)

/-- Every ambient index is an original exponent index distinct from the selected control. -/
theorem ambient_index {count : Nat} (active : Fin count) (index : Nat)
    (present : index ∈ (List.range count).erase active.val) :
    index < count ∧ index ≠ active.val := by
  constructor
  · exact List.mem_range.mp (List.mem_of_mem_erase present)
  · intro same
    subst index
    exact List.nodup_range.not_mem_erase present

private theorem combined_entries_perm (width : Nat) {count : Nat} (active : Fin count) :
    ((MeasuredPointAddition.Placement.context width (storageMap width active)
      (physicalMap width active)).entries ++ (ambientContext width active).entries).Perm
        (readyContext width count).entries := by
  have indices : ([active.val, count] ++ (List.range count).erase active.val).Perm
      (List.range (count + 1)) := by
    rw [List.range_succ]
    exact ((List.perm_append_singleton count ((List.range count).erase active.val)).symm.cons
      active.val).trans ((List.perm_cons_erase (List.mem_range.mpr active.isLt)).symm.append_right
        [count])
  rw [placed_entries]
  change (((NumeratorMeasurement.context width).entries ++
    [indexedEntry width active.val, indexedEntry width count]) ++
      ((List.range count).erase active.val).map (indexedEntry width)).Perm
        ((NumeratorMeasurement.context width).entries ++
          (List.range (count + 1)).map (indexedEntry width))
  rw [List.append_assoc]
  exact List.Perm.append_left _ (by
    simpa only [List.map_append, List.map_cons, List.map_nil] using
      indices.map (indexedEntry width))

/-- Every remaining exponent is disjoint from the entire placed point body and its selector. -/
theorem ambient_disjoint (width : Nat) {count : Nat} (active : Fin count) :
    RuntimeCtx.StorageDisjoint
      (MeasuredPointAddition.Placement.context width (storageMap width active)
        (physicalMap width active)) (ambientContext width active) := by
  have entries := combined_entries_perm width active
  constructor
  · apply (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mpr
    have distinct := (entries.map RuntimeEntry.key).nodup_iff.mpr
      (readyContext width count).keysNodup
    rw [List.map_append] at distinct
    exact (List.nodup_append'.mp distinct).2.2
  · apply (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mpr
    have distinct := ((entries.flatMap_right RuntimeEntry.quantumWires).map
      QuantumWire.identity).nodup_iff.mpr (readyContext width count).identitiesNodup
    rw [List.flatMap_append, List.map_append] at distinct
    exact (List.nodup_append'.mp distinct).2.2

/-- The actual placed body and resident frame contain precisely the common complete entries. -/
theorem framed_entries (width : Nat) {count : Nat} (active : Fin count) :
    ((MeasuredPointAddition.Placement.context width (storageMap width active)
      (physicalMap width active)).disjointUnion (ambientContext width active)
        (ambient_disjoint width active)).entries.Perm (readyContext width count).entries :=
  combined_entries_perm width active

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
