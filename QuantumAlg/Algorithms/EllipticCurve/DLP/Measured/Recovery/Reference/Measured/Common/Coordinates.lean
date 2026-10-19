/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Measured.Stored.Step
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Point.Fibers
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Workspace.Basis
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step.Coordinates.Label
import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step.Coordinates.Ambient
import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step.Coordinates.Controls
import Mathlib.Data.Fin.Tuple.Basic

/-!
# One original exponent interval and one fixed dirty arithmetic bank

Coordinates are the production ready union, rangeBasis and actual point/ambient physical
positions. All exponents remain quantum coordinates. The fixed bank contains the
complete original NumeratorMeasurement register, selector and arbitrary Reference. No
classical Store, including any result-cell Store, is collapsed or removed.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Reference
namespace Measured.CommonBank

noncomputable section

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

abbrev Exponents (count : Nat) := Fin count → Fin 2

abbrev Bank (width : Nat) (Reference : Register) :=
  Recovery.Point.Instrument.FiberBank width Reference

private def shuffle {Arithmetic Exponent Reference : Type} :
    Arithmetic × ((Fin 2 × Exponent) × Reference) ≃
      Exponent × (Arithmetic × (Fin 2 × Reference)) where
  toFun value := (value.2.1.2, (value.1, (value.2.1.1, value.2.2)))
  invFun value := (value.2.1, ((value.2.2.1, value.1), value.2.2.2))
  left_inv value := by rcases value with ⟨a, ⟨⟨s, u⟩, r⟩⟩; rfl
  right_inv value := by rcases value with ⟨u, ⟨a, ⟨s, r⟩⟩⟩; rfl

/-- Separate all original exponents from one active-independent arithmetic/selector bank. -/
def coordinates (width count : Nat) (Reference : Register) :
    ((readyContext width count).register.prod Reference).Index ≃
      Exponents count × Bank width Reference :=
  (ContextUnion.referenceBasis (NumeratorMeasurement.context width)
    (indexedContext width (List.range (count + 1)) List.nodup_range)
    (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range) Reference).trans
    (((Equiv.refl (NumeratorMeasurement.context width).register.Index).prodCongr
      (((rangeBasis width (count + 1)).trans
        (Fin.snocEquiv (fun _ : Fin (count + 1) => Fin 2)).symm).prodCongr
          (Equiv.refl Reference.Index))).trans shuffle)

lemma coordinates_exponent (width count : Nat) (Reference : Register)
    (value : ((readyContext width count).register.prod Reference).Index)
    (index : Fin count) :
    (coordinates width count Reference value).1 index =
      indexedValue width count value.1 index.castSucc := rfl

lemma coordinates_arithmetic (width count : Nat) (Reference : Register)
    (value : ((readyContext width count).register.prod Reference).Index) :
    (coordinates width count Reference value).2.1 = sharedBasis width count value.1 := rfl

lemma coordinates_selector (width count : Nat) (Reference : Register)
    (value : ((readyContext width count).register.prod Reference).Index) :
    (coordinates width count Reference value).2.2.1 =
      indexedValue width count value.1 (Fin.last count) := rfl

lemma coordinates_reference (width count : Nat) (Reference : Register)
    (value : ((readyContext width count).register.prod Reference).Index) :
    (coordinates width count Reference value).2.2.2 = value.2 := rfl

/-- The exponent coordinate reads one actual original resident physical system. -/
def exponentPosition (width count : Nat) (index : Fin count) :
    Fin (readyContext width count).systemCount :=
  ContextUnion.rightPosition (NumeratorMeasurement.context width)
    (indexedContext width (List.range (count + 1)) List.nodup_range)
    (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)
    (rangePosition width (count + 1) index.castSucc)

lemma exponentPosition_wire (width count : Nat) (index : Fin count) :
    (readyContext width count).quantumLayout.wire (exponentPosition width count index) =
      QuantumWire.mk (InPlaceControlled.frameWidth width + index.val) 2 := by
  rw [exponentPosition, ContextUnion.contextUnion_right_wire, rangePosition_wire]
  rfl

lemma coordinates_exponent_value (width count : Nat) (Reference : Register)
    (value : ((readyContext width count).register.prod Reference).Index) (index : Fin count) :
    ((coordinates width count Reference value).1 index).val =
      (value.1 (exponentPosition width count index)).val :=
  indexedValue_value width count value.1 index.castSucc

/-- The actual selected point view has this control, selector and full original arithmetic. -/
lemma stepCoordinates_point (width : Nat) {count : Nat} (active : Fin count)
    (Reference : Register)
    (value : ((readyContext width count).register.prod Reference).Index) :
    (stepCoordinates width active Reference value).1 =
      MeasuredPointAddition.label width ((coordinates width count Reference value).1 active)
        (coordinates width count Reference value).2.2.1
        (coordinates width count Reference value).2.1 :=
  pointBasis_label width active value.1

lemma stepCoordinates_reference (width : Nat) {count : Nat} (active : Fin count)
    (Reference : Register)
    (value : ((readyContext width count).register.prod Reference).Index) :
    (stepCoordinates width active Reference value).2.2 =
      (coordinates width count Reference value).2.2.2 := rfl

private abbrev Remaining {count : Nat} (active : Fin count) :=
  (List.range count).erase active.val

/-- A list position in the actual ambient context names its original exponent index. -/
def remainingIndex {count : Nat} (active : Fin count)
    (position : Fin (Remaining active).length) : Fin count :=
  ⟨(Remaining active)[position.val]'position.isLt,
    (ambient_index active _ (List.getElem_mem position.isLt)).1⟩

lemma remainingIndex_ne {count : Nat} (active : Fin count)
    (position : Fin (Remaining active).length) : remainingIndex active position ≠ active := by
  intro same
  exact (ambient_index active _ (List.getElem_mem position.isLt)).2
    (congrArg Fin.val same)

lemma remainingIndex_surjective {count : Nat} (active index : Fin count)
    (different : index ≠ active) :
    ∃ position : Fin (Remaining active).length, remainingIndex active position = index := by
  have differentValues : index.val ≠ active.val := fun same => different (Fin.ext same)
  have present : index.val ∈ Remaining active :=
    (List.mem_erase_of_ne differentValues).2 (List.mem_range.mpr index.isLt)
  obtain ⟨position, bounded, same⟩ := List.mem_iff_getElem.mp present
  exact ⟨⟨position, bounded⟩, Fin.ext same⟩

/-- Each actual ambient wire is exactly the corresponding original exponent wire. -/
lemma ambientPosition_remaining (width : Nat) {count : Nat} (active : Fin count)
    (position : Fin (Remaining active).length) :
    ambientPosition width active
        (indexedPositions width (Remaining active) (List.nodup_range.erase _) position) =
      exponentPosition width count (remainingIndex active position) := by
  apply (readyContext width count).quantumLayout.position_eq_of_identity_eq
  apply congrArg QuantumWire.identity
  rw [ambientPosition_wire, indexedPositions_wire, exponentPosition_wire]
  rfl

/-- No spectator exponent is encoded in a classical tag; every ambient read is physical. -/
lemma ambient_coordinate (width : Nat) {count : Nat} (active : Fin count)
    (Reference : Register)
    (value : ((readyContext width count).register.prod Reference).Index)
    (position : Fin (Remaining active).length) :
    indexedBasis width (Remaining active) (List.nodup_range.erase _)
        (pointBasis width active value.1).2 position =
      (coordinates width count Reference value).1 (remainingIndex active position) := by
  apply Fin.ext
  calc
    _ = ((pointBasis width active value.1).2
        (indexedPositions width (Remaining active) (List.nodup_range.erase _) position)).val :=
      indexedBasis_value width (Remaining active) (List.nodup_range.erase _) _ position
    _ = (value.1 (ambientPosition width active
        (indexedPositions width (Remaining active) (List.nodup_range.erase _) position))).val :=
      pointBasis_ambient_value width active value.1 _
    _ = (value.1 (exponentPosition width count (remainingIndex active position))).val := by
      rw [ambientPosition_remaining]
    _ = _ := (coordinates_exponent_value width count Reference value
      (remainingIndex active position)).symm

/-- Equality of the complete quantum ambient basis means equality of all other exponents. -/
lemma ambient_equal_iff (width : Nat) {count : Nat} (active : Fin count)
    (Reference : Register)
    (row column : ((readyContext width count).register.prod Reference).Index) :
    (pointBasis width active row.1).2 = (pointBasis width active column.1).2 ↔
      ∀ index : Fin count, index ≠ active →
        (coordinates width count Reference row).1 index =
          (coordinates width count Reference column).1 index := by
  constructor
  · intro equal index different
    obtain ⟨position, rfl⟩ := remainingIndex_surjective active index different
    rw [← ambient_coordinate width active Reference row position,
      ← ambient_coordinate width active Reference column position, equal]
  · intro equal
    apply (indexedBasis width (Remaining active) (List.nodup_range.erase _)).injective
    funext position
    rw [ambient_coordinate, ambient_coordinate]
    exact equal _ (remainingIndex_ne active position)

/-- The selected control and complete ambient delta are precisely the all-exponent delta. -/
lemma exponents_equal_iff (width : Nat) {count : Nat} (active : Fin count)
    (Reference : Register)
    (row column : ((readyContext width count).register.prod Reference).Index) :
    (coordinates width count Reference row).1 = (coordinates width count Reference column).1 ↔
      ((coordinates width count Reference row).1 active =
        (coordinates width count Reference column).1 active ∧
          (pointBasis width active row.1).2 = (pointBasis width active column.1).2) := by
  rw [ambient_equal_iff]
  constructor
  · intro equal
    exact ⟨congrFun equal active, fun index _ => congrFun equal index⟩
  · intro equal
    funext index
    by_cases selected : index = active
    · subst index
      exact equal.1
    · exact equal.2 index selected

end

end Measured.CommonBank
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Reference
