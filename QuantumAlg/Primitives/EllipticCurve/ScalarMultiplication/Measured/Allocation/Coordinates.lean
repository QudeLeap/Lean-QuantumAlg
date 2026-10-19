/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Assembly
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step.Admissible
import all QuantumAlg.Core.Execution.Preparation.Coordinates

/-!
# Actual initialized scalar coordinates on the shared resident workspace

The two charged preparations establish the fixed arithmetic basis and zero
selector. All supplied exponent values stay on their original physical wires.
These facts follow from the actual preparation and entry-permutation maps,
without a caller-supplied assumption about allocated work or result cells.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Allocation

noncomputable section

open Execution ContextUnion MeasuredUncompute MAU.Inversion.SharedEEA

private def selectorReadyBasis (width count : Nat)
    (selector : (indexedLayout width count).register.Index)
    (original : (withCells width count).register.Index) :
    (readyContext width count).register.Index :=
  (ContextPermutation.basis (body_entries width count)).symm
    (selectorAssembly width count (selector, original))

private lemma selectorReadyBasis_value (width count : Nat)
    (selector : (indexedLayout width count).register.Index)
    (original : (withCells width count).register.Index)
    (index : Fin (readyContext width count).systemCount) :
    (selectorReadyBasis width count selector original index).val =
      (selectorAssembly width count (selector, original)
        (ContextPermutation.positions (body_entries width count) index)).val := by
  have actual := ContextPermutation.basis_value (body_entries width count)
    (selectorReadyBasis width count selector original) index
  simpa only [selectorReadyBasis, Equiv.apply_symm_apply] using actual.symm

private lemma selectorReadyBasis_shared (width count : Nat)
    (selector : (indexedLayout width count).register.Index)
    (original : (withCells width count).register.Index) :
    sharedBasis width count (selectorReadyBasis width count selector original) =
      (unionBasisEquiv (NumeratorMeasurement.context width) (exponents width count)
        (complete_disjoint width count) original).1 := by
  funext index
  apply Fin.ext
  let oldPosition := leftPosition (NumeratorMeasurement.context width) (exponents width count)
    (complete_disjoint width count) index
  have positionsMatch :
      ContextPermutation.positions (body_entries width count) (readyPosition width count index) =
        PreparationBorrowed.fullPositionEquiv (withCells width count) (indexedKey width count)
          (indexedLayout width count) (selector_fresh width count) (selector_disjoint width count)
          (.inr oldPosition) := by
    apply (after width count).quantumLayout.position_eq_of_identity_eq
    apply congrArg QuantumWire.identity
    dsimp only [oldPosition]
    rw [ContextPermutation.positions_wire, readyPosition, contextUnion_left_wire,
      PreparationBorrowed.fullPositionEquiv_old_wire, contextUnion_left_wire]
  have read := selectorReadyBasis_value width count selector original
    (readyPosition width count index)
  rw [positionsMatch] at read
  have prepared := preparedLocalBasisEquiv_old_value (withCells width count)
    (indexedKey width count) (indexedLayout width count) (selector_fresh width count)
    (selector_disjoint width count) selector original oldPosition
  have ready := contextUnion_split_left_value (NumeratorMeasurement.context width)
    (indexedContext width (List.range (count + 1)) List.nodup_range)
    (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)
    (selectorReadyBasis width count selector original) index
  have old := contextUnion_split_left_value (NumeratorMeasurement.context width)
    (exponents width count) (complete_disjoint width count) original index
  exact ready.symm.trans (read.trans (prepared.trans old))

private lemma selectorReadyBasis_exponent (width count : Nat)
    (selector : (indexedLayout width count).register.Index)
    (original : (withCells width count).register.Index) (index : Fin count) :
    indexedValue width count (selectorReadyBasis width count selector original) index.castSucc =
      rangeBasis width count
        (unionBasisEquiv (NumeratorMeasurement.context width) (exponents width count)
          (complete_disjoint width count) original).2 index := by
  apply Fin.ext
  let oldPosition := rightPosition (NumeratorMeasurement.context width) (exponents width count)
    (complete_disjoint width count) (rangePosition width count index)
  have positionsMatch : ContextPermutation.positions (body_entries width count)
      (indexedPosition width count index.castSucc) =
        PreparationBorrowed.fullPositionEquiv (withCells width count) (indexedKey width count)
          (indexedLayout width count) (selector_fresh width count) (selector_disjoint width count)
          (.inr oldPosition) := by
    apply (after width count).quantumLayout.position_eq_of_identity_eq
    apply congrArg QuantumWire.identity
    dsimp only [oldPosition]
    rw [ContextPermutation.positions_wire, indexedPosition, contextUnion_right_wire,
      rangePosition_wire, PreparationBorrowed.fullPositionEquiv_old_wire,
      contextUnion_right_wire, rangePosition_wire]
    rfl
  have read := selectorReadyBasis_value width count selector original
    (indexedPosition width count index.castSucc)
  rw [positionsMatch] at read
  have prepared := preparedLocalBasisEquiv_old_value (withCells width count)
    (indexedKey width count) (indexedLayout width count) (selector_fresh width count)
    (selector_disjoint width count) selector original oldPosition
  have old := contextUnion_split_right_value (NumeratorMeasurement.context width)
    (exponents width count) (complete_disjoint width count) original
    (rangePosition width count index)
  exact (indexedValue_value width count _ index.castSucc).trans
    (read.trans (prepared.trans (old.trans (rangeBasis_value width count _ index).symm)))

private lemma selectorReadyBasis_selector (width count : Nat)
    (selector : (indexedLayout width count).register.Index)
    (original : (withCells width count).register.Index) :
    (indexedValue width count (selectorReadyBasis width count selector original)
      (Fin.last count)).val = (selector 0).val := by
  have positionsMatch : ContextPermutation.positions (body_entries width count)
      (indexedPosition width count (Fin.last count)) =
        PreparationBorrowed.fullPositionEquiv (withCells width count) (indexedKey width count)
          (indexedLayout width count) (selector_fresh width count) (selector_disjoint width count)
          (.inl 0) := by
    apply (after width count).quantumLayout.position_eq_of_identity_eq
    apply congrArg QuantumWire.identity
    rw [ContextPermutation.positions_wire, indexedPosition, contextUnion_right_wire,
      rangePosition_wire, PreparationBorrowed.fullPositionEquiv_new_wire]
    rfl
  have read := selectorReadyBasis_value width count selector original
    (indexedPosition width count (Fin.last count))
  rw [positionsMatch] at read
  exact (indexedValue_value width count _ (Fin.last count)).trans
    (read.trans (preparedLocalBasisEquiv_new_value (withCells width count)
      (indexedKey width count) (indexedLayout width count) (selector_fresh width count)
      (selector_disjoint width count) selector original 0))

/-- The actual fixed preparation basis, expressed on the complete shared cascade context. -/
def initializedReadyBasis (modulus count : Nat)
    (original : (before modulus.size count).register.Index) :
    (readyContext modulus.size count).register.Index :=
  (ContextPermutation.basis (body_entries modulus.size count)).symm
    (initializedAssembly modulus count
      ((BasisPreparation.zero (indexedLayout modulus.size count)).value,
        (InPlacePreparation.preparation modulus).value, original))

/-- Actual initialization prepares the original complete arithmetic frame from supplied words. -/
lemma initializedReadyBasis_shared (modulus count : Nat)
    (exponent : (exponents modulus.size count).register.Index) (x y : Fin (2 ^ modulus.size)) :
    sharedBasis modulus.size count
      (initializedReadyBasis modulus count (inputLabel modulus.size count exponent x y)) =
        InPlaceTarget.preparedBasis modulus x y := by
  change sharedBasis modulus.size count (selectorReadyBasis modulus.size count _ _) = _
  rw [selectorReadyBasis_shared, Equiv.trans_apply, auxiliary_cells_input, Equiv.apply_symm_apply]

/-- Every supplied exponent survives both preparations and all finite-cell retains exactly. -/
lemma initializedReadyBasis_exponent (modulus count : Nat)
    (exponent : (exponents modulus.size count).register.Index) (x y : Fin (2 ^ modulus.size))
    (index : Fin count) :
    indexedValue modulus.size count
      (initializedReadyBasis modulus count (inputLabel modulus.size count exponent x y))
      index.castSucc = rangeBasis modulus.size count exponent index := by
  change indexedValue modulus.size count (selectorReadyBasis modulus.size count _ _)
    index.castSucc = _
  rw [selectorReadyBasis_exponent, Equiv.trans_apply, auxiliary_cells_input, Equiv.apply_symm_apply]

/-- The charged fresh preparation establishes the zero selector for every original input. -/
lemma initializedReadyBasis_selector (modulus count : Nat)
    (original : (before modulus.size count).register.Index) :
    indexedValue modulus.size count (initializedReadyBasis modulus count original)
      (Fin.last count) = 0 := by
  apply Fin.ext
  change (indexedValue modulus.size count (selectorReadyBasis modulus.size count _ _)
    (Fin.last count)).val = 0
  rw [selectorReadyBasis_selector]
  rfl

end

end MeasuredPlacement.Allocation
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
