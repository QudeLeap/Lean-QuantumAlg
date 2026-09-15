/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Target.Basis
import all QuantumAlg.Core.Execution.Context.Union.Preparation.Basis
import all QuantumAlg.Core.Execution.Measurement.Cells.Framing.Coordinates

/-!
# Actual prepared scalar-workspace basis with all original exponent systems

The original basis contains only two coordinate words and all supplied
exponent systems. The actual arithmetic preparation, original cell retains
and zero-selector preparation assemble every final basis coordinate while
retaining all incoming exponent and coordinate values.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Allocation

noncomputable section

open Execution ContextUnion MeasuredUncompute MAU.Inversion.SharedEEA

/-- A supplied basis consists exactly of two original words and the full exponent register. -/
def inputLabel (width count : Nat) (exponent : (exponents width count).register.Index)
    (x y : Fin (2 ^ width)) : (before width count).register.Index :=
  (unionBasisEquiv (InversePreparation.before width) (exponents width count)
    (input_disjoint width count)).symm ((InversePreparation.inputBasisEquiv width).symm (x, y),
      exponent)

/-- Every original input basis admits precisely the supplied word and exponent coordinates. -/
theorem inputLabel_surjective (width count : Nat)
    (original : (before width count).register.Index) :
    ∃ (exponent : (exponents width count).register.Index) (x y : Fin (2 ^ width)),
      original = inputLabel width count exponent x y := by
  obtain ⟨⟨old, exponent⟩, rfl⟩ :=
    (unionBasisEquiv (InversePreparation.before width) (exponents width count)
      (input_disjoint width count)).symm.surjective original
  obtain ⟨⟨x, y⟩, rfl⟩ := (InversePreparation.inputBasisEquiv width).symm.surjective old
  exact ⟨exponent, x, y, rfl⟩

/-- The charged arithmetic preparation keeps every supplied exponent in its full live context. -/
def auxiliaryAssembly (modulus count : Nat) :
    ((InputPreparation.auxiliaryLayout modulus.size).register.Index ×
      (before modulus.size count).register.Index) ≃
      ((InversePreparation.after modulus.size).disjointUnion (exponents modulus.size count)
        (auxiliary_disjoint modulus.size count)).register.Index :=
  preparedFramedBasisEquiv InversePreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size)
    (InversePreparation.auxiliary_fresh modulus.size)
    (InversePreparation.auxiliary_disjoint modulus.size) (auxiliary_disjoint modulus.size count)

/-- Original finite-cell retention keeps every old joint quantum coordinate unchanged. -/
def cellsAssembly (width count : Nat) :
    ((InversePreparation.after width).disjointUnion (exponents width count)
      (auxiliary_disjoint width count)).register.Index ≃ (withCells width count).register.Index :=
  MeasurementCells.framedBasisEquiv (InversePreparation.after width)
    (exponents width count) 2 width (complete_disjoint width count)

/-- The actual selector preparation inserts the same one owned system beyond all exponents. -/
def selectorAssembly (width count : Nat) :
    ((indexedLayout width count).register.Index × (withCells width count).register.Index) ≃
      (after width count).register.Index :=
  preparedLocalBasisEquiv (withCells width count) (indexedKey width count)
    (indexedLayout width count) (selector_fresh width count) (selector_disjoint width count)

/-- Every final coordinate assembles through the actual preparation and retain sequence. -/
def initializedAssembly (modulus count : Nat) :
    ((indexedLayout modulus.size count).register.Index ×
      ((InputPreparation.auxiliaryLayout modulus.size).register.Index ×
        (before modulus.size count).register.Index)) ≃ (after modulus.size count).register.Index :=
  (Equiv.prodCongr (Equiv.refl _) ((auxiliaryAssembly modulus count).trans
    (cellsAssembly modulus.size count))).trans (selectorAssembly modulus.size count)

/-- The actual fixed preparation retains both original words and the complete exponent register. -/
theorem auxiliaryAssembly_input (modulus count : Nat)
    (exponent : (exponents modulus.size count).register.Index) (x y : Fin (2 ^ modulus.size)) :
    auxiliaryAssembly modulus count ((InPlacePreparation.preparation modulus).value,
      inputLabel modulus.size count exponent x y) =
      (unionBasisEquiv (InversePreparation.after modulus.size) (exponents modulus.size count)
        (auxiliary_disjoint modulus.size count)).symm
        (InversePreparation.assembly modulus.size ((InPlacePreparation.preparation modulus).value,
          (InversePreparation.inputBasisEquiv modulus.size).symm (x, y)), exponent) :=
  preparedFramedBasis_join InversePreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size)
    (InversePreparation.auxiliary_fresh modulus.size)
    (InversePreparation.auxiliary_disjoint modulus.size)
    (auxiliary_disjoint modulus.size count) _ _ _

/-- Actual result retains preserve all original arithmetic and exponent basis values together. -/
theorem cellsAssembly_input (width count : Nat)
    (exponent : (exponents width count).register.Index)
    (original : (InversePreparation.after width).register.Index) :
    cellsAssembly width count
      ((unionBasisEquiv (InversePreparation.after width) (exponents width count)
        (auxiliary_disjoint width count)).symm (original, exponent)) =
      (unionBasisEquiv (NumeratorMeasurement.context width) (exponents width count)
        (complete_disjoint width count)).symm
        (MeasurementCells.basisEquiv (InversePreparation.after width) 2 width original, exponent) :=
  MeasurementCells.framedBasisEquiv_join (InversePreparation.after width)
    (exponents width count) 2 width (complete_disjoint width count) original exponent

/-- Both words and all exponent values survive in the prepared A=0 arithmetic frame. -/
theorem auxiliary_cells_input (modulus count : Nat)
    (exponent : (exponents modulus.size count).register.Index) (x y : Fin (2 ^ modulus.size)) :
    cellsAssembly modulus.size count
      (auxiliaryAssembly modulus count ((InPlacePreparation.preparation modulus).value,
        inputLabel modulus.size count exponent x y)) =
      (unionBasisEquiv (NumeratorMeasurement.context modulus.size) (exponents modulus.size count)
        (complete_disjoint modulus.size count)).symm
        (InPlaceTarget.preparedBasis modulus x y, exponent) := by
  rw [auxiliaryAssembly_input]
  exact cellsAssembly_input modulus.size count exponent
    (InversePreparation.assembly modulus.size ((InPlacePreparation.preparation modulus).value,
      (InversePreparation.inputBasisEquiv modulus.size).symm (x, y)))

end

end MeasuredPlacement.Allocation
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
