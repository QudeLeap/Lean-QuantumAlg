/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Cascade
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Preparation
import all QuantumAlg.Core.Execution.Context.Union.Preparation
import all QuantumAlg.Core.Execution.Measurement.Cells.Framing

/-!
# Actual preparation before the measured scalar cascade

The supplied systems are the original two coordinate words and all exponent
bits. One charged fixed preparation adds the arithmetic complement; actual
retains add the original finite measurement cells; one charged preparation
adds the zero selector. The cascade then executes on precisely those entries.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Allocation

noncomputable section

open Execution ContextUnion MeasuredUncompute MAU.Inversion.SharedEEA

/-- All supplied exponent systems are physically resident from the start. -/
@[reducible] def exponents (width count : Nat) : RuntimeCtx .quantum :=
  indexedContext width (List.range count) List.nodup_range

private theorem complete_disjoint (width count : Nat) :
    RuntimeCtx.StorageDisjoint (NumeratorMeasurement.context width) (exponents width count) :=
  indexedContext_disjoint width (List.range count) List.nodup_range

private theorem auxiliary_disjoint (width count : Nat) :
    RuntimeCtx.StorageDisjoint (InversePreparation.after width) (exponents width count) :=
  MeasurementCells.original_disjoint (InversePreparation.after width)
    (exponents width count) 2 width (complete_disjoint width count)

private theorem input_disjoint (width count : Nat) :
    RuntimeCtx.StorageDisjoint (InversePreparation.before width) (exponents width count) :=
  preparation_original_disjoint InversePreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout width) (InversePreparation.auxiliary_fresh width)
    (InversePreparation.auxiliary_disjoint width) (auxiliary_disjoint width count)

/-- Only the two supplied coordinate words and arbitrary exponent systems are initially live. -/
@[reducible] def before (width count : Nat) : RuntimeCtx .quantum :=
  (InversePreparation.before width).disjointUnion (exponents width count)
    (input_disjoint width count)

/-- The actual fixed arithmetic preparation leaves every supplied exponent system resident. -/
def prepareAuxiliary (modulus count : Nat) :
    Circuit (before modulus.size count)
      ((InversePreparation.after modulus.size).disjointUnion (exponents modulus.size count)
        (auxiliary_disjoint modulus.size count)) :=
  prepareFramed InversePreparation.auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
    (InversePreparation.auxiliary_fresh modulus.size)
    (InversePreparation.auxiliary_disjoint modulus.size)
    (auxiliary_disjoint modulus.size count) (InPlacePreparation.preparation modulus)

/-- All original arithmetic systems and retained result cells precede the supplied exponents. -/
@[reducible] def withCells (width count : Nat) : RuntimeCtx .quantum :=
  (NumeratorMeasurement.context width).disjointUnion (exponents width count)
    (complete_disjoint width count)

/-- Allocate the original finite result cells without changing any key to avoid the exponents. -/
def allocateCells (width count : Nat) :
    Circuit ((InversePreparation.after width).disjointUnion (exponents width count)
      (auxiliary_disjoint width count)) (withCells width count) :=
  MeasurementCells.allocateFramed (InversePreparation.after width)
    (exponents width count) 2 width (complete_disjoint width count)

private theorem selector_entries (width count : Nat) :
    (indexedEntry width count :: (withCells width count).entries).Perm
      (readyContext width count).entries := by
  change (indexedEntry width count :: ((NumeratorMeasurement.context width).entries ++
    (List.range count).map (indexedEntry width))).Perm
      ((NumeratorMeasurement.context width).entries ++
        (List.range (count + 1)).map (indexedEntry width))
  rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, ← List.append_assoc]
  exact (List.perm_append_singleton _ _).symm

private theorem selector_fresh (width count : Nat) :
    indexedKey width count ∉ (withCells width count).keys := by
  have distinct := ((selector_entries width count).map RuntimeEntry.key).nodup_iff.mpr
    (readyContext width count).keysNodup
  exact (List.nodup_cons.mp distinct).1

private theorem selector_disjoint (width count : Nat) :
    List.Disjoint (indexedLayout width count).identities (withCells width count).physicalIdx := by
  have distinct := (((selector_entries width count).flatMap_right RuntimeEntry.quantumWires).map
    QuantumWire.identity).nodup_iff.mpr (readyContext width count).identitiesNodup
  change (((indexedLayout width count).wires ++ (withCells width count).quantumWires).map
    QuantumWire.identity).Nodup at distinct
  rw [List.map_append, ← layout_identities_eq_map_wires] at distinct
  exact (List.nodup_append'.mp distinct).2.2

/-- The actual selector preparation determines the complete final live context. -/
@[reducible] def after (width count : Nat) : RuntimeCtx .quantum :=
  (withCells width count).addOwnedLayout (indexedKey width count) (indexedLayout width count)
    (selector_fresh width count) (selector_disjoint width count)

/-- Prepare exactly one zero selector beyond all supplied exponent systems. -/
def prepareSelector (width count : Nat) : Circuit (withCells width count) (after width count) :=
  .prepare (withCells width count) (indexedKey width count) (indexedLayout width count)
    (selector_fresh width count) (selector_disjoint width count)
    (BasisPreparation.zero (indexedLayout width count))

/-- Both charged quantum preparations and all actual result retains occur before the cascade. -/
def initializeWork (modulus count : Nat) :
    Circuit (before modulus.size count) (after modulus.size count) :=
  .seq (prepareAuxiliary modulus count)
    (.seq (allocateCells modulus.size count) (prepareSelector modulus.size count))

/-- The allocated output retains every common entry, original role and physical identity. -/
theorem body_entries (width count : Nat) :
    (readyContext width count).entries.Perm (after width count).entries :=
  (selector_entries width count).symm

/-- Execute the same actual measured cascade on the entries produced by initialization. -/
def placedCascade {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count)) :
    Circuit (after p.size count) (after p.size count) :=
  ContextPermutation.localCircuit (cascade E points order) (cascade_isLocal E points order)
    (after p.size count) (body_entries p.size count)

/-- One actual circuit initializes its work and executes the prescribed indexed point cascade. -/
def circuit {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count)) :
    Circuit (before p.size count) (after p.size count) :=
  .seq (initializeWork p count) (placedCascade E points order)

/-- The complete output structurally reads all original measurement cells in the final context. -/
def output (width count : Nat) :
    Output (after width count) (.fixedVector width (.finite 2)) :=
  Output.all (after width count) (.read (ContextPermutation.input (body_entries width count)
    (ContextUnion.inputLeft
      (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)
      (MeasurementCells.input (InversePreparation.after width) 2 width))))

/-- Every live original or allocated entry occurs in the same complete output listing. -/
theorem output_listing (width count : Nat) :
    (output width count).listing = (after width count).keys := Output.all_listing _ _

end

end MeasuredPlacement.Allocation
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
