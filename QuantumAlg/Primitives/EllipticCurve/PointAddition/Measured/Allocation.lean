/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Runtime
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Preparation
import all QuantumAlg.Core.Execution.Context.Union.Preparation
import all QuantumAlg.Core.Execution.Measurement.Cells.Framing
import all QuantumAlg.Core.Execution.Context.Permutation.Local.State
import all QuantumAlg.Core.Execution.Context.Permutation.Local.Resources

/-!
# Actual allocation before measured affine point addition

The supplied context contains only the two original coordinate words and the
coherent control. Fixed preparation adds the shared arithmetic auxiliaries;
real retains add the original measurement-result cells; a second charged
preparation supplies the internal zero selector. The accepted body is compiled
onto exactly those live entries without changing their identities or roles.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation

noncomputable section

open Execution ContextUnion MeasuredUncompute MAU.Inversion.SharedEEA

/-- The complete shared-frame allocation remains disjoint from the supplied coherent control. -/
theorem auxiliary_disjoint_control (width : Nat) :
    RuntimeCtx.StorageDisjoint (InversePreparation.after width)
      (InPlaceControlled.controlContext width) :=
  MeasurementCells.original_disjoint (InversePreparation.after width)
    (InPlaceControlled.controlContext width) 2 width (InPlaceControlled.control_disjoint width)

/-- The two original supplied words are disjoint from the same supplied coherent control. -/
theorem input_disjoint_control (width : Nat) :
    RuntimeCtx.StorageDisjoint (InversePreparation.before width)
      (InPlaceControlled.controlContext width) :=
  preparation_original_disjoint InversePreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout width) (InversePreparation.auxiliary_fresh width)
    (InversePreparation.auxiliary_disjoint width) (auxiliary_disjoint_control width)

/-- Only the original coordinate words and the arbitrary supplied control are initially live. -/
def before (width : Nat) : RuntimeCtx .quantum :=
  (InversePreparation.before width).disjointUnion (InPlaceControlled.controlContext width)
    (input_disjoint_control width)

/-- The same charged fixed arithmetic preparation keeps the supplied control physically present. -/
def prepareAuxiliary (modulus : Nat) :
    Circuit (before modulus.size)
      ((InversePreparation.after modulus.size).disjointUnion
        (InPlaceControlled.controlContext modulus.size)
        (auxiliary_disjoint_control modulus.size)) :=
  prepareFramed InversePreparation.auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
    (InversePreparation.auxiliary_fresh modulus.size)
    (InversePreparation.auxiliary_disjoint modulus.size)
    (auxiliary_disjoint_control modulus.size) (InPlacePreparation.preparation modulus)

/-- Actual retains use the original measurement keys beside the already resident control. -/
def allocateCells (width : Nat) :
    Circuit ((InversePreparation.after width).disjointUnion
      (InPlaceControlled.controlContext width) (auxiliary_disjoint_control width))
      (InPlaceControlled.context width) :=
  MeasurementCells.allocateFramed (InversePreparation.after width)
    (InPlaceControlled.controlContext width) 2 width (InPlaceControlled.control_disjoint width)

private theorem selector_physical_disjoint (width : Nat) :
    List.Disjoint (selectorLayout width).identities
      (InPlaceControlled.context width).physicalIdx := by
  have separated := (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mp
    (selector_disjoint width).2
  have identities : (selectorLayout width).identities = (selectorContext width).physicalIdx := by
    change (selectorLayout width).identities =
      ((selectorLayout width).wires ++ []).map QuantumWire.identity
    rw [List.append_nil, ← layout_identities_eq_map_wires]
  rw [identities]
  exact separated.symm

/-- The final context is produced by the actual zero-selector preparation instruction. -/
def after (width : Nat) : RuntimeCtx .quantum :=
  (InPlaceControlled.context width).addOwnedLayout (selectorKey width) (selectorLayout width)
    (InPlaceControlled.context width).canonicalFreshKey_fresh (selector_physical_disjoint width)

/-- The internal selector is supplied by an actual charged zero preparation. -/
def prepareSelector (width : Nat) : Circuit (InPlaceControlled.context width) (after width) :=
  .prepare (InPlaceControlled.context width) (selectorKey width) (selectorLayout width)
    (InPlaceControlled.context width).canonicalFreshKey_fresh (selector_physical_disjoint width)
    (BasisPreparation.zero (selectorLayout width))

/-- All original cells, physical wires, shapes and roles match the accepted body exactly. -/
theorem body_entries (width : Nat) : (context width).entries.Perm (after width).entries := by
  change ((InPlaceControlled.context width).entries ++
    [RuntimeEntry.ownedLayout (selectorKey width) (selectorLayout width)]).Perm
      (RuntimeEntry.ownedLayout (selectorKey width) (selectorLayout width) ::
        (InPlaceControlled.context width).entries)
  exact List.perm_append_singleton _ _

/-- The original measured body executes on the actually allocated entries. -/
def placedBody {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] (Q : AffinePoint E) :
    Circuit (after p.size) (after p.size) :=
  ContextPermutation.localCircuit (body E Q) (body_isLocal E Q) (after p.size) (body_entries p.size)

/-- Both quantum preparations and all original result-cell allocations occur in this prefix. -/
def initializeWork (modulus : Nat) : Circuit (before modulus.size) (after modulus.size) :=
  .seq (prepareAuxiliary modulus) (.seq (allocateCells modulus.size) (prepareSelector modulus.size))

/-- One circuit initializes its own work and then executes measured controlled point addition. -/
def circuit {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] (Q : AffinePoint E) :
    Circuit (before p.size) (after p.size) :=
  .seq (initializeWork p) (placedBody E Q)

/-- The complete output reads the original actual measurement cells in the final live context. -/
def output (width : Nat) : Output (after width) (.fixedVector width (.finite 2)) :=
  Output.all (after width)
    (.read (ContextPermutation.input (body_entries width) (resultInput width)))

theorem output_listing (width : Nat) : (output width).listing = (after width).keys :=
  Output.all_listing _ _

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation
