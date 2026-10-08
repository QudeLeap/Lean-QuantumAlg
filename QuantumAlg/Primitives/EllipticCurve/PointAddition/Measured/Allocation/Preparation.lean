/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Layout
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Preparation.Framed
import all QuantumAlg.Core.Execution.Measurement.Cells.Framing.Execution
import all QuantumAlg.Core.Execution.Context.Permutation.References
import all QuantumAlg.Core.Execution.Output

/-!
# Actual work allocation before measured affine point addition

The two supplied coordinate words and coherent control stay resident. The
auxiliary bank is allocated in zero and loaded by the literal fixed X program;
the original retained result cells and a zero selector complete the workspace.
This owner depends only on the layout and preparation contracts.
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
    Circuit (.quantum AlgorithmGate.model .empty) (before modulus.size)
      ((InversePreparation.after modulus.size).disjointUnion
        (InPlaceControlled.controlContext modulus.size)
        (auxiliary_disjoint_control modulus.size)) :=
  InPlacePreparation.Framed.circuit modulus (InPlaceControlled.controlContext modulus.size)
    (auxiliary_disjoint_control modulus.size)

/-- Actual retains use the original measurement keys beside the already resident control. -/
def allocateCells (width : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty)
      ((InversePreparation.after width).disjointUnion
      (InPlaceControlled.controlContext width) (auxiliary_disjoint_control width))
      (InPlaceControlled.context width) :=
  MeasurementCells.allocateFramed (model := .quantum AlgorithmGate.model .empty)
    (InversePreparation.after width)
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
def prepareSelector (width : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (InPlaceControlled.context width) (after width) :=
  .prepareZero (InPlaceControlled.context width) (selectorKey width) (selectorLayout width)
    (InPlaceControlled.context width).canonicalFreshKey_fresh (selector_physical_disjoint width)

/-- All original cells, physical wires, shapes and roles match the accepted body exactly. -/
theorem body_entries (width : Nat) : (context width).entries.Perm (after width).entries := by
  change ((InPlaceControlled.context width).entries ++
    [RuntimeEntry.ownedLayout (selectorKey width) (selectorLayout width)]).Perm
      (RuntimeEntry.ownedLayout (selectorKey width) (selectorLayout width) ::
        (InPlaceControlled.context width).entries)
  exact List.perm_append_singleton _ _

/-- Both quantum preparations and all original result-cell allocations occur in this prefix. -/
def initializeWork (modulus : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty) (before modulus.size) (after modulus.size) :=
  .seq (prepareAuxiliary modulus) (.seq (allocateCells modulus.size) (prepareSelector modulus.size))

/-- The complete output reads the original actual measurement cells in the final live context. -/
def output (width : Nat) : Output (after width) (.fixedVector width (.finite 2)) :=
  Output.all (after width)
    (.read (ContextPermutation.input (body_entries width) (resultInput width)))

theorem output_listing (width : Nat) : (output width).listing = (after width).keys :=
  Output.all_listing _ _


/-- Every real zero preparation and every fixed-bit loading gate occurs in order. -/
def initializationTrace (modulus : Nat) :
    List (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  (ZeroPreparation.eventTrace AlgorithmGate.model .empty
    (InputPreparation.auxiliaryLayout modulus.size) ++
    (InPlacePreparation.loadProgram modulus).eventTrace .empty .empty) ++
    ZeroPreparation.eventTrace AlgorithmGate.model .empty (selectorLayout modulus.size)

/-- The actual initialization charges all auxiliary zeros, literal X loads and the selector zero. -/
theorem initializeWork_eventTrace (modulus : Nat)
    (path : (initializeWork modulus).Path) :
    (initializeWork modulus).eventTrace path = initializationTrace modulus := by
  have loaded : (prepareAuxiliary modulus).eventTrace path.1 =
      ZeroPreparation.eventTrace AlgorithmGate.model .empty
        (InputPreparation.auxiliaryLayout modulus.size) ++
        (InPlacePreparation.loadProgram modulus).eventTrace .empty .empty :=
    InPlacePreparation.Framed.eventTrace modulus (InPlaceControlled.controlContext modulus.size)
      (auxiliary_disjoint_control modulus.size) path.1
  have retained : (allocateCells modulus.size).eventTrace path.2.1 = [] :=
    MeasurementCells.allocateFramed_eventTrace (model := .quantum AlgorithmGate.model .empty)
      (InversePreparation.after modulus.size) (InPlaceControlled.controlContext modulus.size)
      2 modulus.size (InPlaceControlled.control_disjoint modulus.size) path.2.1
  change (prepareAuxiliary modulus).eventTrace path.1 ++
    ((allocateCells modulus.size).eventTrace path.2.1 ++
      ZeroPreparation.eventTrace AlgorithmGate.model .empty (selectorLayout modulus.size)) =
    (ZeroPreparation.eventTrace AlgorithmGate.model .empty
      (InputPreparation.auxiliaryLayout modulus.size) ++
      (InPlacePreparation.loadProgram modulus).eventTrace .empty .empty) ++
      ZeroPreparation.eventTrace AlgorithmGate.model .empty (selectorLayout modulus.size)
  rw [loaded, retained, List.nil_append]

/-- The resource pool is derived from exactly those emitted native events. -/
theorem initializeWork_resourcePool (modulus : Nat)
    (path : (initializeWork modulus).Path) :
    (initializeWork modulus).resourcePool path =
      ResourcePool.ofList (initializationTrace modulus) :=
  congrArg ResourcePool.ofList (initializeWork_eventTrace modulus path)

/-- Zero allocation and X loading preserve every store block and the full resident reference. -/
theorem prepareAuxiliary_execute (modulus : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (before modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    splitServiceState (InversePreparation.after modulus.size)
      (InPlaceControlled.controlContext modulus.size) (auxiliary_disjoint_control modulus.size)
      ((prepareAuxiliary modulus).execute Reference state) =
      ((InPlacePreparation.circuit modulus).execute
        (Register.prod (InPlaceControlled.controlContext modulus.size).register Reference)
        (splitServiceState (InversePreparation.before modulus.size)
          (InPlaceControlled.controlContext modulus.size)
          (input_disjoint_control modulus.size) state)).mapHistory
            (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) :=
  InPlacePreparation.Framed.execute modulus (InPlaceControlled.controlContext modulus.size)
    (auxiliary_disjoint_control modulus.size) state

/-- The original retained cells keep every store, service, history and reference coordinate. -/
theorem allocateCells_execute (width : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ((InversePreparation.after width).disjointUnion
      (InPlaceControlled.controlContext width) (auxiliary_disjoint_control width))
      Reference (ClassicalOracleModel.empty.HiddenState × History)) :
    splitServiceState (NumeratorMeasurement.context width) (InPlaceControlled.controlContext width)
      (InPlaceControlled.control_disjoint width)
      ((allocateCells width).execute Reference state) =
      ((MeasurementCells.allocate (model := .quantum AlgorithmGate.model .empty)
        (InversePreparation.after width) 2 width).execute
        (Register.prod (InPlaceControlled.controlContext width).register Reference)
        (splitServiceState (InversePreparation.after width) (InPlaceControlled.controlContext width)
          (auxiliary_disjoint_control width) state)).mapHistory
            (fun record => (record.1, (record.2.1.1, (record.2.1.2,
              MeasurementCells.allocateFramedPathEquiv
                (model := .quantum AlgorithmGate.model .empty)
                (InversePreparation.after width) (InPlaceControlled.controlContext width) 2 width
                (InPlaceControlled.control_disjoint width) record.2.2)))) :=
  MeasurementCells.allocateFramed_execute (model := .quantum AlgorithmGate.model .empty)
    (InversePreparation.after width) (InPlaceControlled.controlContext width) 2 width
    (InPlaceControlled.control_disjoint width) state

/-- The selector instruction adds its actual zero factor to the complete incoming state. -/
theorem prepareSelector_execute (width : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (InPlaceControlled.context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (prepareSelector width).execute Reference state =
      (state.prepare (selectorKey width) (selectorLayout width)
        (InPlaceControlled.context width).canonicalFreshKey_fresh (selector_physical_disjoint width)
        (BasisPreparation.zero (selectorLayout width))).mapHistory
          (fun record => (record.1.1, (record.1.2, record.2))) := rfl
end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation
