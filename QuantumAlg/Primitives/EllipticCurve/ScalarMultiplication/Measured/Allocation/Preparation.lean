/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Workspace
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Preparation.Framed
import all QuantumAlg.Core.Execution.Measurement.Cells.Framing.Execution
import all QuantumAlg.Core.Execution.Context.Permutation.References
import all QuantumAlg.Core.Execution.Output

/-!
# Actual work allocation beside all supplied exponent systems

The original coordinate words and every exponent system stay resident. The
auxiliary bank is allocated in zero and loaded by its real fixed X program;
the original retained result cells and a zero selector complete the workspace.
This owner is independent of the measured scalar cascade implementation.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Allocation

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open Execution ContextUnion MeasuredUncompute MAU.Inversion.SharedEEA

/-- All supplied exponent systems are physically resident from the start. -/
@[reducible] def exponents (width count : Nat) : RuntimeCtx .quantum :=
  indexedContext width (List.range count) List.nodup_range

private lemma complete_disjoint (width count : Nat) :
    RuntimeCtx.StorageDisjoint (NumeratorMeasurement.context width) (exponents width count) :=
  indexedContext_disjoint width (List.range count) List.nodup_range

private lemma auxiliary_disjoint (width count : Nat) :
    RuntimeCtx.StorageDisjoint (InversePreparation.after width) (exponents width count) :=
  MeasurementCells.original_disjoint (InversePreparation.after width)
    (exponents width count) 2 width (complete_disjoint width count)

private lemma input_disjoint (width count : Nat) :
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
    Circuit (.quantum AlgorithmGate.model .empty) (before modulus.size count)
      ((InversePreparation.after modulus.size).disjointUnion (exponents modulus.size count)
        (auxiliary_disjoint modulus.size count)) :=
  InPlacePreparation.Framed.circuit modulus (exponents modulus.size count)
    (auxiliary_disjoint modulus.size count)

/-- All original arithmetic systems and retained result cells precede the supplied exponents. -/
@[reducible] def withCells (width count : Nat) : RuntimeCtx .quantum :=
  (NumeratorMeasurement.context width).disjointUnion (exponents width count)
    (complete_disjoint width count)

/-- Allocate the original finite result cells without changing any key to avoid the exponents. -/
def allocateCells (width count : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty)
      ((InversePreparation.after width).disjointUnion (exponents width count)
      (auxiliary_disjoint width count)) (withCells width count) :=
  MeasurementCells.allocateFramed (model := .quantum AlgorithmGate.model .empty)
    (InversePreparation.after width)
    (exponents width count) 2 width (complete_disjoint width count)

private lemma selector_entries (width count : Nat) :
    (indexedEntry width count :: (withCells width count).entries).Perm
      (readyContext width count).entries := by
  change (indexedEntry width count :: ((NumeratorMeasurement.context width).entries ++
    (List.range count).map (indexedEntry width))).Perm
      ((NumeratorMeasurement.context width).entries ++
        (List.range (count + 1)).map (indexedEntry width))
  rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, ← List.append_assoc]
  exact (List.perm_append_singleton _ _).symm

private lemma selector_fresh (width count : Nat) :
    indexedKey width count ∉ (withCells width count).keys := by
  have distinct := ((selector_entries width count).map RuntimeEntry.key).nodup_iff.mpr
    (readyContext width count).keysNodup
  exact (List.nodup_cons.mp distinct).1

private lemma selector_disjoint (width count : Nat) :
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

/-- The actual allocated selector contributes a physical system at every parameter width. -/
lemma after_systemCount_pos (width count : Nat) : 0 < (after width count).systemCount := by
  let selector : Fin (after width count).systemCount :=
    PreparationBorrowed.fullPositionEquiv (withCells width count)
      (indexedKey width count) (indexedLayout width count)
      (selector_fresh width count) (selector_disjoint width count)
      (.inl (0 : Fin 1))
  exact lt_of_le_of_lt (Nat.zero_le selector.val) selector.isLt

/-- Prepare exactly one zero selector beyond all supplied exponent systems. -/
def prepareSelector (width count : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty) (withCells width count)
      (after width count) :=
  .prepareZero (withCells width count) (indexedKey width count) (indexedLayout width count)
    (selector_fresh width count) (selector_disjoint width count)

/-- Both charged quantum preparations and all actual result retains occur before the cascade. -/
def initializeWork (modulus count : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (before modulus.size count) (after modulus.size count) :=
  .seq (prepareAuxiliary modulus count)
    (.seq (allocateCells modulus.size count) (prepareSelector modulus.size count))

/-- The allocated output retains every common entry, original role and physical identity. -/
lemma body_entries (width count : Nat) :
    (readyContext width count).entries.Perm (after width count).entries :=
  (selector_entries width count).symm

/-- The complete output structurally reads all original measurement cells in the final context. -/
def output (width count : Nat) :
    Output (after width count) (.fixedVector width (.finite 2)) :=
  Output.all (after width count) (.read (ContextPermutation.input (body_entries width count)
    (ContextUnion.inputLeft
      (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)
      (MeasurementCells.input (InversePreparation.after width) 2 width))))

/-- Every live original or allocated entry occurs in the same complete output listing. -/
lemma output_listing (width count : Nat) :
    (output width count).listing = (after width count).keys := Output.all_listing _ _


/-- Every real zero preparation and every fixed-bit loading gate occurs in order. -/
def initializationTrace (modulus count : Nat) :
    List (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  (ZeroPreparation.eventTrace AlgorithmGate.model .empty
    (InputPreparation.auxiliaryLayout modulus.size) ++
    (InPlacePreparation.loadProgram modulus).eventTrace .empty .empty) ++
    ZeroPreparation.eventTrace AlgorithmGate.model .empty (indexedLayout modulus.size count)

/-- The actual initialization charges all auxiliary zeros, literal X loads and the selector zero. -/
lemma initializeWork_eventTrace (modulus count : Nat)
    (path : (initializeWork modulus count).Path) :
    (initializeWork modulus count).eventTrace path = initializationTrace modulus count := by
  have loaded : (prepareAuxiliary modulus count).eventTrace path.1 =
      ZeroPreparation.eventTrace AlgorithmGate.model .empty
        (InputPreparation.auxiliaryLayout modulus.size) ++
        (InPlacePreparation.loadProgram modulus).eventTrace .empty .empty :=
    InPlacePreparation.Framed.eventTrace modulus (exponents modulus.size count)
      (auxiliary_disjoint modulus.size count) path.1
  have retained : (allocateCells modulus.size count).eventTrace path.2.1 = [] :=
    MeasurementCells.allocateFramed_eventTrace (model := .quantum AlgorithmGate.model .empty)
      (InversePreparation.after modulus.size) (exponents modulus.size count)
      2 modulus.size (complete_disjoint modulus.size count) path.2.1
  change (prepareAuxiliary modulus count).eventTrace path.1 ++
    ((allocateCells modulus.size count).eventTrace path.2.1 ++
      ZeroPreparation.eventTrace AlgorithmGate.model .empty (indexedLayout modulus.size count)) =
    (ZeroPreparation.eventTrace AlgorithmGate.model .empty
      (InputPreparation.auxiliaryLayout modulus.size) ++
      (InPlacePreparation.loadProgram modulus).eventTrace .empty .empty) ++
      ZeroPreparation.eventTrace AlgorithmGate.model .empty (indexedLayout modulus.size count)
  rw [loaded, retained, List.nil_append]

/-- The resource pool is derived from exactly those emitted native events. -/
lemma initializeWork_resourcePool (modulus count : Nat)
    (path : (initializeWork modulus count).Path) :
    (initializeWork modulus count).resourcePool path =
      ResourcePool.ofList (initializationTrace modulus count) :=
  congrArg ResourcePool.ofList (initializeWork_eventTrace modulus count path)

/-- Zero allocation and X loading preserve every store block and the full resident reference. -/
lemma prepareAuxiliary_execute (modulus count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (before modulus.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    splitServiceState (InversePreparation.after modulus.size) (exponents modulus.size count)
      (auxiliary_disjoint modulus.size count)
      ((prepareAuxiliary modulus count).execute environment Reference state) =
      ((InPlacePreparation.circuit modulus).execute environment
        (Register.prod (exponents modulus.size count).register Reference)
        (splitServiceState (InversePreparation.before modulus.size) (exponents modulus.size count)
          (input_disjoint modulus.size count) state)).mapHistory
            (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) :=
  InPlacePreparation.Framed.execute
    (environment := environment) modulus (exponents modulus.size count)
    (auxiliary_disjoint modulus.size count) state

/-- The original retained cells keep every store, service, history and reference coordinate. -/
lemma allocateCells_execute (width count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ((InversePreparation.after width).disjointUnion (exponents width count)
      (auxiliary_disjoint width count)) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    splitServiceState (NumeratorMeasurement.context width) (exponents width count)
      (complete_disjoint width count)
      ((allocateCells width count).execute environment Reference state) =
      ((MeasurementCells.allocate (model := .quantum AlgorithmGate.model .empty)
        (InversePreparation.after width) 2 width).execute environment
        (Register.prod (exponents width count).register Reference)
        (splitServiceState (InversePreparation.after width) (exponents width count)
          (auxiliary_disjoint width count) state)).mapHistory
            (fun record => (record.1, (record.2.1.1, (record.2.1.2,
              MeasurementCells.allocateFramedPathEquiv
                (model := .quantum AlgorithmGate.model .empty)
                (InversePreparation.after width) (exponents width count) 2 width
                (complete_disjoint width count) record.2.2)))) :=
  MeasurementCells.allocateFramed_execute
    (environment := environment) (model := .quantum AlgorithmGate.model .empty)
    (InversePreparation.after width) (exponents width count) 2 width
    (complete_disjoint width count) state

/-- The selector instruction adds its actual zero factor to the complete incoming state. -/
lemma prepareSelector_execute (width count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (withCells width count) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (prepareSelector width count).execute environment Reference state =
      (state.prepare (indexedKey width count) (indexedLayout width count)
        (selector_fresh width count) (selector_disjoint width count)
        (BasisPreparation.zero (indexedLayout width count))).mapHistory
          (fun record => (record.1.1, (record.1.2, record.2))) := rfl
end

end MeasuredPlacement.Allocation
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
