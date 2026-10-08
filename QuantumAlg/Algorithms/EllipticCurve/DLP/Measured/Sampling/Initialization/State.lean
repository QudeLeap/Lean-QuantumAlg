/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Initialization
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Initialization.Cells

/-!
# Complete block and record target for actual scalar initialization

The prescribed tensor density is applied separately to each original
classical-history block. Actual store pushes provide the output records:
auxiliary presence, every original numerator-result cell, then the selector
presence. No original classical value or quantum-reference coherence is
supplied again after execution begins.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion MeasuredUncompute ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation MAU.Inversion.SharedEEA
open GenericPointAddition.InPlace

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The independently prescribed initialization density in every original complete block. -/
def initializationBlocks (modulus count : Nat) {C : Type} [Fintype C] {Reference : Register}
    (state : ExecutionState C (Register.prod (before modulus.size count).register Reference)) :
    ExecutionState C (Register.prod (after modulus.size count).register Reference) where
  block value := initializedDensity modulus count Reference (state.block value)
  total_le_one := by
    simp only [initializedDensity_mass]
    exact state.total_le_one

private def auxiliaryBlocks (modulus count : Nat) {C : Type} [Fintype C]
    {Reference : Register}
    (state : ExecutionState C (Register.prod (before modulus.size count).register Reference)) :
    ExecutionState C (Register.prod
      ((InversePreparation.after modulus.size).disjointUnion (exponents modulus.size count)
        (auxiliary_disjoint modulus.size count)).register Reference) :=
  prepareContext (ctx := before modulus.size count) state InversePreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size)
    (preparation_fresh_union InversePreparation.auxiliaryKey
      (InputPreparation.auxiliaryLayout modulus.size)
      (InversePreparation.auxiliary_fresh modulus.size)
      (InversePreparation.auxiliary_disjoint modulus.size)
      (auxiliary_disjoint modulus.size count))
    (preparation_wires_union InversePreparation.auxiliaryKey
      (InputPreparation.auxiliaryLayout modulus.size)
      (InversePreparation.auxiliary_fresh modulus.size)
      (InversePreparation.auxiliary_disjoint modulus.size)
      (auxiliary_disjoint modulus.size count))
    (InPlacePreparation.preparation modulus).normalized

private def cellBlocks (width count : Nat) {C : Type} [Fintype C] {Reference : Register}
    (state : ExecutionState C (Register.prod
      ((InversePreparation.after width).disjointUnion (exponents width count)
        (auxiliary_disjoint width count)).register Reference)) :
    ExecutionState C (Register.prod (withCells width count).register Reference) :=
  state.reindex (S := Register.prod (withCells width count).register Reference)
    (MeasurementCells.framedJointBasisEquiv (InversePreparation.after width)
      (exponents width count) 2 width (complete_disjoint width count) Reference)

private def selectorBlocks (width count : Nat) {C : Type} [Fintype C]
    {Reference : Register}
    (state : ExecutionState C (Register.prod (withCells width count).register Reference)) :
    ExecutionState C (Register.prod (after width count).register Reference) :=
  prepareContext (ctx := withCells width count) state (indexedKey width count)
    (indexedLayout width count) (selector_fresh width count) (selector_disjoint width count)
    (BasisPreparation.zero (indexedLayout width count)).normalized

private def auxiliaryRecord (modulus count : Nat) (History : Type)
    (record : Store (before modulus.size count) ×
      (ClassicalOracleModel.empty.HiddenState × History)) :
    Store ((InversePreparation.after modulus.size).disjointUnion (exponents modulus.size count)
      (auxiliary_disjoint modulus.size count)) ×
        (ClassicalOracleModel.empty.HiddenState ×
          (History × (prepareAuxiliary modulus count).Path)) :=
  (record.1.pushOwnedLayout InversePreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size)
    (preparation_fresh_union InversePreparation.auxiliaryKey
      (InputPreparation.auxiliaryLayout modulus.size)
      (InversePreparation.auxiliary_fresh modulus.size)
      (InversePreparation.auxiliary_disjoint modulus.size)
      (auxiliary_disjoint modulus.size count))
    (preparation_wires_union InversePreparation.auxiliaryKey
      (InputPreparation.auxiliaryLayout modulus.size)
      (InversePreparation.auxiliary_fresh modulus.size)
      (InversePreparation.auxiliary_disjoint modulus.size)
      (auxiliary_disjoint modulus.size count)),
        (record.2.1, (record.2.2, ((), ()))))

private def selectorRecord (width count : Nat) (History : Type)
    (record : Store (withCells width count) ×
      (ClassicalOracleModel.empty.HiddenState × History)) :
    Store (after width count) ×
      (ClassicalOracleModel.empty.HiddenState × (History × Unit)) :=
  (record.1.pushOwnedLayout (indexedKey width count) (indexedLayout width count)
    (selector_fresh width count) (selector_disjoint width count),
      (record.2.1, (record.2.2, ())))

/-- Actual preparation markers and retained finite cells determine each final classical record. -/
def initializationRecord (modulus count : Nat) (History : Type)
    (record : Store (before modulus.size count) ×
      (ClassicalOracleModel.empty.HiddenState × History)) :
    Store (after modulus.size count) ×
      (ClassicalOracleModel.empty.HiddenState ×
        (History × (initializeWork modulus count).Path)) :=
  let auxiliary := auxiliaryRecord modulus count History record
  let cells := scalarCellsRecord modulus.size count
    (History × (prepareAuxiliary modulus count).Path) auxiliary
  let selected := selectorRecord modulus.size count
    ((History × (prepareAuxiliary modulus count).Path) ×
      (allocateCells modulus.size count).Path) cells
  (selected.1, (selected.2.1,
    (selected.2.2.1.1.1, (selected.2.2.1.1.2,
      (selected.2.2.1.2, selected.2.2.2)))))

private theorem auxiliaryBlocks_entry (modulus count : Nat)
    {C : Type} [Fintype C] {Reference : Register}
    (state : ExecutionState C (Register.prod (before modulus.size count).register Reference))
    (label : C) (newRow newColumn : (InputPreparation.auxiliaryLayout modulus.size).register.Index)
    (oldRow oldColumn : (Register.prod (before modulus.size count).register Reference).Index) :
    ((auxiliaryBlocks modulus count state).block label).matrix
      (auxiliaryAssembly modulus count (newRow, oldRow.1), oldRow.2)
      (auxiliaryAssembly modulus count (newColumn, oldColumn.1), oldColumn.2) =
      ((InPlacePreparation.preparation modulus).normalized.vec newRow *
        star ((InPlacePreparation.preparation modulus).normalized.vec newColumn)) *
          (state.block label).matrix oldRow oldColumn :=
  prepareContext_joined_entry state InversePreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size)
    (preparation_fresh_union InversePreparation.auxiliaryKey
      (InputPreparation.auxiliaryLayout modulus.size)
      (InversePreparation.auxiliary_fresh modulus.size)
      (InversePreparation.auxiliary_disjoint modulus.size)
      (auxiliary_disjoint modulus.size count))
    (preparation_wires_union InversePreparation.auxiliaryKey
      (InputPreparation.auxiliaryLayout modulus.size)
      (InversePreparation.auxiliary_fresh modulus.size)
      (InversePreparation.auxiliary_disjoint modulus.size)
      (auxiliary_disjoint modulus.size count))
    (InPlacePreparation.preparation modulus).normalized label newRow newColumn oldRow oldColumn

private theorem cellBlocks_entry (width count : Nat)
    {C : Type} [Fintype C] {Reference : Register}
    (state : ExecutionState C (Register.prod
      ((InversePreparation.after width).disjointUnion (exponents width count)
        (auxiliary_disjoint width count)).register Reference)) (label : C)
    (row column : (Register.prod
      ((InversePreparation.after width).disjointUnion (exponents width count)
        (auxiliary_disjoint width count)).register Reference).Index) :
    ((cellBlocks width count state).block label).matrix
      (cellsAssembly width count row.1, row.2) (cellsAssembly width count column.1, column.2) =
        (state.block label).matrix row column := by
  let basis := MeasurementCells.framedJointBasisEquiv (InversePreparation.after width)
    (exponents width count) 2 width (complete_disjoint width count) Reference
  change ((state.reindex (S := Register.prod (withCells width count).register Reference)
    basis).block label).matrix (basis row) (basis column) = _
  change (state.block label).matrix (basis.symm (basis row))
    (basis.symm (basis column)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

private theorem selectorBlocks_entry (width count : Nat)
    {C : Type} [Fintype C] {Reference : Register}
    (state : ExecutionState C (Register.prod (withCells width count).register Reference))
    (label : C) (newRow newColumn : (indexedLayout width count).register.Index)
    (oldRow oldColumn : (Register.prod (withCells width count).register Reference).Index) :
    ((selectorBlocks width count state).block label).matrix
      (selectorAssembly width count (newRow, oldRow.1), oldRow.2)
      (selectorAssembly width count (newColumn, oldColumn.1), oldColumn.2) =
      ((BasisPreparation.zero (indexedLayout width count)).normalized.vec newRow *
        star ((BasisPreparation.zero (indexedLayout width count)).normalized.vec newColumn)) *
          (state.block label).matrix oldRow oldColumn :=
  prepareContext_joined_entry state (indexedKey width count) (indexedLayout width count)
    (selector_fresh width count) (selector_disjoint width count)
    (BasisPreparation.zero (indexedLayout width count)).normalized label
    newRow newColumn oldRow oldColumn

private theorem selectorCellsBlocks_entry (width count : Nat)
    {C : Type} [Fintype C] {Reference : Register}
    (state : ExecutionState C (Register.prod
      ((InversePreparation.after width).disjointUnion (exponents width count)
        (auxiliary_disjoint width count)).register Reference)) (label : C)
    (newRow newColumn : (indexedLayout width count).register.Index)
    (row column : (Register.prod
      ((InversePreparation.after width).disjointUnion (exponents width count)
        (auxiliary_disjoint width count)).register Reference).Index) :
    ((selectorBlocks width count (cellBlocks width count state)).block label).matrix
      (selectorAssembly width count (newRow, cellsAssembly width count row.1), row.2)
      (selectorAssembly width count (newColumn, cellsAssembly width count column.1), column.2) =
      ((BasisPreparation.zero (indexedLayout width count)).normalized.vec newRow *
        star ((BasisPreparation.zero (indexedLayout width count)).normalized.vec newColumn)) *
          (state.block label).matrix row column := by
  have selected := selectorBlocks_entry width count (Reference := Reference)
    (cellBlocks width count state) label newRow newColumn
    (cellsAssembly width count row.1, row.2) (cellsAssembly width count column.1, column.2)
  have cells := cellBlocks_entry width count (Reference := Reference) state label row column
  exact selected.trans (congrArg (fun value : ℂ =>
    ((BasisPreparation.zero (indexedLayout width count)).normalized.vec newRow *
      star ((BasisPreparation.zero (indexedLayout width count)).normalized.vec newColumn)) * value)
        cells)

section AssembledBlocks

attribute [local irreducible] auxiliaryBlocks cellBlocks selectorBlocks initializedDensity
  auxiliaryAssembly cellsAssembly selectorAssembly

private theorem initialized_preparedBlocks_entry (modulus count : Nat)
    {C : Type} [Fintype C] {Reference : Register}
    (state : ExecutionState C (Register.prod (before modulus.size count).register Reference))
    (label : C) (selectorRow selectorColumn : (indexedLayout modulus.size count).register.Index)
    (auxiliaryRow auxiliaryColumn : (InputPreparation.auxiliaryLayout modulus.size).register.Index)
    (oldRow oldColumn : (Register.prod (before modulus.size count).register Reference).Index) :
    ((selectorBlocks modulus.size count (Reference := Reference)
      (cellBlocks modulus.size count (Reference := Reference)
        (auxiliaryBlocks modulus count (Reference := Reference) state))).block label).matrix
      (initializedJointAssembly modulus count Reference (selectorRow, auxiliaryRow, oldRow))
      (initializedJointAssembly modulus count Reference
        (selectorColumn, auxiliaryColumn, oldColumn)) =
      (initializedDensity modulus count Reference (state.block label)).matrix
        (initializedJointAssembly modulus count Reference (selectorRow, auxiliaryRow, oldRow))
        (initializedJointAssembly modulus count Reference
          (selectorColumn, auxiliaryColumn, oldColumn)) := by
  change ((selectorBlocks modulus.size count (Reference := Reference)
      (cellBlocks modulus.size count (Reference := Reference)
        (auxiliaryBlocks modulus count (Reference := Reference) state))).block label).matrix
      (selectorAssembly modulus.size count (selectorRow, cellsAssembly modulus.size count
        (auxiliaryAssembly modulus count (auxiliaryRow, oldRow.1))), oldRow.2)
      (selectorAssembly modulus.size count (selectorColumn, cellsAssembly modulus.size count
        (auxiliaryAssembly modulus count (auxiliaryColumn, oldColumn.1))), oldColumn.2) = _
  have selected := selectorCellsBlocks_entry modulus.size count (Reference := Reference)
    (auxiliaryBlocks modulus count state) label selectorRow selectorColumn
    (auxiliaryAssembly modulus count (auxiliaryRow, oldRow.1), oldRow.2)
    (auxiliaryAssembly modulus count (auxiliaryColumn, oldColumn.1), oldColumn.2)
  have auxiliary := auxiliaryBlocks_entry modulus count (Reference := Reference) state label
    auxiliaryRow auxiliaryColumn oldRow oldColumn
  have complete := selected.trans (congrArg (fun value : ℂ =>
    ((BasisPreparation.zero (indexedLayout modulus.size count)).normalized.vec selectorRow *
      star ((BasisPreparation.zero (indexedLayout modulus.size count)).normalized.vec
        selectorColumn)) * value) auxiliary)
  have predicted := initializedDensity_entry modulus count Reference (state.block label)
    selectorRow selectorColumn auxiliaryRow auxiliaryColumn oldRow oldColumn
  exact complete.trans predicted.symm

private theorem initialized_preparedBlocks (modulus count : Nat)
    {C : Type} [Fintype C] {Reference : Register}
    (state : ExecutionState C (Register.prod (before modulus.size count).register Reference)) :
    selectorBlocks modulus.size count (Reference := Reference)
        (cellBlocks modulus.size count (Reference := Reference)
          (auxiliaryBlocks modulus count (Reference := Reference) state)) =
      initializationBlocks modulus count (Reference := Reference) state := by
  apply ExecutionState.ext
  intro label
  apply DensityOperator.ext
  ext row column
  obtain ⟨⟨selectorRow, auxiliaryRow, oldRow⟩, rfl⟩ :=
    (initializedJointAssembly modulus count Reference).surjective row
  obtain ⟨⟨selectorColumn, auxiliaryColumn, oldColumn⟩, rfl⟩ :=
    (initializedJointAssembly modulus count Reference).surjective column
  exact initialized_preparedBlocks_entry modulus count state label
    selectorRow selectorColumn auxiliaryRow auxiliaryColumn oldRow oldColumn

end AssembledBlocks

private theorem auxiliary_load_density (modulus count : Nat) {Reference : Register}
    (density : DensityOperator (Register.prod (before modulus.size count).register Reference)) :
    DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor
        (frameUnitary (InversePreparation.after modulus.size)
          (exponents modulus.size count) (auxiliary_disjoint modulus.size count)
          (InPlacePreparation.loadProgram modulus)).matrix
        (1 : UnitaryOperator Reference))
      (preparedDensity InversePreparation.auxiliaryKey
        (InputPreparation.auxiliaryLayout modulus.size)
        (preparation_fresh_union InversePreparation.auxiliaryKey
          (InputPreparation.auxiliaryLayout modulus.size)
          (InversePreparation.auxiliary_fresh modulus.size)
          (InversePreparation.auxiliary_disjoint modulus.size)
          (auxiliary_disjoint modulus.size count))
        (preparation_wires_union InversePreparation.auxiliaryKey
          (InputPreparation.auxiliaryLayout modulus.size)
          (InversePreparation.auxiliary_fresh modulus.size)
          (InversePreparation.auxiliary_disjoint modulus.size)
          (auxiliary_disjoint modulus.size count))
        (BasisPreparation.zero (InputPreparation.auxiliaryLayout modulus.size)).normalized
        Reference density) =
      preparedDensity InversePreparation.auxiliaryKey
        (InputPreparation.auxiliaryLayout modulus.size)
        (preparation_fresh_union InversePreparation.auxiliaryKey
          (InputPreparation.auxiliaryLayout modulus.size)
          (InversePreparation.auxiliary_fresh modulus.size)
          (InversePreparation.auxiliary_disjoint modulus.size)
          (auxiliary_disjoint modulus.size count))
        (preparation_wires_union InversePreparation.auxiliaryKey
          (InputPreparation.auxiliaryLayout modulus.size)
          (InversePreparation.auxiliary_fresh modulus.size)
          (InversePreparation.auxiliary_disjoint modulus.size)
          (auxiliary_disjoint modulus.size count))
        (InPlacePreparation.preparation modulus).normalized Reference density := by
  apply preparedDensity_frameUnitary_transport
    (ctx := InversePreparation.before modulus.size)
    (frame := exponents modulus.size count)
    InversePreparation.auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
    (InversePreparation.auxiliary_fresh modulus.size)
    (InversePreparation.auxiliary_disjoint modulus.size)
    (auxiliary_disjoint modulus.size count)
    (InPlacePreparation.loadProgram modulus)
    (BasisPreparation.zero (InputPreparation.auxiliaryLayout modulus.size))
    (InPlacePreparation.preparation modulus)
    (fun {R} input => by
      exact preparedDensity_load_ket InversePreparation.auxiliaryKey
        (InputPreparation.auxiliaryLayout modulus.size)
        (InversePreparation.auxiliary_fresh modulus.size)
        (InversePreparation.auxiliary_disjoint modulus.size)
        (BasisPreparation.zero (InputPreparation.auxiliaryLayout modulus.size)).value
        (InPlacePreparation.preparation modulus).value
        (InPlacePreparation.loadProgram modulus).matrix
        (InPlacePreparation.loadProgram_seed modulus) input)
    Reference density

private theorem unitary_mapClassical_instances {C D : Type}
    [Fintype C] [Fintype D] {R : Register}
    {first result : DecidableEq D} (state : ExecutionState C R)
    (update : C → D) (operator : D → UnitaryOperator R) :
    (@ExecutionState.mapClassical C D _ _ R first state update).applyUnitary operator =
      @ExecutionState.mapClassical C D _ _ R result
        (state.applyUnitary (fun value => operator (update value))) update := by
  cases Subsingleton.elim first result
  exact ExecutionState.applyUnitary_mapClassical state update operator

private theorem auxiliary_execution (modulus count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (before modulus.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (prepareAuxiliary modulus count).execute Reference state =
      (auxiliaryBlocks modulus count state).mapClassical
        (auxiliaryRecord modulus count History) := by
  let zeroBlocks := prepareContext (ctx := before modulus.size count) state
    InversePreparation.auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
    (preparation_fresh_union InversePreparation.auxiliaryKey
      (InputPreparation.auxiliaryLayout modulus.size)
      (InversePreparation.auxiliary_fresh modulus.size)
      (InversePreparation.auxiliary_disjoint modulus.size)
      (auxiliary_disjoint modulus.size count))
    (preparation_wires_union InversePreparation.auxiliaryKey
      (InputPreparation.auxiliaryLayout modulus.size)
      (InversePreparation.auxiliary_fresh modulus.size)
      (InversePreparation.auxiliary_disjoint modulus.size)
      (auxiliary_disjoint modulus.size count))
    (BasisPreparation.zero (InputPreparation.auxiliaryLayout modulus.size)).normalized
  let operation := UnitaryOperator.prodTensor
    (frameUnitary (InversePreparation.after modulus.size)
      (exponents modulus.size count) (auxiliary_disjoint modulus.size count)
      (InPlacePreparation.loadProgram modulus)).matrix
    (1 : UnitaryOperator Reference)
  have loaded : zeroBlocks.applyUnitary (fun _ => operation) =
      auxiliaryBlocks modulus count state := by
    apply ExecutionState.ext
    intro label
    exact auxiliary_load_density modulus count (state.block label)
  change (prepareFramed InversePreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size)
    (InversePreparation.auxiliary_fresh modulus.size)
    (InversePreparation.auxiliary_disjoint modulus.size)
    (auxiliary_disjoint modulus.size count)
    (InPlacePreparation.loadProgram modulus)).execute Reference state = _
  unfold prepareFramed
  unfold prepareZeroFramed
  erw [Circuit.execute_seq]
  erw [Circuit.execute_unitary (H := History × Unit)]
  erw [Circuit.execute_prepareZero]
  dsimp only [State.prepare, State.mapHistory]
  erw [unitary_mapClassical_instances (result := Classical.decEq _),
    unitary_mapClassical_instances (result := Classical.decEq _)]
  erw [loaded]
  dsimp only [Circuit.Path]
  erw [ExecutionState.executionState_mapClassical_comp_instances
    (result := Classical.decEq _)]
  erw [ExecutionState.executionState_mapClassical_comp_instances
    (result := Classical.decEq _)]
  erw [ExecutionState.executionState_mapClassical_comp_instances
    (result := Classical.decEq _)]
  apply ExecutionState.executionState_mapClassical_congr
    (D := Store ((InversePreparation.after modulus.size).disjointUnion
      (exponents modulus.size count) (auxiliary_disjoint modulus.size count)) ×
      (ClassicalOracleModel.empty.HiddenState ×
        (History × (prepareAuxiliary modulus count).Path)))
  funext record
  rfl

private theorem selector_execution (width count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (withCells width count) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (prepareSelector width count).execute Reference state =
      (selectorBlocks width count state).mapClassical (selectorRecord width count History) :=
  by
    change (Circuit.prepareZero (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := .empty) (classicalOracles := .empty)
      (withCells width count) (indexedKey width count) (indexedLayout width count)
      (selector_fresh width count) (selector_disjoint width count)).execute Reference state = _
    rw [Circuit.execute_prepareZero]
    dsimp only [State.prepare, State.mapHistory, selectorBlocks]
    exact
      (ExecutionState.executionState_mapClassical_comp_instances
        (result := Classical.decEq _) _ _ _).trans
          (ExecutionState.executionState_mapClassical_congr _ rfl)

private theorem cells_execution (width count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ((InversePreparation.after width).disjointUnion (exponents width count)
      (auxiliary_disjoint width count)) Reference
        (ClassicalOracleModel.empty.HiddenState × History)) :
    (allocateCells width count).execute Reference state =
      (cellBlocks width count state).mapClassical (scalarCellsRecord width count History) :=
  allocateCells_execution width count state

private theorem cellBlocks_mapClassical (width count : Nat)
    {C D : Type} [Fintype C] [Fintype D] {Reference : Register}
    (state : ExecutionState C (Register.prod
      ((InversePreparation.after width).disjointUnion (exponents width count)
        (auxiliary_disjoint width count)).register Reference)) (update : C → D) :
    cellBlocks width count (state.mapClassical update) =
      (cellBlocks width count state).mapClassical update :=
  (ExecutionState.coordinate_reindex_mapClassical state _ update).symm

private theorem selectorBlocks_mapClassical (width count : Nat)
    {C D : Type} [Fintype C] [Fintype D] {Reference : Register}
    (state : ExecutionState C (Register.prod (withCells width count).register Reference))
    (update : C → D) :
    selectorBlocks width count (state.mapClassical update) =
      (selectorBlocks width count state).mapClassical update :=
  State.prepareContext_mapClassical_decision state _ _ _ _ _ update

private theorem initialization_blocks_records (modulus count : Nat)
    {C A B D F G : Type} [Fintype C] [Fintype A] [Fintype B]
    [Fintype D] [Fintype F] [Fintype G] {Reference : Register}
    (state : ExecutionState C (Register.prod (before modulus.size count).register Reference))
    (first : C → A) (second : A → B) (third : B → D) (fourth : D → F) (fifth : F → G) :
    ((((selectorBlocks modulus.size count (Reference := Reference)
      ((cellBlocks modulus.size count (Reference := Reference)
        ((auxiliaryBlocks modulus count (Reference := Reference) state).mapClassical first))
        |>.mapClassical second)).mapClassical third).mapClassical fourth).mapClassical fifth) =
      (initializationBlocks modulus count (Reference := Reference) state).mapClassical
        (fifth ∘ fourth ∘ third ∘ second ∘ first) := by
  rw [cellBlocks_mapClassical, selectorBlocks_mapClassical,
    selectorBlocks_mapClassical, initialized_preparedBlocks]
  simp only [ExecutionState.executionState_mapClassical_comp, Function.comp_def]

private def stagedInitialization (modulus count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (before modulus.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    State (after modulus.size count) Reference
      (ClassicalOracleModel.empty.HiddenState ×
        (History × (initializeWork modulus count).Path)) :=
  let auxiliary : State
      ((InversePreparation.after modulus.size).disjointUnion (exponents modulus.size count)
        (auxiliary_disjoint modulus.size count)) Reference
      (ClassicalOracleModel.empty.HiddenState ×
        (History × (prepareAuxiliary modulus count).Path)) :=
    (auxiliaryBlocks modulus count state).mapClassical (auxiliaryRecord modulus count History)
  let cells : State (withCells modulus.size count) Reference
      (ClassicalOracleModel.empty.HiddenState ×
        ((History × (prepareAuxiliary modulus count).Path) ×
          (allocateCells modulus.size count).Path)) :=
    (cellBlocks modulus.size count auxiliary).mapClassical
      (scalarCellsRecord modulus.size count (History × (prepareAuxiliary modulus count).Path))
  let selected : State (after modulus.size count) Reference
      (ClassicalOracleModel.empty.HiddenState ×
        (((History × (prepareAuxiliary modulus count).Path) ×
          (allocateCells modulus.size count).Path) × (prepareSelector modulus.size count).Path)) :=
    (selectorBlocks modulus.size count cells).mapClassical
      (selectorRecord modulus.size count ((History × (prepareAuxiliary modulus count).Path) ×
        (allocateCells modulus.size count).Path))
  State.mapHistory (ctx := after modulus.size count)
    (State.mapHistory (ctx := after modulus.size count) selected
      (K := ClassicalOracleModel.empty.HiddenState ×
        ((History × (prepareAuxiliary modulus count).Path) ×
          ((allocateCells modulus.size count).seq (prepareSelector modulus.size count)).Path))
      (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))))
    (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2))))

section StagedExecution

attribute [local irreducible] auxiliaryBlocks cellBlocks selectorBlocks
  auxiliaryRecord scalarCellsRecord selectorRecord ExecutionState.mapClassical

private theorem initializeWork_staged_execute (modulus count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (before modulus.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (initializeWork modulus count).execute Reference state =
      stagedInitialization modulus count state := by
  dsimp only [initializeWork]
  simp only [Circuit.execute_seq]
  rw [auxiliary_execution]
  erw [cells_execution, selector_execution]
  dsimp only [stagedInitialization]
  congr 7 <;> exact Subsingleton.elim _ _

end StagedExecution

section ActualComposition

attribute [local irreducible] auxiliaryBlocks cellBlocks selectorBlocks initializationBlocks
  auxiliaryRecord scalarCellsRecord selectorRecord ExecutionState.mapClassical

private theorem stagedInitialization_eq (modulus count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (before modulus.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    stagedInitialization modulus count state =
      (initializationBlocks modulus count state).mapClassical
        (initializationRecord modulus count History) := by
  dsimp only [stagedInitialization, State.mapHistory]
  have merged := initialization_blocks_records modulus count
    (A := Store ((InversePreparation.after modulus.size).disjointUnion
      (exponents modulus.size count) (auxiliary_disjoint modulus.size count)) ×
        (ClassicalOracleModel.empty.HiddenState ×
          (History × (prepareAuxiliary modulus count).Path)))
    (B := Store (withCells modulus.size count) ×
      (ClassicalOracleModel.empty.HiddenState ×
        ((History × (prepareAuxiliary modulus count).Path) ×
          (allocateCells modulus.size count).Path)))
    (D := Store (after modulus.size count) ×
      (ClassicalOracleModel.empty.HiddenState ×
        (((History × (prepareAuxiliary modulus count).Path) ×
          (allocateCells modulus.size count).Path) ×
          (prepareSelector modulus.size count).Path)))
    (F := Store (after modulus.size count) ×
      (ClassicalOracleModel.empty.HiddenState ×
        ((History × (prepareAuxiliary modulus count).Path) ×
          ((allocateCells modulus.size count).seq (prepareSelector modulus.size count)).Path)))
    (G := Store (after modulus.size count) ×
      (ClassicalOracleModel.empty.HiddenState ×
        (History × (initializeWork modulus count).Path)))
    (Reference := Reference) state
    (auxiliaryRecord modulus count History)
    (scalarCellsRecord modulus.size count (History × (prepareAuxiliary modulus count).Path))
    (selectorRecord modulus.size count ((History × (prepareAuxiliary modulus count).Path) ×
      (allocateCells modulus.size count).Path))
    (fun record => (record.1, (record.2.1,
      (record.2.2.1.1, (record.2.2.1.2, record.2.2.2)))))
    (fun record => (record.1, (record.2.1,
      (record.2.2.1.1, (record.2.2.1.2, record.2.2.2)))))
  have updates :
      (fun record => (record.1, (record.2.1,
        (record.2.2.1.1, (record.2.2.1.2, record.2.2.2))))) ∘
        (fun record => (record.1, (record.2.1,
          (record.2.2.1.1, (record.2.2.1.2, record.2.2.2))))) ∘
        selectorRecord modulus.size count
          ((History × (prepareAuxiliary modulus count).Path) ×
            (allocateCells modulus.size count).Path) ∘
        scalarCellsRecord modulus.size count (History × (prepareAuxiliary modulus count).Path) ∘
        auxiliaryRecord modulus count History = initializationRecord modulus count History := rfl
  have rewritten := congrArg
    (fun update : Store (before modulus.size count) ×
        (ClassicalOracleModel.empty.HiddenState × History) →
      Store (after modulus.size count) ×
        (ClassicalOracleModel.empty.HiddenState ×
          (History × (initializeWork modulus count).Path)) =>
        (initializationBlocks modulus count state).mapClassical update) updates
  have combined := merged.trans ((State.mapClassical_decision _ _ _ _).trans rewritten)
  convert combined using 1
  congr 7 <;> exact Subsingleton.elim _ _

/-- The actual two preparations and all original retains have the complete prescribed state. -/
theorem initializeWork_execute (modulus count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (before modulus.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (initializeWork modulus count).execute Reference state =
      (initializationBlocks modulus count state).mapClassical
        (initializationRecord modulus count History) :=
  (initializeWork_staged_execute modulus count state).trans
    (stagedInitialization_eq modulus count state)

end ActualComposition

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
