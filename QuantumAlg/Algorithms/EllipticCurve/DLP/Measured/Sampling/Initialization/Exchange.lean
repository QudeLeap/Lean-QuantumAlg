/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Initialization.State

/-!
# Complete execution exchange of original exponent preparation and initialization

The actual initialization record keeps the same classical values and the same
retained-cell path when an earlier mathematical history is regrouped. Combined
with the full block tensor identity, this exchanges the actual exponent
instruction with the actual two preparations and all original result retains.
Only the mathematical execution path is reordered.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion MeasuredUncompute ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation MAU.Inversion.SharedEEA
open GenericPointAddition.InPlace MeasurementCells

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem framedAllocationRecord_history (ctx frame : RuntimeCtx .quantum)
    (dimension : ℕ+) (History : Type) (count : Nat)
    (separate : RuntimeCtx.StorageDisjoint (MeasurementCells.context ctx dimension count) frame)
    (stored : Store
      (ctx.disjointUnion frame (original_disjoint ctx frame dimension count separate)))
    (history : History) :
    framedAllocationRecord ctx frame dimension History count separate (stored, history) =
      let actual := framedAllocationRecord ctx frame dimension Unit count separate (stored, ())
      (actual.1, (history, actual.2.2)) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [framedAllocationRecord]
      rw [induction]

private theorem initializationRecord_mapHistory (modulus count : Nat) {H K : Type}
    (stored : Store (before modulus.size count)) (history : H) (update : H → K) :
    initializationRecord modulus count K (stored, update history) =
      let actual := initializationRecord modulus count H (stored, history)
      (actual.1, (update actual.2.1, actual.2.2)) := by
  simp only [initializationRecord, auxiliaryRecord, selectorRecord, scalarCellsRecord]
  erw [framedAllocationRecord_history (History := K × Unit),
    framedAllocationRecord_history (History := H × Unit)]

private theorem auxiliaryBlocks_mapClassical (modulus count : Nat)
    {C D : Type} [Fintype C] [Fintype D] {Reference : Register}
    (state : ExecutionState C (Register.prod (before modulus.size count).register Reference))
    (update : C → D) :
    auxiliaryBlocks modulus count (state.mapClassical update) =
      (auxiliaryBlocks modulus count state).mapClassical update :=
  State.prepareContext_mapClassical_decision state _ _ _ _ _ update

private theorem initializationBlocks_mapClassical (modulus count : Nat)
    {C D : Type} [Fintype C] [Fintype D] {Reference : Register}
    (state : ExecutionState C (Register.prod (before modulus.size count).register Reference))
    (update : C → D) :
    initializationBlocks modulus count (state.mapClassical update) =
      (initializationBlocks modulus count state).mapClassical update := by
  rw [← initialized_preparedBlocks, ← initialized_preparedBlocks]
  rw [auxiliaryBlocks_mapClassical, cellBlocks_mapClassical, selectorBlocks_mapClassical]

private theorem initializationBlocks_mapClassical_decision (modulus count : Nat)
    {C D : Type} [Fintype C] [Fintype D] (decision : DecidableEq D) {Reference : Register}
    (state : ExecutionState C (Register.prod (before modulus.size count).register Reference))
    (update : C → D) :
    initializationBlocks modulus count
        (@ExecutionState.mapClassical C D _ _ _ decision state update) =
      @ExecutionState.mapClassical C D _ _ _ decision
        (initializationBlocks modulus count state) update := by
  have first := State.mapClassical_decision decision (Classical.decEq D) state update
  have last := State.mapClassical_decision (Classical.decEq D) decision
    (initializationBlocks modulus count state) update
  exact (congrArg (initializationBlocks modulus count) first).trans
    ((initializationBlocks_mapClassical modulus count state update).trans last)

private theorem initializationBlocks_unitary (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    {C : Type} [Fintype C] {Reference : Register}
    (state : ExecutionState C
      (Register.prod (before modulus.size (2 * exponentWidth)).register Reference)) :
    (initializationBlocks modulus (2 * exponentWidth) state).applyUnitary
        (fun _ => UnitaryOperator.prodTensor
          (afterExponentProgram modulus exponentWidth program physical).matrix
          (1 : UnitaryOperator Reference)) =
      initializationBlocks modulus (2 * exponentWidth)
        (state.applyUnitary fun _ =>
          beforeExponentOperator modulus exponentWidth program physical Reference) := by
  apply ExecutionState.ext
  intro label
  exact afterExponentOperator_initializedDensity modulus exponentWidth program physical
    Reference (state.block label)

private theorem initializeWork_unitary (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (before modulus.size (2 * exponentWidth)) Reference History) :
    ((initializeWork modulus (2 * exponentWidth)).execute Reference state).unitary
        (afterExponentProgram modulus exponentWidth program physical) =
      ((initializeWork modulus (2 * exponentWidth)).execute Reference
        (state.unitary (beforeExponentProgram modulus exponentWidth program physical))).mapHistory
          (fun record => ((record.1.1, record.2), record.1.2)) := by
  rw [initializeWork_execute, initializeWork_execute]
  simp only [State.unitary, ExecutionState.applyUnitary_mapClassical]
  rw [initializationBlocks_unitary, initializationBlocks_mapClassical_decision]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  have labels :
      (fun record : Store (before modulus.size (2 * exponentWidth)) × History =>
        let actual := initializationRecord modulus (2 * exponentWidth) History record
        (actual.1, (actual.2, ()))) =
      (fun record : Store (before modulus.size (2 * exponentWidth)) × History =>
        let actual := initializationRecord modulus (2 * exponentWidth) (History × Unit)
          (record.1, (record.2, ()))
        (actual.1, ((actual.2.1.1, actual.2.2), actual.2.1.2))) := by
    funext record
    rw [initializationRecord_mapHistory modulus (2 * exponentWidth)
      record.1 record.2 (fun history => (history, ()))]
  rw [labels]
  exact State.mapClassical_decision _ _ _ _

private theorem regroup_preparation_history {ctx : RuntimeCtx .quantum}
    {Reference : Register} {History Path : Type} [Fintype History] [Fintype Path]
    (state : State ctx Reference ((History × Unit) × Path)) :
    (state.mapHistory (fun record => ((record.1.1, record.2), record.1.2))).mapHistory
        (fun record => (record.1.1, (record.1.2, record.2))) =
      (state.mapHistory (fun record => (record.1.1, (record.1.2, record.2)))).mapHistory
        (fun record => (record.1, (record.2.2, record.2.1))) := by
  simp only [State.mapHistory_comp, Function.comp_def]

section ActualExchange

attribute [local irreducible] Circuit.execute State.unitary State.mapHistory
  ExecutionState.mapClassical

/-- The actual original exponent instruction commutes with initialization in the complete State. -/
theorem initializeWork_exponentCircuit_execute (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (before modulus.size (2 * exponentWidth)) Reference History) :
    ((initializeWork modulus (2 * exponentWidth)).seq
      (afterExponentCircuit modulus exponentWidth program physical)).execute Reference state =
      (((beforeExponentCircuit modulus exponentWidth program physical).seq
        (initializeWork modulus (2 * exponentWidth))).execute Reference state).mapHistory
          (fun record => (record.1, (record.2.2, record.2.1))) := by
  rw [Circuit.execute_seq, Circuit.execute_seq]
  simp only [beforeExponentCircuit, afterExponentCircuit, Circuit.execute_unitary]
  rw [initializeWork_unitary]
  exact regroup_preparation_history
    ((initializeWork modulus (2 * exponentWidth)).execute Reference
      (state.unitary (beforeExponentProgram modulus exponentWidth program physical)))

end ActualExchange

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
