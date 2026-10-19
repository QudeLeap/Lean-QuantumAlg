/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Embedding.Cells.State
import all QuantumAlg.Core.Execution.Measurement.Matrix
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws

/-!
# Exact full Store and quantum coordinates of existing terminal cells

These finite bijections only expose the same complete blocks as
underMeasurementCellsSplitState. They do not allocate, write, erase, or independently
prepare any cell.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Reference
namespace Terminal

noncomputable section

open QuantumAlg QuantumAlg.Execution
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {kind : ProblemKind} (ctx : RuntimeCtx kind) (dimension : ℕ+)

/-- The actual retained head has exactly its original Store and its new cell Store. -/
def retainedStoreEquiv (count : Nat) :
    Store (MeasurementCells.context ctx dimension (count + 1)) ≃
      (Store (MeasurementCells.context ctx dimension count) ×
        Store (Circuit.measurementCellFrame ctx dimension count)) :=
  (ContextPermutation.storeEquiv (Circuit.retainedLocalPermutation
    (MeasurementCells.context ctx dimension count)
    (MeasurementCells.context ctx dimension count).canonicalFreshKey (.finite dimension)
    (MeasurementCells.context ctx dimension count).canonicalFreshKey_fresh)).symm.trans
      (ContextUnion.storeEquiv (Circuit.retainedLocalDisjoint
        (MeasurementCells.context ctx dimension count)
        (MeasurementCells.context ctx dimension count).canonicalFreshKey (.finite dimension)
        (MeasurementCells.context ctx dimension count).canonicalFreshKey_fresh))

/-- Split every actual result cell, retaining its old value in allocation order. -/
def cellStoreEquiv : (count : Nat) →
    Store (MeasurementCells.context ctx dimension count) ≃
      (Store ctx × Circuit.measurementCellsHistory ctx dimension count)
  | 0 =>
    { toFun := fun stored => (stored, ())
      invFun := fun stored => stored.1
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨stored, ⟨⟩⟩; rfl }
  | count + 1 =>
      (retainedStoreEquiv ctx dimension count).trans
        (((cellStoreEquiv count).prodCongr (Equiv.refl _)).trans
          (Equiv.prodAssoc _ _ _))

/-- Every old cell's zero-wire register remains in the mathematical Reference. -/
def cellBasis : (count : Nat) → (Reference : Register) →
    ((MeasurementCells.context ctx dimension count).register.prod Reference).Index ≃
      (ctx.register.prod
        (Circuit.measurementCellsReference ctx dimension count Reference)).Index
  | 0, _ => Equiv.refl _
  | count + 1, Reference =>
      (Circuit.underRetainedSplitBasis
        (MeasurementCells.context ctx dimension count).canonicalFreshKey (.finite dimension)
        (MeasurementCells.context ctx dimension count).canonicalFreshKey_fresh Reference).trans
          (cellBasis count
            ((Circuit.measurementCellFrame ctx dimension count).register.prod Reference))

/-- Complete Store, hidden-state, and old-history coordinates are invertible. -/
def cellRecords (count : Nat) (Hidden H : Type) :
    (Store (MeasurementCells.context ctx dimension count) × (Hidden × H)) ≃
      (Store ctx × (Hidden × (Circuit.measurementCellsHistory ctx dimension count × H))) where
  toFun record :=
    let stored := cellStoreEquiv ctx dimension count record.1
    (stored.1, (record.2.1, (stored.2, record.2.2)))
  invFun record :=
    ((cellStoreEquiv ctx dimension count).symm (record.1, record.2.2.1),
      (record.2.1, record.2.2.2))
  left_inv record := by
    simpa only [Prod.mk.eta] using congrArg (fun stored => (stored, record.2))
      ((cellStoreEquiv ctx dimension count).symm_apply_apply record.1)
  right_inv record := by simp only [Equiv.apply_symm_apply]

private def cellHistoryAssoc (count : Nat) (Hidden H : Type) :
    (Hidden × (Circuit.measurementCellsHistory ctx dimension count ×
      (Store (Circuit.measurementCellFrame ctx dimension count) × H))) ≃
    (Hidden × ((Circuit.measurementCellsHistory ctx dimension count ×
      Store (Circuit.measurementCellFrame ctx dimension count)) × H)) where
  toFun record := (record.1, ((record.2.1, record.2.2.1), record.2.2.2))
  invFun record := (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The original split state retains every complete density block entry exactly. -/
lemma cellSplitState_entry (count : Nat)
    {Reference : Register} {Hidden H : Type} [Fintype Hidden] [Fintype H]
    (state : State (MeasurementCells.context ctx dimension count) Reference (Hidden × H))
    (label : Store ctx × (Hidden × (Circuit.measurementCellsHistory ctx dimension count × H)))
    (row column : (ctx.register.prod
      (Circuit.measurementCellsReference ctx dimension count Reference)).Index) :
    ((Circuit.underMeasurementCellsSplitState ctx dimension count state).block label).matrix
        row column =
      (state.block ((cellRecords ctx dimension count Hidden H).symm label)).matrix
        ((cellBasis ctx dimension count Reference).symm row)
        ((cellBasis ctx dimension count Reference).symm column) := by
  induction count generalizing Reference H with
  | zero =>
      have mapped : Circuit.underMeasurementCellsSplitState ctx dimension 0 state =
          state.mapClassical (cellRecords ctx dimension 0 Hidden H) := by
        unfold Circuit.underMeasurementCellsSplitState State.mapHistory
        exact ExecutionState.executionState_mapClassical_congr_decision state
          _ _ (fun _ => rfl) _ _
      rw [mapped, ExecutionState.coordinate_mapClassical_block]
      rfl
  | succ count ih =>
      let inner := MeasurementCells.context ctx dimension count
      let split : State inner
          ((Circuit.measurementCellFrame ctx dimension count).register.prod Reference)
          (Hidden × (Store (Circuit.measurementCellFrame ctx dimension count) × H)) :=
        Circuit.underRetainedSplitState inner.canonicalFreshKey (.finite dimension)
          inner.canonicalFreshKey_fresh state
      let prior := Circuit.underMeasurementCellsSplitState ctx dimension count split
      let labels := (Equiv.refl (Store ctx)).prodCongr
        (cellHistoryAssoc ctx dimension count Hidden H)
      have mapped : prior.mapHistory (cellHistoryAssoc ctx dimension count Hidden H) =
          prior.mapClassical labels := by
        unfold State.mapHistory
        exact ExecutionState.executionState_mapClassical_congr_decision prior
          _ labels (fun _ => rfl) _ _
      change ((prior.mapHistory (cellHistoryAssoc ctx dimension count Hidden H)).block label).matrix
        row column = _
      erw [mapped, ExecutionState.coordinate_mapClassical_block]
      erw [ih split (labels.symm label) row column]
      erw [Circuit.underRetainedSplitState_entry inner.canonicalFreshKey (.finite dimension)
        inner.canonicalFreshKey_fresh state]
      rfl

private def retainedPredicateWeight {Stored Hidden H Path : Type}
    (predicate : Stored → H → Prop) : Stored × (Hidden × (H × Path)) → ℂ :=
  fun record => if predicate record.1 record.2.2.1 then 1 else 0

private def splitPredicateWeight {Base Cells Stored Hidden H Path : Type}
    (recover : Base × Cells → Stored) (predicate : Stored → H → Prop) :
    Base × (Hidden × (Cells × (H × Path))) → ℂ :=
  fun record => if predicate (recover (record.1, record.2.2.1)) record.2.2.2.1 then 1 else 0

private def originalPredicateWeight {Base Cells Stored Hidden H Path : Type}
    (recover : Base × Cells → Stored) (predicate : Stored → H → Prop) :
    Base × (Hidden × ((Cells × H) × Path)) → ℂ :=
  fun record => if predicate (recover (record.1, record.2.2.1.1)) record.2.2.1.2 then 1 else 0

private lemma cellPredicateWeight_pullback (count : Nat) {Hidden H Path : Type}
    (predicate : Store (MeasurementCells.context ctx dimension count) → H → Prop) :
    (fun record : Store (MeasurementCells.context ctx dimension count) ×
        (Hidden × (H × Path)) =>
      splitPredicateWeight (cellStoreEquiv ctx dimension count).symm predicate
        (cellRecords ctx dimension count Hidden (H × Path) record)) =
      retainedPredicateWeight (Hidden := Hidden) (Path := Path) predicate := by
  funext record
  change (if predicate
    ((cellStoreEquiv ctx dimension count).symm (cellStoreEquiv ctx dimension count record.1))
    record.2.2.1 then (1 : ℂ) else 0) = _
  rw [Equiv.symm_apply_apply]
  rfl

private lemma splitPredicateWeight_history
    {Base Cells Stored Hidden H SourcePath TargetPath : Type}
    (recover : Base × Cells → Stored) (predicate : Stored → H → Prop)
    (transport : SourcePath → TargetPath) :
    (fun record : Base × (Hidden × ((Cells × H) × SourcePath)) =>
      splitPredicateWeight recover predicate
        (record.1, (record.2.1, (record.2.2.1.1,
          (record.2.2.1.2, transport record.2.2.2))))) =
      originalPredicateWeight (Hidden := Hidden) (Path := SourcePath) recover predicate := rfl

private lemma weightedEntry_transport
    {Actual Split Original : Type} [Fintype Actual] [Fintype Split] [Fintype Original]
    {ActualRegister SplitRegister : Register}
    (actual : ExecutionState Actual ActualRegister)
    (split : ExecutionState Split SplitRegister)
    (original : ExecutionState Original SplitRegister)
    (coordinates : Actual → Split) (history : Original → Split) (weight : Split → ℂ)
    (actualWeight : Actual → ℂ) (originalWeight : Original → ℂ)
    (row column : ActualRegister.Index) (left right : SplitRegister.Index)
    (coordinateEntry : ExecutionState.weightedMatrixEntry split weight left right =
      ExecutionState.weightedMatrixEntry actual
        (fun record => weight (coordinates record)) row column)
    (execution : split = original.mapClassical history)
    (actualPullback : (fun record => weight (coordinates record)) = actualWeight)
    (originalPullback : (fun record => weight (history record)) = originalWeight) :
    ExecutionState.weightedMatrixEntry actual actualWeight row column =
      ExecutionState.weightedMatrixEntry original originalWeight left right := by
  rw [← actualPullback, ← originalPullback]
  exact coordinateEntry.symm.trans
    ((congrArg (fun output => ExecutionState.weightedMatrixEntry output weight left right)
      execution).trans
      (@ExecutionState.weightedMatrixEntry_mapClassical _ _ _ _
        (Classical.decEq _) _ original history weight left right))

/-- Every arbitrary classical block weight transports through the exact cell coordinates. -/
lemma cellSplit_weightedMatrixEntry (count : Nat)
    {Reference : Register} {Hidden H : Type} [Fintype Hidden] [Fintype H]
    (state : State (MeasurementCells.context ctx dimension count) Reference (Hidden × H))
    (weight : (Store ctx ×
      (Hidden × (Circuit.measurementCellsHistory ctx dimension count × H))) → ℂ)
    (row column : ((MeasurementCells.context ctx dimension count).register.prod Reference).Index) :
    ExecutionState.weightedMatrixEntry
        (Circuit.underMeasurementCellsSplitState ctx dimension count state) weight
        (cellBasis ctx dimension count Reference row)
        (cellBasis ctx dimension count Reference column) =
      ExecutionState.weightedMatrixEntry state
        (fun record => weight (cellRecords ctx dimension count Hidden H record)) row column := by
  unfold ExecutionState.weightedMatrixEntry
  rw [← Equiv.sum_comp (cellRecords ctx dimension count Hidden H)]
  apply Finset.sum_congr rfl
  intro record _
  rw [cellSplitState_entry]
  simp only [Equiv.symm_apply_apply]

/-- Native placement preserves the complete weighted density on the original real paths. -/
lemma underCells_weighted_entry {model : ExecutionModel}
    {environment : model.Environment} (ctx : RuntimeCtx model.kind)
    (dimension : ℕ+) (code : Circuit model ctx ctx false) (count : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (MeasurementCells.context ctx dimension count) Reference (model.HiddenState × H))
    (predicate : Store (MeasurementCells.context ctx dimension count) → H → Prop)
    (row column : ((MeasurementCells.context ctx dimension count).register.prod Reference).Index) :
    ExecutionState.weightedMatrixEntry
        ((Circuit.embedMeasurementCells code dimension count).execute environment Reference state)
        (fun record => if predicate record.1 record.2.2.1 then 1 else 0) row column =
      ExecutionState.weightedMatrixEntry
        (code.execute environment (Circuit.measurementCellsReference ctx dimension count Reference)
          (Circuit.underMeasurementCellsSplitState ctx dimension count state))
        (fun record => if predicate
          ((cellStoreEquiv ctx dimension count).symm (record.1, record.2.2.1.1))
          record.2.2.1.2 then 1 else 0)
        (cellBasis ctx dimension count Reference row)
        (cellBasis ctx dimension count Reference column) := by
  classical
  let actual : State (MeasurementCells.context ctx dimension count) Reference
      (model.HiddenState ×
        (H × (Circuit.embedMeasurementCells code dimension count).Path)) :=
    (Circuit.embedMeasurementCells code dimension count).execute environment Reference state
  let original : State ctx (Circuit.measurementCellsReference ctx dimension count Reference)
      (model.HiddenState × (Circuit.measurementCellsHistory ctx dimension count × H) ×
        code.Path) :=
    code.execute environment (Circuit.measurementCellsReference ctx dimension count Reference)
      (Circuit.underMeasurementCellsSplitState ctx dimension count state)
  let history :
      (model.HiddenState × (Circuit.measurementCellsHistory ctx dimension count × H) ×
        code.Path) →
      (model.HiddenState × (Circuit.measurementCellsHistory ctx dimension count ×
        (H × (Circuit.embedMeasurementCells code dimension count).Path))) :=
    fun record => (record.1, (record.2.1.1, (record.2.1.2,
      Circuit.embedMeasurementCellsPathEquiv code dimension count record.2.2)))
  let weight : (Store ctx × (model.HiddenState ×
      (Circuit.measurementCellsHistory ctx dimension count ×
        (H × (Circuit.embedMeasurementCells code dimension count).Path)))) → ℂ :=
    splitPredicateWeight (cellStoreEquiv ctx dimension count).symm predicate
  let left := cellBasis ctx dimension count Reference row
  let right := cellBasis ctx dimension count Reference column
  have coordinates := cellSplit_weightedMatrixEntry ctx dimension count actual
    weight row column
  have execution : Circuit.underMeasurementCellsSplitState ctx dimension count actual =
      original.mapHistory history :=
    Circuit.embedMeasurementCells_execute ctx dimension code count environment state
  exact weightedEntry_transport actual
    (Circuit.underMeasurementCellsSplitState ctx dimension count actual) original
    (cellRecords ctx dimension count model.HiddenState
      (H × (Circuit.embedMeasurementCells code dimension count).Path))
    (fun record => (record.1, history record.2)) weight
    (retainedPredicateWeight (Hidden := model.HiddenState)
      (Path := (Circuit.embedMeasurementCells code dimension count).Path) predicate)
    (originalPredicateWeight (Hidden := model.HiddenState) (Path := code.Path)
      (cellStoreEquiv ctx dimension count).symm predicate)
    row column left right coordinates
    (execution.trans (by
      unfold State.mapHistory
      exact ExecutionState.executionState_mapClassical_congr_decision original
        _ _ (fun _ => rfl) _ _))
    (cellPredicateWeight_pullback ctx dimension count
      (Hidden := model.HiddenState) (H := H)
      (Path := (Circuit.embedMeasurementCells code dimension count).Path) predicate)
    (splitPredicateWeight_history (Hidden := model.HiddenState) (H := H)
      (SourcePath := code.Path)
      (TargetPath := (Circuit.embedMeasurementCells code dimension count).Path)
      (cellStoreEquiv ctx dimension count).symm predicate
      (Circuit.embedMeasurementCellsPathEquiv code dimension count))

/-- No quantum value changes when the actual classical-cell Stores are split. -/
lemma cellBasis_left (count : Nat) (Reference : Register)
    (input : ((MeasurementCells.context ctx dimension count).register.prod Reference).Index) :
    (cellBasis ctx dimension count Reference input).1 =
      (MeasurementCells.basisEquiv ctx dimension count).symm input.1 := by
  induction count generalizing Reference with
  | zero => rfl
  | succ count ih =>
      let first :
          ((MeasurementCells.context ctx dimension (count + 1)).register.prod Reference).Index ≃
            ((MeasurementCells.context ctx dimension count).register.prod
              ((Circuit.measurementCellFrame ctx dimension count).register.prod Reference)).Index :=
        Circuit.underRetainedSplitBasis
          (MeasurementCells.context ctx dimension count).canonicalFreshKey (.finite dimension)
          (MeasurementCells.context ctx dimension count).canonicalFreshKey_fresh Reference
      have firstLeft : (first input).1 = input.1 :=
        Circuit.underRetainedSplitBasis_left
          (MeasurementCells.context ctx dimension count).canonicalFreshKey (.finite dimension)
          (MeasurementCells.context ctx dimension count).canonicalFreshKey_fresh Reference input
      have prior := ih
        ((Circuit.measurementCellFrame ctx dimension count).register.prod Reference) (first input)
      dsimp only [Circuit.measurementCellFrame, Circuit.retainedLocalFrame] at firstLeft prior ⊢
      exact prior.trans
        (congrArg (MeasurementCells.basisEquiv ctx dimension count).symm firstLeft)

end

end Terminal
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Reference
