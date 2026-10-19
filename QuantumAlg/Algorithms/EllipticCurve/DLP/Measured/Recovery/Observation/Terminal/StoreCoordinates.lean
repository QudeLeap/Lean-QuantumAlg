/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.BareStores
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Store.Ambient
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Terminal.CellCoordinates
import all QuantumAlg.Core.Execution.Context.Union.Store.Laws
import all QuantumAlg.Core.Execution.Store.Ext
import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Sum

/-!
# Complete instantaneous and final classical terminal coordinates

The actual recursive old cell split retains every finite result-cell Store.
Its history reads and writes agree with the original allocation indices. The
instantaneous coordinate map exposes the complete old ready Store and that
unchanged cell history; the real fixed stage retains the whole cell history.
Quantum-only ambient Stores have unique classical presence markers, while
their quantum data remain in the joint state and its external Reference.

The separate final coordinate map reverses each complete result block. It is
an invertible mathematical Store correspondence, not an executed permutation,
packing instruction or zero-cost implementation. Arbitrary dirty cells, zero
result width, complete borrowed classical frame data and older histories are
retained. No path-fiber equivalence, deferred-write execution equation, common
instrument, recovery, success or complete algorithm resource claim is made.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace TerminalStoreCoordinates

noncomputable section

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement

variable {kind : ProblemKind}

private lemma split_left_read {left right : RuntimeCtx kind}
    (separate : RuntimeCtx.StorageDisjoint left right)
    (stored : Store (left.disjointUnion right separate)) {shape : CShape}
    (input : CInputRef left shape) :
    ((ContextUnion.storeEquiv separate stored).1).read input =
      stored.read (ContextUnion.inputLeft separate input) := by
  have same := ContextUnion.contextUnion_read_join_left separate
    (ContextUnion.storeEquiv separate stored).1
    (ContextUnion.storeEquiv separate stored).2 input
  exact same.symm.trans (congrArg
    (fun joined : Store (left.disjointUnion right separate) =>
      joined.read (ContextUnion.inputLeft separate input))
    (ContextUnion.join_split_store separate stored))

private lemma split_right_read {left right : RuntimeCtx kind}
    (separate : RuntimeCtx.StorageDisjoint left right)
    (stored : Store (left.disjointUnion right separate)) {shape : CShape}
    (input : CInputRef right shape) :
    ((ContextUnion.storeEquiv separate stored).2).read input =
      stored.read (ContextUnion.inputRight separate input) := by
  have same := ContextUnion.contextUnion_read_join_right separate
    (ContextUnion.storeEquiv separate stored).1
    (ContextUnion.storeEquiv separate stored).2 input
  exact same.symm.trans (congrArg
    (fun joined : Store (left.disjointUnion right separate) =>
      joined.read (ContextUnion.inputRight separate input))
    (ContextUnion.join_split_store separate stored))

private lemma retained_tail (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (stored : Store (MeasurementCells.context ctx dimension (count + 1))) :
    (Recovery.Reference.Terminal.retainedStoreEquiv ctx dimension count stored).1 =
      (⟨stored.cells.2⟩ : Store (MeasurementCells.context ctx dimension count)) := by
  apply Store.store_eq_of_storage_reads
  intro shape input
  let same := Circuit.retainedLocalPermutation (MeasurementCells.context ctx dimension count)
    (MeasurementCells.context ctx dimension count).canonicalFreshKey (.finite dimension)
    (MeasurementCells.context ctx dimension count).canonicalFreshKey_fresh
  change ((ContextUnion.storeEquiv _
    ((ContextPermutation.storeEquiv same).symm stored)).1).read (.storage input) = _
  rw [split_left_read]
  have mapped := ContextPermutation.store_read_input same
    ((ContextPermutation.storeEquiv same).symm stored)
    (ContextUnion.inputLeft _ (.storage input))
  have source : ContextPermutation.input same (ContextUnion.inputLeft _ (.storage input)) =
      .storage (input.underRetained
        (MeasurementCells.context ctx dimension count).canonicalFreshKey (.finite dimension)
        (MeasurementCells.context ctx dimension count).canonicalFreshKey_fresh) := by
    change CInputRef.storage _ = CInputRef.storage _
    apply congrArg CInputRef.storage
    exact CStorageRef.storageRef_eq_of_key _ _ rfl
  have restored :
      ContextPermutation.store same ((ContextPermutation.storeEquiv same).symm stored) =
        stored :=
    (ContextPermutation.storeEquiv same).apply_symm_apply stored
  rw [restored, source] at mapped
  exact mapped.symm

private lemma retained_head (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (stored : Store (MeasurementCells.context ctx dimension (count + 1))) :
    (Recovery.Reference.Terminal.retainedStoreEquiv ctx dimension count stored).2 =
      (⟨(stored.cells.1, ())⟩ : Store (Circuit.measurementCellFrame ctx dimension count)) := by
  apply (BareStores.historyCellValue ctx dimension count).injective
  rw [BareStores.historyCellValue_read]
  let same := Circuit.retainedLocalPermutation (MeasurementCells.context ctx dimension count)
    (MeasurementCells.context ctx dimension count).canonicalFreshKey (.finite dimension)
    (MeasurementCells.context ctx dimension count).canonicalFreshKey_fresh
  change (((ContextUnion.storeEquiv _
    ((ContextPermutation.storeEquiv same).symm stored)).2).read
      (.storage (BareStores.historyCell ctx dimension count).toCStorageRef)).toFin =
        stored.cells.1.toFin
  rw [split_right_read]
  have mapped := ContextPermutation.store_read_input same
    ((ContextPermutation.storeEquiv same).symm stored)
    (ContextUnion.inputRight _
      (.storage (BareStores.historyCell ctx dimension count).toCStorageRef))
  have source : ContextPermutation.input same (ContextUnion.inputRight _
      (.storage (BareStores.historyCell ctx dimension count).toCStorageRef)) =
      .storage
        (⟨(MeasurementCells.context ctx dimension count).canonicalFreshKey, .retained, .here⟩ :
          CStorageRef (MeasurementCells.context ctx dimension (count + 1))
            (.finite dimension)) := by
    change CInputRef.storage _ = CInputRef.storage _
    apply congrArg CInputRef.storage
    exact CStorageRef.storageRef_eq_of_key _ _ rfl
  have restored :
      ContextPermutation.store same ((ContextPermutation.storeEquiv same).symm stored) =
        stored :=
    (ContextPermutation.storeEquiv same).apply_symm_apply stored
  rw [restored, source] at mapped
  exact congrArg CShape.Value.toFin mapped.symm

private lemma cellStore_succ (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (stored : Store (MeasurementCells.context ctx dimension (count + 1))) :
    Recovery.Reference.Terminal.cellStoreEquiv ctx dimension (count + 1) stored =
      ((Recovery.Reference.Terminal.cellStoreEquiv ctx dimension count ⟨stored.cells.2⟩).1,
        ((Recovery.Reference.Terminal.cellStoreEquiv ctx dimension count ⟨stored.cells.2⟩).2,
          (⟨(stored.cells.1, ())⟩ :
            Store (Circuit.measurementCellFrame ctx dimension count)))) := by
  change ((Recovery.Reference.Terminal.cellStoreEquiv ctx dimension count
      (Recovery.Reference.Terminal.retainedStoreEquiv ctx dimension count stored).1).1,
    ((Recovery.Reference.Terminal.cellStoreEquiv ctx dimension count
      (Recovery.Reference.Terminal.retainedStoreEquiv ctx dimension count stored).1).2,
        (Recovery.Reference.Terminal.retainedStoreEquiv ctx dimension count stored).2)) = _
  rw [retained_tail, retained_head]

/-- Every complete old history slot reads the actual result cell at its allocation index. -/
lemma cellStore_history_read (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (stored : Store (MeasurementCells.context ctx dimension count)) (index : Fin count) :
    BareStores.historyRead ctx dimension count
        (Recovery.Reference.Terminal.cellStoreEquiv ctx dimension count stored).2 index =
      (stored.read (.storage
        (MeasurementCells.reference ctx dimension count index).toCStorageRef)).toFin := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      rw [cellStore_succ]
      refine Fin.cases rfl (fun previous => ?_) index
      exact ih ⟨stored.cells.2⟩ previous

/-- The actual complete cell write updates precisely its original history Store slot. -/
lemma cellStore_write_result (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (stored : Store (MeasurementCells.context ctx dimension count)) (index : Fin count)
    (value : Fin dimension) :
    Recovery.Reference.Terminal.cellStoreEquiv ctx dimension count
        (stored.write (MeasurementCells.reference ctx dimension count index) (.finite value)) =
      ((Recovery.Reference.Terminal.cellStoreEquiv ctx dimension count stored).1,
        BareStores.historyWrite ctx dimension count
          (Recovery.Reference.Terminal.cellStoreEquiv ctx dimension count stored).2 index
            value) := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      refine Fin.cases ?_ (fun previous => ?_) index
      · rw [cellStore_succ, cellStore_succ]
        rfl
      · rw [cellStore_succ, cellStore_succ]
        exact congrArg (fun record : Store ctx ×
            Circuit.measurementCellsHistory ctx dimension count =>
          (record.1, (record.2,
            (⟨(stored.cells.1, ())⟩ :
              Store (Circuit.measurementCellFrame ctx dimension count)))))
          (ih ⟨stored.cells.2⟩ previous)

private lemma cellStore_underCells_base {source target : RuntimeCtx kind}
    (base : Store source ≃ Store target) (dimension : ℕ+) (count : Nat)
    (stored : Store (MeasurementCells.context source dimension count)) :
    (Recovery.Reference.Terminal.cellStoreEquiv target dimension count
      (BareStores.underCells base dimension count stored)).1 =
        base (Recovery.Reference.Terminal.cellStoreEquiv source dimension count stored).1 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [cellStore_succ, cellStore_succ]
      exact ih ⟨stored.cells.2⟩

/-- Complete cell splitting commutes with actual base transport and keeps every cell value. -/
lemma cellStore_underCells {source target : RuntimeCtx kind}
    (base : Store source ≃ Store target) (dimension : ℕ+) (count : Nat)
    (stored : Store (MeasurementCells.context source dimension count)) :
    Recovery.Reference.Terminal.cellStoreEquiv target dimension count
        (BareStores.underCells base dimension count stored) =
      (base (Recovery.Reference.Terminal.cellStoreEquiv source dimension count stored).1,
        BareStores.historyTransport source target dimension count
          (Recovery.Reference.Terminal.cellStoreEquiv source dimension count stored).2) := by
  apply Prod.ext
  · exact cellStore_underCells_base base dimension count stored
  · apply (BareStores.historyValues target dimension count).injective
    rw [BareStores.historyTransport_values]
    funext index
    rw [BareStores.historyValues_read, BareStores.historyValues_read,
      cellStore_history_read, cellStore_history_read]
    exact congrArg CShape.Value.toFin
      (BareStores.underCells_read_result base dimension count stored index)

private lemma cellFrame_eq_of_reads (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (first second : Store (Recovery.Point.cellFrame ctx dimension count))
    (same : ∀ index : Fin count,
      first.read (.storage (Recovery.Point.cellFrameReference ctx dimension count index)) =
        second.read (.storage (Recovery.Point.cellFrameReference ctx dimension count index))) :
    first = second := by
  induction count with
  | zero =>
      obtain ⟨first⟩ := first
      obtain ⟨second⟩ := second
      cases first
      cases second
      rfl
  | succ count ih =>
      apply congrArg Store.mk
      apply Prod.ext
      · exact same 0
      · exact congrArg Store.cells
          (ih ⟨first.cells.2⟩ ⟨second.cells.2⟩ (fun index => same index.succ))

/-- Equality of the actual full frame Store is exactly equality of all old cell histories. -/
lemma cellStore_history_eq_iff_frame (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (first second : Store (MeasurementCells.context ctx dimension count)) :
    (Recovery.Reference.Terminal.cellStoreEquiv ctx dimension count first).2 =
        (Recovery.Reference.Terminal.cellStoreEquiv ctx dimension count second).2 ↔
      ((Recovery.Point.cellsPlacement ctx dimension count).store first).2 =
        ((Recovery.Point.cellsPlacement ctx dimension count).store second).2 := by
  constructor
  · intro same
    apply cellFrame_eq_of_reads ctx dimension count
    intro index
    have reads :
        first.read (.storage
          (MeasurementCells.reference ctx dimension count index).toCStorageRef) =
        second.read (.storage
          (MeasurementCells.reference ctx dimension count index).toCStorageRef) := by
      apply (ClassicalRegister.finEquiv dimension).injective
      change (first.read (.storage
        (MeasurementCells.reference ctx dimension count index).toCStorageRef)).toFin =
          (second.read (.storage
            (MeasurementCells.reference ctx dimension count index).toCStorageRef)).toFin
      exact (cellStore_history_read ctx dimension count first index).symm.trans
        ((congrArg (fun history : Circuit.measurementCellsHistory ctx dimension count =>
          BareStores.historyRead ctx dimension count history index) same).trans
            (cellStore_history_read ctx dimension count second index))
    exact (Recovery.Point.cellsPlacement_read ctx dimension count first index).symm.trans
      (reads.trans (Recovery.Point.cellsPlacement_read ctx dimension count second index))
  · intro same
    apply (BareStores.historyValues ctx dimension count).injective
    funext index
    have frameRead := congrArg (fun framed : Store (Recovery.Point.cellFrame ctx dimension count) =>
      framed.read (.storage (Recovery.Point.cellFrameReference ctx dimension count index))) same
    have reads := (Recovery.Point.cellsPlacement_read ctx dimension count first index).trans
      (frameRead.trans (Recovery.Point.cellsPlacement_read ctx dimension count second index).symm)
    calc
      _ = BareStores.historyRead ctx dimension count
          (Recovery.Reference.Terminal.cellStoreEquiv ctx dimension count first).2 index :=
        BareStores.historyValues_read ctx dimension count _ index
      _ = (first.read (.storage
          (MeasurementCells.reference ctx dimension count index).toCStorageRef)).toFin :=
        cellStore_history_read ctx dimension count first index
      _ = (second.read (.storage
          (MeasurementCells.reference ctx dimension count index).toCStorageRef)).toFin :=
        congrArg CShape.Value.toFin reads
      _ = BareStores.historyRead ctx dimension count
          (Recovery.Reference.Terminal.cellStoreEquiv ctx dimension count second).2 index :=
        (cellStore_history_read ctx dimension count second index).symm
      _ = _ := (BareStores.historyValues_read ctx dimension count _ index).symm

/-- Instantaneous full Store coordinates: old ready Store and unchanged old cell history. -/
def instantStore (modulus m : Nat) :
    Store (Recovery.Layout.terminal modulus.size m) ≃
      (Store (readyContext modulus.size (2 * m)) ×
        Circuit.measurementCellsHistory (Allocation.after modulus.size (2 * m)) 2 (2 * m)) :=
  (BareStores.terminal modulus m).trans
    ((Recovery.Reference.Terminal.cellStoreEquiv (Allocation.after modulus.size (2 * m)) 2 (2 *
      m)).trans
      ((ContextPermutation.storeEquiv (Allocation.body_entries modulus.size (2 * m))).symm.prodCongr
        (Equiv.refl _)))

/-- The first coordinate is the complete actual old ready Store, before any final reversal. -/
lemma instantStore_ready (modulus m : Nat)
    (stored : Store (Recovery.Layout.terminal modulus.size m)) :
    (instantStore modulus m stored).1 =
      (ContextPermutation.storeEquiv (Allocation.body_entries modulus.size (2 * m))).symm
        (Recovery.Reference.Terminal.cellStoreEquiv (Allocation.after modulus.size (2 * m)) 2 (2
          * m)
          (BareStores.terminal modulus m stored)).1 := rfl

/-- The instantaneous history keeps every original dirty result value in the same slot. -/
lemma instantStore_history (modulus m : Nat)
    (stored : Store (Recovery.Layout.terminal modulus.size m)) :
    (instantStore modulus m stored).2 =
      BareStores.historyTransport (Recovery.Layout.bank modulus.size)
        (Allocation.after modulus.size (2 * m)) 2 (2 * m)
        (Recovery.Reference.Terminal.cellStoreEquiv (Recovery.Layout.bank modulus.size) 2 (2 *
          m) stored).2 :=
  congrArg Prod.snd (cellStore_underCells (BareStores.baseStore modulus.size m) 2 (2 * m) stored)

/-- Actual result-cell writes preserve the entire ready Store and update their full history. -/
lemma instantStore_write_result (modulus m : Nat)
    (stored : Store (Recovery.Layout.terminal modulus.size m)) (index : Fin (2 * m)) (value :
      Fin 2) :
    instantStore modulus m
        (stored.write (Recovery.Layout.resultCell modulus.size m index) (.finite value)) =
      ((instantStore modulus m stored).1,
        BareStores.historyWrite (Allocation.after modulus.size (2 * m)) 2 (2 * m)
          (instantStore modulus m stored).2 index value) := by
  let coordinates := fun record : Store (Allocation.after modulus.size (2 * m)) ×
      Circuit.measurementCellsHistory (Allocation.after modulus.size (2 * m)) 2 (2 * m) =>
    ((ContextPermutation.storeEquiv (Allocation.body_entries modulus.size (2 * m))).symm
      record.1, record.2)
  have moved := BareStores.terminal_write_result modulus m stored index (.finite value)
  have split := cellStore_write_result (Allocation.after modulus.size (2 * m)) 2 (2 * m)
    (BareStores.terminal modulus m stored) index value
  exact (congrArg (fun current :
      Store (MeasurementCells.context (Allocation.after modulus.size (2 * m)) 2 (2 * m)) =>
    coordinates (Recovery.Reference.Terminal.cellStoreEquiv (Allocation.after modulus.size (2 * m))
      2 (2 * m) current)) moved).trans (congrArg coordinates split)

private lemma write_finite_cast {ctx : RuntimeCtx .quantum} (dimension : ℕ+)
    (sameDimension : dimension = 2) (stored : Store ctx)
    (output : CWriteRef ctx (.finite dimension)) (observed : CWriteRef ctx (.finite 2))
    (sameKey : output.key = observed.key) (outcome : Fin dimension) :
    stored.write output (.finite outcome) =
      stored.write observed (.finite (Fin.cast (congrArg PNat.val sameDimension) outcome)) := by
  subst dimension
  have refs : output.toCStorageRef = observed.toCStorageRef :=
    CStorageRef.storageRef_eq_of_key output.toCStorageRef observed.toCStorageRef sameKey
  change (⟨Cells.write stored.cells output.toCStorageRef.slot (.finite outcome)⟩ : Store ctx) =
    ⟨Cells.write stored.cells observed.toCStorageRef.slot (.finite outcome)⟩
  rw [refs]

/-- The same coordinate law uses the actual physical readout destination and outcome cast. -/
lemma instantStore_write_output (modulus m : Nat)
    (stored : Store (Recovery.Layout.terminal modulus.size m)) (index : Fin (2 * m))
    (outcome : Fin ((Recovery.Layout.terminal modulus.size m).quantumLayout.wire
      (Recovery.Layout.position modulus.size m 0)).dimension) :
    instantStore modulus m
        (stored.write (Recovery.Stage.output modulus.size m index) (.finite outcome)) =
      ((instantStore modulus m stored).1,
        BareStores.historyWrite (Allocation.after modulus.size (2 * m)) 2 (2 * m)
          (instantStore modulus m stored).2 index
          (Recovery.Stage.PointCoordinates.ReadoutRows.outcomeBit modulus.size m outcome)) := by
  have sameKey :=
    Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity.FeedbackReads.output_key
      modulus.size m index
  rw [write_finite_cast _ (Recovery.Layout.position_qubit modulus.size m 0) stored
    (Recovery.Stage.output modulus.size m index) (Recovery.Layout.resultCell modulus.size m index)
    sameKey outcome]
  exact instantStore_write_result modulus m stored index _

/-- The real fixed stage retains the complete cell frame, expressed in instantaneous coordinates. -/
lemma fixed_retains_iff_history (modulus m : Nat)
    (stored original : Store (Recovery.Layout.terminal modulus.size m)) :
    Recovery.Stage.retains modulus.size m stored original ↔
      (instantStore modulus m original).2 = (instantStore modulus m stored).2 := by
  rw [Recovery.Point.Store.fixed_retains_iff_cells]
  change ((Recovery.Point.cellsPlacement (Recovery.Layout.bank modulus.size) 2 (2 * m)).store
    original).2 =
      ((Recovery.Point.cellsPlacement (Recovery.Layout.bank modulus.size) 2 (2 * m)).store
        stored).2 ↔ _
  rw [instantStore_history, instantStore_history]
  constructor
  · intro same
    exact congrArg
      (BareStores.historyTransport (Recovery.Layout.bank modulus.size)
        (Allocation.after modulus.size (2 * m)) 2 (2 * m))
      ((cellStore_history_eq_iff_frame (Recovery.Layout.bank modulus.size) 2 (2 * m)
        original stored).mpr same)
  · intro same
    exact (cellStore_history_eq_iff_frame (Recovery.Layout.bank modulus.size) 2 (2 * m)
      original stored).mp
      ((BareStores.historyTransport (Recovery.Layout.bank modulus.size)
        (Allocation.after modulus.size (2 * m)) 2 (2 * m)).injective same)

private def blocks (m : Nat) : Fin (2 * m) ≃ (Fin m ⊕ Fin m) :=
  (finCongr (Nat.two_mul m)).trans finSumFinEquiv.symm

/-- Reverse each result block independently without changing the first-then-second order. -/
def blockReverse (m : Nat) : Equiv.Perm (Fin (2 * m)) :=
  (blocks m).trans ((Equiv.sumCongr Fin.revPerm Fin.revPerm).trans (blocks m).symm)

/-- The first block uses exactly its reversed original allocation index. -/
lemma blockReverse_left (m : Nat) (index : Fin m) :
    blockReverse m (Fin.cast (Nat.two_mul m).symm (Fin.castAdd m index)) =
      Fin.cast (Nat.two_mul m).symm (Fin.castAdd m index.rev) := by
  simp [blockReverse, blocks]

/-- The second block uses exactly its reversed original allocation index. -/
lemma blockReverse_right (m : Nat) (index : Fin m) :
    blockReverse m (Fin.cast (Nat.two_mul m).symm (Fin.natAdd m index)) =
      Fin.cast (Nat.two_mul m).symm (Fin.natAdd m index.rev) := by
  change Fin.cast (Nat.two_mul m).symm
    (finSumFinEquiv (Sum.map Fin.rev Fin.rev (finSumFinEquiv.symm (Fin.natAdd m index)))) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

/-- The same full result-block reversal is its own inverse, including the empty case. -/
lemma blockReverse_involutive (m : Nat) : Function.Involutive (blockReverse m) := by
  intro index
  simp only [blockReverse, Equiv.trans_apply, Equiv.apply_symm_apply]
  cases same : blocks m index with
  | inl value =>
      simp only [Equiv.sumCongr_apply, Fin.revPerm_apply, Sum.map_inl, Fin.rev_rev]
      rw [← same, Equiv.symm_apply_apply]
  | inr value =>
      simp only [Equiv.sumCongr_apply, Fin.revPerm_apply, Sum.map_inr, Fin.rev_rev]
      rw [← same, Equiv.symm_apply_apply]

/-- Reindex the complete finite history, preserving every dirty value invertibly. -/
def reverseHistory (ctx : RuntimeCtx kind) (m : Nat) :
    Equiv.Perm (Circuit.measurementCellsHistory ctx 2 (2 * m)) :=
  (BareStores.historyValues ctx 2 (2 * m)).trans
    ((Equiv.arrowCongr (blockReverse m).symm (Equiv.refl (Fin 2))).trans
      (BareStores.historyValues ctx 2 (2 * m)).symm)

/-- Every reversed history read is the original full value at the reversed block position. -/
lemma reverseHistory_read (ctx : RuntimeCtx kind) (m : Nat)
    (history : Circuit.measurementCellsHistory ctx 2 (2 * m)) (index : Fin (2 * m)) :
    BareStores.historyRead ctx 2 (2 * m) (reverseHistory ctx m history) index =
      BareStores.historyRead ctx 2 (2 * m) history (blockReverse m index) := by
  rw [← BareStores.historyValues_read, ← BareStores.historyValues_read]
  change BareStores.historyValues ctx 2 (2 * m)
      ((BareStores.historyValues ctx 2 (2 * m)).symm
        (fun index => BareStores.historyValues ctx 2 (2 * m) history (blockReverse m index)))
      index = _
  rw [Equiv.apply_symm_apply]

/-- Final complete bare Store coordinates; this map is not an executed instruction. -/
def finalStore (modulus m : Nat) :
    Store (Recovery.Layout.terminal modulus.size m) ≃
      Store (ECDLP.Measured.exponentMeasurementContext modulus m) :=
  (BareStores.terminal modulus m).trans
    ((Recovery.Reference.Terminal.cellStoreEquiv (Allocation.after modulus.size (2 * m)) 2 (2 *
      m)).trans
      (((Equiv.refl _).prodCongr (reverseHistory (Allocation.after modulus.size (2 * m)) m)).trans
        (Recovery.Reference.Terminal.cellStoreEquiv (Allocation.after modulus.size (2 * m)) 2 (2
          * m)).symm))

/-- Final reversal changes only the complete cell history, leaving the base Store untouched. -/
lemma finalStore_coordinates (modulus m : Nat)
    (stored : Store (Recovery.Layout.terminal modulus.size m)) :
    Recovery.Reference.Terminal.cellStoreEquiv (Allocation.after modulus.size (2 * m)) 2 (2 * m)
        (finalStore modulus m stored) =
      ((Recovery.Reference.Terminal.cellStoreEquiv (Allocation.after modulus.size (2 * m)) 2 (2 * m)
          (BareStores.terminal modulus m stored)).1,
        reverseHistory (Allocation.after modulus.size (2 * m)) m
          (instantStore modulus m stored).2) :=
  (Recovery.Reference.Terminal.cellStoreEquiv (Allocation.after modulus.size (2 * m)) 2 (2 *
    m)).apply_symm_apply _

/-- The final old ready Store is exactly the instantaneous full ready Store. -/
lemma finalStore_ready (modulus m : Nat)
    (stored : Store (Recovery.Layout.terminal modulus.size m)) :
    (ContextPermutation.storeEquiv (Allocation.body_entries modulus.size (2 * m))).symm
      (Recovery.Reference.Terminal.cellStoreEquiv (Allocation.after modulus.size (2 * m)) 2 (2 * m)
        (finalStore modulus m stored)).1 = (instantStore modulus m stored).1 := by
  rw [finalStore_coordinates]
  rfl

/-- The complete final old result cell reads the corresponding reversed actual new cell. -/
lemma finalStore_read_result (modulus m : Nat)
    (stored : Store (Recovery.Layout.terminal modulus.size m)) (index : Fin (2 * m)) :
    (finalStore modulus m stored).read (.storage
        (ECDLP.Measured.exponentMeasurementCells modulus m index).toCStorageRef) =
      stored.read (.storage
        (Recovery.Layout.resultCell modulus.size m (blockReverse m index)).toCStorageRef) := by
  apply (ClassicalRegister.finEquiv 2).injective
  change ((finalStore modulus m stored).read (.storage
      (ECDLP.Measured.exponentMeasurementCells modulus m index).toCStorageRef)).toFin =
    (stored.read (.storage
      (Recovery.Layout.resultCell modulus.size m (blockReverse m index)).toCStorageRef)).toFin
  calc
    _ = BareStores.historyRead (Allocation.after modulus.size (2 * m)) 2 (2 * m)
        (Recovery.Reference.Terminal.cellStoreEquiv (Allocation.after modulus.size (2 * m)) 2 (2
          * m)
          (finalStore modulus m stored)).2 index :=
      (cellStore_history_read (Allocation.after modulus.size (2 * m)) 2 (2 * m)
        (finalStore modulus m stored) index).symm
    _ = BareStores.historyRead (Allocation.after modulus.size (2 * m)) 2 (2 * m)
        (instantStore modulus m stored).2 (blockReverse m index) :=
      (congrArg (fun record : Store (Allocation.after modulus.size (2 * m)) ×
          Circuit.measurementCellsHistory (Allocation.after modulus.size (2 * m)) 2 (2 * m) =>
        BareStores.historyRead (Allocation.after modulus.size (2 * m)) 2 (2 * m) record.2 index)
        (finalStore_coordinates modulus m stored)).trans
          (reverseHistory_read (Allocation.after modulus.size (2 * m)) m _ index)
    _ = _ := (cellStore_history_read (Allocation.after modulus.size (2 * m)) 2 (2 * m)
      (BareStores.terminal modulus m stored) (blockReverse m index)).trans
        (congrArg CShape.Value.toFin
          (BareStores.terminal_read_result modulus m stored (blockReverse m index)))

/-- Complete arbitrary borrowed frame, hidden state and earlier history remain unchanged data. -/
def finalRecords (modulus m : Nat) (frame : RuntimeCtx kind) (Hidden History : Type) :
    (Store (Recovery.Layout.terminal modulus.size m) × (Store frame × (Hidden × History))) ≃
      (Store (ECDLP.Measured.exponentMeasurementContext modulus m) ×
        (Store frame × (Hidden × History))) :=
  (finalStore modulus m).prodCongr (Equiv.refl _)

/-- No borrowed classical frame value, service tag or earlier history is discarded. -/
lemma finalRecords_frame_history (modulus m : Nat) (frame : RuntimeCtx kind)
    (Hidden History : Type)
    (record : Store (Recovery.Layout.terminal modulus.size m) × (Store frame × (Hidden ×
      History))) :
    (finalRecords modulus m frame Hidden History record).2 = record.2 := rfl

end

end TerminalStoreCoordinates
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
