/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.BareStores
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Layout.Reference
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Terminal.CellCoordinates
import all QuantumAlg.Core.Execution.Store.WritePrefix

/-!
# Complete point Stores under the actual bare-terminal correspondence

The actual old indexed placement and new nested embeddings extract the same
complete point Store from the common Numerator Store. Every Numerator value,
including all dirty measurement cells, is arbitrary. Result-cell prefix writes
commute with the complete bare Store transport and leave this point projection
unchanged. No equality of the two intermediate complete caller Stores is used.
The projections below are mathematical coordinates, not erasure or packing
instructions. The original result-cell values remain in the complete Stores
and their existing history coordinates.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point.Store

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement

variable {kind : ProblemKind}

/-- Remove only the two unique quantum-entry markers from the complete point Store. -/
private def pointNumerator (width : Nat) :
    Store (MeasuredPointAddition.context width) ≃ Store (NumeratorMeasurement.context width) :=
  (Recovery.Point.Instrument.storeCoordinates width).trans (InPlaceControlled.storeCoordinates
    width)

private def pointStorage (width : Nat) {shape : CShape}
    (ref : CStorageRef (NumeratorMeasurement.context width) shape) :
    CStorageRef (MeasuredPointAddition.context width) shape :=
  ContextUnion.storageLeft (MeasuredPointAddition.selector_disjoint width)
    (ContextUnion.storageLeft (InPlaceControlled.control_disjoint width) ref)

private lemma union_split_left_read {left right : RuntimeCtx kind}
    (separate : RuntimeCtx.StorageDisjoint left right)
    (stored : Store (left.disjointUnion right separate)) {shape : CShape}
    (input : CInputRef left shape) :
    ((ContextUnion.storeEquiv separate stored).1).read input =
      stored.read (ContextUnion.inputLeft separate input) := by
  have same := ContextUnion.contextUnion_read_join_left separate
    (ContextUnion.storeEquiv separate stored).1
    (ContextUnion.storeEquiv separate stored).2 input
  change ((ContextUnion.storeEquiv separate).symm
    (ContextUnion.storeEquiv separate stored)).read
      (ContextUnion.inputLeft separate input) = _ at same
  rw [Equiv.symm_apply_apply] at same
  exact same.symm

private lemma pointNumerator_read (width : Nat)
    (stored : Store (MeasuredPointAddition.context width)) {shape : CShape}
    (ref : CStorageRef (NumeratorMeasurement.context width) shape) :
    (pointNumerator width stored).read (.storage ref) =
      stored.read (.storage (pointStorage width ref)) := by
  change (InPlaceControlled.storeCoordinates width
    (Recovery.Point.Instrument.storeCoordinates width stored)).read (.storage ref) = _
  change ((ContextUnion.storeEquiv (InPlaceControlled.control_disjoint width)
    (Recovery.Point.Instrument.storeCoordinates width stored)).1).read (.storage ref) = _
  rw [union_split_left_read]
  change ((ContextUnion.storeEquiv (MeasuredPointAddition.selector_disjoint width)
    stored).1).read
      (.storage (ContextUnion.storageLeft (InPlaceControlled.control_disjoint width) ref)) = _
  exact union_split_left_read (MeasuredPointAddition.selector_disjoint width) stored _

private lemma embedding_child_read {child caller : RuntimeCtx kind}
    (placement : ContextEmbedding child caller) (stored : Store caller)
    {shape : CShape} (input : CInputRef child shape) :
    ((placement.store stored).1).read input = stored.read (placement.input input) := by
  have same := placement.contextEmbedding_input_read
    (placement.store stored).1 (placement.store stored).2 input
  simpa only [Prod.mk.eta, Equiv.symm_apply_apply] using same.symm

/-- Every actual old active index extracts the same complete dirty point Store. -/
lemma indexedPointStore_numerator (width : Nat) {count : Nat} (active : Fin count)
    (stored : Store (readyContext width count)) :
    pointNumerator width (Recovery.Reference.Measured.pointStore width active stored).1 =
      BareStores.readyStore width count stored := by
  apply Store.store_eq_of_storage_reads
  intro shape ref
  rw [pointNumerator_read, BareStores.readyStore_read]
  change ((Recovery.Point.indexedPointPlacement width active).store stored).1.read
    (.storage (pointStorage width ref)) = _
  rw [embedding_child_read]
  apply congrArg stored.read
  change CInputRef.storage _ = CInputRef.storage _
  apply congrArg CInputRef.storage
  apply CStorageRef.storageRef_eq_of_key
  change storageMap width active ref.key = ref.key
  exact storageMap_original width active ref.key
    (List.mem_map.mpr ⟨.storage ref.key ref.role shape, ref.present, rfl⟩)

/-- The ready-Store transport identifies every old active call's full point input. -/
lemma indexedPointStore_ready_transport (width firstCount secondCount : Nat)
    (first : Fin firstCount) (second : Fin secondCount)
    (stored : Store (readyContext width firstCount)) :
    (Recovery.Reference.Measured.pointStore width second
      ((BareStores.readyStore width secondCount).symm
        (BareStores.readyStore width firstCount stored))).1 =
      (Recovery.Reference.Measured.pointStore width first stored).1 := by
  apply (pointNumerator width).injective
  rw [indexedPointStore_numerator, indexedPointStore_numerator, Equiv.apply_symm_apply]

/-- The original base permutation uses exactly the same complete point Store at each call. -/
lemma indexedPointStore_base_transport (width m : Nat) (active : Fin (2 * m))
    (stored : Store (Recovery.Layout.bank width)) :
    (Recovery.Reference.Measured.pointStore width active
      ((ContextPermutation.storeEquiv (Allocation.body_entries width (2 * m))).symm
        (BareStores.baseStore width m stored))).1 =
      ((Recovery.Point.indexedPointPlacement width (0 : Fin 2)).store stored).1 := by
  have returned : (ContextPermutation.storeEquiv (Allocation.body_entries width (2 * m))).symm
      (BareStores.baseStore width m stored) =
      (BareStores.readyStore width (2 * m)).symm (BareStores.readyStore width 2 stored) := by
    change (ContextPermutation.storeEquiv (Allocation.body_entries width (2 * m))).symm
      (ContextPermutation.storeEquiv (Allocation.body_entries width (2 * m)) _) = _
    exact Equiv.symm_apply_apply _ _
  rw [returned]
  exact indexedPointStore_ready_transport width 2 (2 * m) (0 : Fin 2) active stored

private def cellStorage (ctx : RuntimeCtx kind) (dimension : ℕ+) {shape : CShape}
    (ref : CStorageRef ctx shape) :
    (count : Nat) → CStorageRef (MeasurementCells.context ctx dimension count) shape
  | 0 => ref
  | count + 1 => (cellStorage ctx dimension ref count).underRetained
      (MeasurementCells.context ctx dimension count).canonicalFreshKey (.finite dimension)
      (MeasurementCells.context ctx dimension count).canonicalFreshKey_fresh

private lemma cellStorage_key (ctx : RuntimeCtx kind) (dimension : ℕ+) {shape : CShape}
    (ref : CStorageRef ctx shape) (count : Nat) :
    (cellStorage ctx dimension ref count).key = ref.key := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

private lemma cellStorage_input (ctx : RuntimeCtx kind) (dimension : ℕ+) {shape : CShape}
    (ref : CStorageRef ctx shape) (count : Nat) :
    MeasurementCells.liftInput dimension (.storage ref) count =
      .storage (cellStorage ctx dimension ref count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [MeasurementCells.liftInput, ih]
      rfl

/-- Mathematical old-cell projection; the untouched terminal Store stays an argument. -/
private def cellBase (ctx : RuntimeCtx kind) (dimension : ℕ+) : (count : Nat) →
    Store (MeasurementCells.context ctx dimension count) → Store ctx
  | 0, stored => stored
  | count + 1, stored => cellBase ctx dimension count ⟨stored.cells.2⟩

private lemma cellBase_read (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (stored : Store (MeasurementCells.context ctx dimension count)) {shape : CShape}
    (ref : CStorageRef ctx shape) :
    (cellBase ctx dimension count stored).read (.storage ref) =
      stored.read (.storage (cellStorage ctx dimension ref count)) := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih ⟨stored.cells.2⟩

private lemma cellsPlacement_base (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (stored : Store (MeasurementCells.context ctx dimension count)) :
    ((Recovery.Point.cellsPlacement ctx dimension count).store stored).1 =
      cellBase ctx dimension count stored := by
  apply Store.store_eq_of_storage_reads
  intro shape ref
  rw [embedding_child_read, cellBase_read]
  apply congrArg stored.read
  change CInputRef.storage _ = CInputRef.storage _
  apply congrArg CInputRef.storage
  apply CStorageRef.storageRef_eq_of_key
  change ref.key = (cellStorage ctx dimension ref count).key
  exact (cellStorage_key ctx dimension ref count).symm

private lemma retainedStore_base (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (stored : Store (MeasurementCells.context ctx dimension (count + 1))) :
    (Recovery.Reference.Terminal.retainedStoreEquiv ctx dimension count stored).1 =
      (⟨stored.cells.2⟩ : Store (MeasurementCells.context ctx dimension count)) := by
  apply Store.store_eq_of_storage_reads
  intro shape ref
  let same := Circuit.retainedLocalPermutation (MeasurementCells.context ctx dimension count)
    (MeasurementCells.context ctx dimension count).canonicalFreshKey (.finite dimension)
    (MeasurementCells.context ctx dimension count).canonicalFreshKey_fresh
  change ((ContextUnion.storeEquiv _
    ((ContextPermutation.storeEquiv same).symm stored)).1).read (.storage ref) = _
  rw [union_split_left_read]
  have mapped := ContextPermutation.store_read_input same
    ((ContextPermutation.storeEquiv same).symm stored) (ContextUnion.inputLeft _ (.storage ref))
  have source : ContextPermutation.input same (ContextUnion.inputLeft _ (.storage ref)) =
      .storage (ref.underRetained
        (MeasurementCells.context ctx dimension count).canonicalFreshKey (.finite dimension)
        (MeasurementCells.context ctx dimension count).canonicalFreshKey_fresh) := by
    change CInputRef.storage _ = CInputRef.storage _
    apply congrArg CInputRef.storage
    exact CStorageRef.storageRef_eq_of_key _ _ rfl
  change ((ContextPermutation.storeEquiv same)
    ((ContextPermutation.storeEquiv same).symm stored)).read
      (ContextPermutation.input same (ContextUnion.inputLeft _ (.storage ref))) = _ at mapped
  rw [Equiv.apply_symm_apply, source] at mapped
  exact mapped.symm

/-- The old interpreter's complete cell-history coordinates have this same old-cell projection. -/
lemma oldCellStore_base (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (stored : Store (MeasurementCells.context ctx dimension count)) :
    (Recovery.Reference.Terminal.cellStoreEquiv ctx dimension count stored).1 =
      ((Recovery.Point.cellsPlacement ctx dimension count).store stored).1 := by
  rw [cellsPlacement_base]
  induction count with
  | zero => rfl
  | succ count ih =>
      change (Recovery.Reference.Terminal.cellStoreEquiv ctx dimension count
        (Recovery.Reference.Terminal.retainedStoreEquiv ctx dimension count stored).1).1 = _
      rw [retainedStore_base]
      exact ih ⟨stored.cells.2⟩

private lemma cellBase_underCells {source target : RuntimeCtx kind}
    (base : Store source ≃ Store target) (dimension : ℕ+) (count : Nat)
    (stored : Store (MeasurementCells.context source dimension count)) :
    cellBase target dimension count (BareStores.underCells base dimension count stored) =
      base (cellBase source dimension count stored) := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih ⟨stored.cells.2⟩

/-- The exact complete old point Store seen below the real old terminal-cell history split. -/
def oldTerminalPointStore (modulus m : Nat) (active : Fin (2 * m))
    (stored : Store (ECDLP.Measured.exponentMeasurementContext modulus m)) :
    Store (MeasuredPointAddition.context modulus.size) :=
  (Recovery.Reference.Measured.pointStore modulus.size active
    ((ContextPermutation.storeEquiv (Allocation.body_entries modulus.size (2 * m))).symm
      (Recovery.Reference.Terminal.cellStoreEquiv (Allocation.after modulus.size (2 * m)) 2 (2 *
        m) stored).1)).1

/-- Complete point Store naturality for every actual old point call and every terminal value. -/
lemma terminal_pointStore (modulus m : Nat) (active : Fin (2 * m))
    (stored : Store (Recovery.Layout.terminal modulus.size m)) :
    oldTerminalPointStore modulus m active (BareStores.terminal modulus m stored) =
      Recovery.Layout.Reference.streamingPointStore modulus.size m stored := by
  have baseSame :
      (Recovery.Reference.Terminal.cellStoreEquiv (Allocation.after modulus.size (2 * m)) 2 (2 * m)
        (BareStores.terminal modulus m stored)).1 =
        BareStores.baseStore modulus.size m
          ((Recovery.Point.cellsPlacement (Recovery.Layout.bank modulus.size) 2 (2 * m)).store
            stored).1 := by
    change (Recovery.Reference.Terminal.cellStoreEquiv (Allocation.after modulus.size (2 * m)) 2
      (2 * m)
      (BareStores.underCells (BareStores.baseStore modulus.size m) 2 (2 * m) stored)).1 = _
    rw [oldCellStore_base, cellsPlacement_base, cellsPlacement_base]
    exact cellBase_underCells (BareStores.baseStore modulus.size m) 2 (2 * m) stored
  change (Recovery.Reference.Measured.pointStore modulus.size active
    ((ContextPermutation.storeEquiv (Allocation.body_entries modulus.size (2 * m))).symm _)).1 = _
  rw [baseSame]
  exact indexedPointStore_base_transport modulus.size m active _

private lemma cellBase_write_result (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (stored : Store (MeasurementCells.context ctx dimension count)) (index : Fin count)
    (value : ClassicalRegister dimension) :
    cellBase ctx dimension count
      (stored.write (MeasurementCells.reference ctx dimension count index) value) =
        cellBase ctx dimension count stored := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      refine Fin.cases rfl (fun previous => ?_) index
      exact ih ⟨stored.cells.2⟩ previous

/-- An actual early terminal write cannot change any of the complete point's classical cells. -/
lemma streamingPointStore_write_result (width m : Nat)
    (stored : Store (Recovery.Layout.terminal width m)) (index : Fin (2 * m))
    (value : ClassicalRegister 2) :
    Recovery.Layout.Reference.streamingPointStore width m
      (stored.write (Recovery.Layout.resultCell width m index) value) =
      Recovery.Layout.Reference.streamingPointStore width m stored := by
  change ((Recovery.Point.indexedPointPlacement width (0 : Fin 2)).store
    ((Recovery.Point.cellsPlacement (Recovery.Layout.bank width) 2 (2 * m)).store
      (stored.write (Recovery.Layout.resultCell width m index) value)).1).1 = _
  rw [cellsPlacement_base]
  change ((Recovery.Point.indexedPointPlacement width (0 : Fin 2)).store
    (cellBase (Recovery.Layout.bank width) 2 (2 * m)
      (stored.write (MeasurementCells.reference (Recovery.Layout.bank width) 2 (2 * m) index)
        value))).1 = _
  rw [cellBase_write_result, ← cellsPlacement_base]
  rfl

/-- Arbitrary ordered partial overwrites commute with the complete bare-terminal transport. -/
lemma terminal_writePrefix (modulus m n : Nat) (indices : Fin n → Fin (2 * m))
    (values : Fin n → ClassicalRegister 2) (stored : Store (Recovery.Layout.terminal
      modulus.size m))
    (count : Nat) (bounded : count ≤ n) :
    BareStores.terminal modulus m
      (Store.writePrefix (fun index => Recovery.Layout.resultCell modulus.size m (indices index))
        values stored count bounded) =
      Store.writePrefix
        (fun index => ECDLP.Measured.exponentMeasurementCells modulus m (indices index))
        values (BareStores.terminal modulus m stored) count bounded := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [Store.writePrefix, BareStores.terminal_write_result, ih, Store.writePrefix]

/-- No prefix length, repeated index or arbitrary written value affects the complete point input. -/
lemma streamingPointStore_writePrefix (width m n : Nat) (indices : Fin n → Fin (2 * m))
    (values : Fin n → ClassicalRegister 2) (stored : Store (Recovery.Layout.terminal width m))
    (count : Nat) (bounded : count ≤ n) :
    Recovery.Layout.Reference.streamingPointStore width m
      (Store.writePrefix (fun index => Recovery.Layout.resultCell width m (indices index))
        values stored count bounded) = Recovery.Layout.Reference.streamingPointStore width m
          stored := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [Store.writePrefix, streamingPointStore_write_result]
      exact ih (Nat.le_of_succ_le bounded)

/-- Deferred old terminal writes preserve the full point projection at arbitrary Stores. -/
lemma oldTerminalPointStore_writePrefix (modulus m n : Nat) (active : Fin (2 * m))
    (indices : Fin n → Fin (2 * m)) (values : Fin n → ClassicalRegister 2)
    (stored : Store (ECDLP.Measured.exponentMeasurementContext modulus m))
    (count : Nat) (bounded : count ≤ n) :
    oldTerminalPointStore modulus m active
      (Store.writePrefix
        (fun index => ECDLP.Measured.exponentMeasurementCells modulus m (indices index))
        values stored count bounded) = oldTerminalPointStore modulus m active stored := by
  obtain ⟨original, rfl⟩ := (BareStores.terminal modulus m).surjective stored
  rw [← terminal_writePrefix, terminal_pointStore, streamingPointStore_writePrefix,
    terminal_pointStore]

/-- Later new calls and old deferred-write calls use identical complete point Store arguments. -/
lemma terminal_pointStore_writePrefix (modulus m n : Nat) (active : Fin (2 * m))
    (indices : Fin n → Fin (2 * m)) (values : Fin n → ClassicalRegister 2)
    (stored : Store (Recovery.Layout.terminal modulus.size m)) (count : Nat) (bounded : count ≤ n) :
    oldTerminalPointStore modulus m active (BareStores.terminal modulus m stored) =
      Recovery.Layout.Reference.streamingPointStore modulus.size m
        (Store.writePrefix (fun index => Recovery.Layout.resultCell modulus.size m (indices index))
          values stored count bounded) := by
  rw [streamingPointStore_writePrefix]
  exact terminal_pointStore modulus m active stored

/-- The literal point kernels keep the same division outcome and full stored final label. -/
lemma pointKraus_terminal_writePrefix {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (m n : Nat) (active : Fin (2 * m)) (Reference : Register)
    (division : Store (MeasuredPointAddition.context p.size))
    (indices : Fin n → Fin (2 * m)) (values : Fin n → ClassicalRegister 2)
    (stored : Store (Recovery.Layout.terminal p.size m)) (count : Nat) (bounded : count ≤ n) :
    Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference division
      (oldTerminalPointStore p m active (BareStores.terminal p m stored)) =
      Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference division
        (Recovery.Layout.Reference.streamingPointStore p.size m
          (Store.writePrefix (fun index => Recovery.Layout.resultCell p.size m (indices index))
            values stored count bounded)) :=
  congrArg (Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
    division)
    (terminal_pointStore_writePrefix p m n active indices values stored count bounded)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point.Store
