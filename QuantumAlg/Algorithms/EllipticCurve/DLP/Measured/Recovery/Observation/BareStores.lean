/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.History.Feedback
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Execution.Measurement.Cells.Inputs
import all QuantumAlg.Core.Execution.Measurement.Cells.State
import all QuantumAlg.Core.Execution.Context.Union.Store.Laws
import all QuantumAlg.Core.Execution.Context.Permutation.Store
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Preparation
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Terminal.Context
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Complete classical Stores of the two bare ECC sampling terminals

The concrete correspondence preserves every Numerator cell and every terminal finite-two
cell. Only the unique classical presence markers of the actual quantum-only indexed
entries change. The newest allocated result cell is index zero on both sides. No
physical measurement order, frequency reversal, quantum state or execution equality is
asserted here. Arbitrary initial cells, scratch values and zero result width are
included. The separate result-cell history correspondence retains each actual finite
cell Store and commutes with its actual indexed reads/writes.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.BareStores

noncomputable section

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind}

/-- Raw retained-head coordinates preserve the real nominal cell value. -/
private def headStore (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat) :
    Store (MeasurementCells.context ctx dimension (count + 1)) ≃
      (ClassicalRegister dimension × Store (MeasurementCells.context ctx dimension count)) where
  toFun stored := (stored.cells.1, ⟨stored.cells.2⟩)
  invFun stored := ⟨(stored.1, stored.2.cells)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Extend an existing complete Store equivalence by the same actual result cells. -/
def underCells {source target : RuntimeCtx kind} (base : Store source ≃ Store target)
    (dimension : ℕ+) : (count : Nat) →
    Store (MeasurementCells.context source dimension count) ≃
      Store (MeasurementCells.context target dimension count)
  | 0 => base
  | count + 1 =>
      (headStore source dimension count).trans
        (((Equiv.refl _).prodCongr (underCells base dimension count)).trans
          (headStore target dimension count).symm)

/-- Each actual result-cell read keeps the same allocation index and value. -/
lemma underCells_read_result {source target : RuntimeCtx kind}
    (base : Store source ≃ Store target) (dimension : ℕ+) (count : Nat)
    (stored : Store (MeasurementCells.context source dimension count)) (index : Fin count) :
    (underCells base dimension count stored).read
        (.storage (MeasurementCells.reference target dimension count index).toCStorageRef) =
      stored.read
        (.storage (MeasurementCells.reference source dimension count index).toCStorageRef) := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      refine Fin.cases ?_ (fun previous => ?_) index
      · rfl
      · exact ih ⟨stored.cells.2⟩ previous

/-- A real indexed result-cell write commutes with complete Store transport. -/
lemma underCells_write_result {source target : RuntimeCtx kind}
    (base : Store source ≃ Store target) (dimension : ℕ+) (count : Nat)
    (stored : Store (MeasurementCells.context source dimension count)) (index : Fin count)
    (value : ClassicalRegister dimension) :
    underCells base dimension count
        (stored.write (MeasurementCells.reference source dimension count index) value) =
      (underCells base dimension count stored).write
        (MeasurementCells.reference target dimension count index) value := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      refine Fin.cases ?_ (fun previous => ?_) index
      · rfl
      · exact congrArg
          (fun tail : Store (MeasurementCells.context target dimension count) =>
            (⟨(stored.cells.1, tail.cells)⟩ :
              Store (MeasurementCells.context target dimension (count + 1))))
          (ih ⟨stored.cells.2⟩ previous)

private lemma read_underRetained {ctx : RuntimeCtx kind} {shape : CShape}
    (key : StorageKey) (retainedShape : CShape) (fresh : key ∉ ctx.keys)
    (stored : Store (ctx.addRetained key retainedShape fresh)) (input : CInputRef ctx shape) :
    stored.read (input.underRetained key retainedShape fresh) =
      (⟨stored.cells.2⟩ : Store ctx).read input := by
  induction input with
  | storage ref => rfl
  | product first second firstIH secondIH =>
      exact congrArg₂ CShape.Value.product firstIH secondIH
  | fixedVector entries ih => exact congrArg CShape.Value.fixedVector (funext ih)
  | first input ih => exact congrArg CShape.Value.first ih
  | second input ih => exact congrArg CShape.Value.second ih
  | vectorGet input index ih => exact congrArg (fun value => value.get index) ih
  | bitsGet input index ih => exact congrArg (fun value => value.bitGet index) ih
  | wordBitGet input index ih => exact congrArg (fun value => value.wordBitGet index) ih

/-- Arbitrary structural older inputs keep their values below arbitrary new cells. -/
lemma underCells_read_input {source target : RuntimeCtx kind} {shape : CShape}
    (base : Store source ≃ Store target) (dimension : ℕ+)
    (first : CInputRef source shape) (second : CInputRef target shape)
    (reads : ∀ stored, (base stored).read second = stored.read first)
    (count : Nat) (stored : Store (MeasurementCells.context source dimension count)) :
    (underCells base dimension count stored).read
        (MeasurementCells.liftInput dimension second count) =
      stored.read (MeasurementCells.liftInput dimension first count) := by
  induction count with
  | zero => exact reads stored
  | succ count ih =>
      rw [MeasurementCells.liftInput, MeasurementCells.liftInput,
        read_underRetained, read_underRetained]
      exact ih ⟨stored.cells.2⟩

/-- An older actual writable cell changes without altering any result-cell value. -/
lemma underCells_write_input {source target : RuntimeCtx kind} {shape : CShape}
    (base : Store source ≃ Store target) (dimension : ℕ+)
    (first : CWriteRef source shape) (second : CWriteRef target shape)
    (writes : ∀ stored value, base (stored.write first value) = (base stored).write second value)
    (count : Nat) (stored : Store (MeasurementCells.context source dimension count))
    (value : CShape.Value shape) :
    underCells base dimension count
        (stored.write (MeasurementCells.liftWrite dimension first count) value) =
      (underCells base dimension count stored).write
        (MeasurementCells.liftWrite dimension second count) value := by
  induction count with
  | zero => exact writes stored value
  | succ count ih =>
      exact congrArg
        (fun tail : Store (MeasurementCells.context target dimension count) =>
          (⟨(stored.cells.1, tail.cells)⟩ :
            Store (MeasurementCells.context target dimension (count + 1))))
        (ih ⟨stored.cells.2⟩)

private lemma indexedCells_subsingleton (width : Nat) (indices : List Nat) :
    Subsingleton (Cells (indices.map (indexedEntry width))) := by
  induction indices with
  | nil => exact inferInstanceAs (Subsingleton Unit)
  | cons index tail ih =>
      let := ih
      exact inferInstanceAs (Subsingleton (Unit × Cells (tail.map (indexedEntry width))))

private def indexedCells (width : Nat) :
    (indices : List Nat) → Cells (indices.map (indexedEntry width))
  | [] => ()
  | _ :: tail => ((), indexedCells width tail)

private instance indexedStore_subsingleton (width : Nat) (indices : List Nat)
    (distinct : indices.Nodup) : Subsingleton (Store (indexedContext width indices distinct)) :=
  ⟨fun first second => by
    let := indexedCells_subsingleton width indices
    exact congrArg Store.mk (Subsingleton.elim first.cells second.cells)⟩

private def indexedStore (width count : Nat) :
    Store (indexedContext width (List.range (count + 1)) List.nodup_range) :=
  ⟨indexedCells width (List.range (count + 1))⟩

private def removeMarkers {α β : Type} [Subsingleton β] (marker : β) : α × β ≃ α where
  toFun := Prod.fst
  invFun first := (first, marker)
  left_inv _ := Prod.ext rfl (Subsingleton.elim _ _)
  right_inv _ := rfl

/-- Only actual owned-quantum entry markers disappear; the full Numerator Store stays. -/
def readyStore (width count : Nat) :
    Store (readyContext width count) ≃ Store (NumeratorMeasurement.context width) :=
  (ContextUnion.storeEquiv
    (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)).trans
      (removeMarkers (indexedStore width count))

/-- An actual Numerator operand in the supplied ready context. -/
def readyInput (width count : Nat) {shape : CShape}
    (input : CInputRef (NumeratorMeasurement.context width) shape) :
    CInputRef (readyContext width count) shape :=
  ContextUnion.inputLeft
    (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range) input

/-- An actual writable Numerator cell in the supplied ready context. -/
def readyWrite (width count : Nat) {shape : CShape}
    (output : CWriteRef (NumeratorMeasurement.context width) shape) :
    CWriteRef (readyContext width count) shape :=
  ContextUnion.writeLeft
    (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range) output

lemma readyStore_read (width count : Nat) (stored : Store (readyContext width count))
    {shape : CShape} (input : CInputRef (NumeratorMeasurement.context width) shape) :
    (readyStore width count stored).read input = stored.read (readyInput width count input) := by
  obtain ⟨original, rfl⟩ := (readyStore width count).symm.surjective stored
  rw [Equiv.apply_symm_apply]
  exact (ContextUnion.contextUnion_read_join_left
    (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)
    original (indexedStore width count) input).symm

lemma readyStore_symm_write (width count : Nat)
    (stored : Store (NumeratorMeasurement.context width))
    {shape : CShape} (output : CWriteRef (NumeratorMeasurement.context width) shape)
    (value : CShape.Value shape) :
    (readyStore width count).symm (stored.write output value) =
      ((readyStore width count).symm stored).write (readyWrite width count output) value :=
  (ContextUnion.contextUnion_write_join_left
    (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)
    stored (indexedStore width count) output value).symm

lemma readyStore_write (width count : Nat) (stored : Store (readyContext width count))
    {shape : CShape} (output : CWriteRef (NumeratorMeasurement.context width) shape)
    (value : CShape.Value shape) :
    readyStore width count (stored.write (readyWrite width count output) value) =
      (readyStore width count stored).write output value := by
  obtain ⟨original, rfl⟩ := (readyStore width count).symm.surjective stored
  rw [← readyStore_symm_write]
  simp only [Equiv.apply_symm_apply]

/-- All common cells agree before extending either side by terminal result cells. -/
def baseStore (width m : Nat) :
    Store (Recovery.Layout.bank width) ≃ Store (Allocation.after width (2 * m)) :=
  (readyStore width 2).trans ((readyStore width (2 * m)).symm.trans
    (ContextPermutation.storeEquiv (Allocation.body_entries width (2 * m))))

def oldBaseInput (width m : Nat) {shape : CShape}
    (input : CInputRef (NumeratorMeasurement.context width) shape) :
    CInputRef (Allocation.after width (2 * m)) shape :=
  ContextPermutation.input (Allocation.body_entries width (2 * m))
    (readyInput width (2 * m) input)

def oldBaseWrite (width m : Nat) {shape : CShape}
    (output : CWriteRef (NumeratorMeasurement.context width) shape) :
    CWriteRef (Allocation.after width (2 * m)) shape :=
  ContextPermutation.writable (Allocation.body_entries width (2 * m))
    (readyWrite width (2 * m) output)

lemma baseStore_read (width m : Nat) (stored : Store (Recovery.Layout.bank width))
    {shape : CShape} (input : CInputRef (NumeratorMeasurement.context width) shape) :
    (baseStore width m stored).read (oldBaseInput width m input) =
      stored.read (readyInput width 2 input) := by
  change (ContextPermutation.store (Allocation.body_entries width (2 * m))
    ((readyStore width (2 * m)).symm (readyStore width 2 stored))).read
      (ContextPermutation.input (Allocation.body_entries width (2 * m))
        (readyInput width (2 * m) input)) = _
  rw [ContextPermutation.store_read_input, ← readyStore_read, Equiv.apply_symm_apply,
    readyStore_read]

lemma baseStore_write (width m : Nat) (stored : Store (Recovery.Layout.bank width))
    {shape : CShape} (output : CWriteRef (NumeratorMeasurement.context width) shape)
    (value : CShape.Value shape) :
    baseStore width m (stored.write (readyWrite width 2 output) value) =
      (baseStore width m stored).write (oldBaseWrite width m output) value := by
  change ContextPermutation.store (Allocation.body_entries width (2 * m))
      ((readyStore width (2 * m)).symm
        (readyStore width 2 (stored.write (readyWrite width 2 output) value))) = _
  rw [readyStore_write, readyStore_symm_write, ContextPermutation.store_write]
  rfl

/-- The concrete bare-terminal full Store transport; no caller premise supplies this map. -/
def terminal (modulus m : Nat) :
    Store (Recovery.Layout.terminal modulus.size m) ≃
      Store (ECDLP.Measured.exponentMeasurementContext modulus m) :=
  underCells (baseStore modulus.size m) 2 (2 * m)

/-- Same allocation-index result cell, with no physical-order reversal. -/
lemma terminal_read_result (modulus m : Nat)
    (stored : Store (Recovery.Layout.terminal modulus.size m)) (index : Fin (2 * m)) :
    (terminal modulus m stored).read
        (.storage (ECDLP.Measured.exponentMeasurementCells modulus m index).toCStorageRef) =
      stored.read (.storage (Recovery.Layout.resultCell modulus.size m index).toCStorageRef) :=
  underCells_read_result (baseStore modulus.size m) 2 (2 * m) stored index

lemma terminal_write_result (modulus m : Nat)
    (stored : Store (Recovery.Layout.terminal modulus.size m)) (index : Fin (2 * m))
    (value : ClassicalRegister 2) :
    terminal modulus m (stored.write (Recovery.Layout.resultCell modulus.size m index) value) =
      (terminal modulus m stored).write
        (ECDLP.Measured.exponentMeasurementCells modulus m index) value :=
  underCells_write_result (baseStore modulus.size m) 2 (2 * m) stored index value

/-- Every structural Numerator read survives beneath all arbitrary terminal cells. -/
lemma terminal_read_numerator (modulus m : Nat)
    (stored : Store (Recovery.Layout.terminal modulus.size m)) {shape : CShape}
    (input : CInputRef (NumeratorMeasurement.context modulus.size) shape) :
    (terminal modulus m stored).read
        (MeasurementCells.liftInput 2 (oldBaseInput modulus.size m input) (2 * m)) =
      stored.read (MeasurementCells.liftInput 2 (readyInput modulus.size 2 input) (2 * m)) :=
  underCells_read_input (baseStore modulus.size m) 2
    (readyInput modulus.size 2 input) (oldBaseInput modulus.size m input)
    (fun original => baseStore_read modulus.size m original input) (2 * m) stored

/-- Every actual writable Numerator cell commutes with full terminal Store transport. -/
lemma terminal_write_numerator (modulus m : Nat)
    (stored : Store (Recovery.Layout.terminal modulus.size m)) {shape : CShape}
    (output : CWriteRef (NumeratorMeasurement.context modulus.size) shape)
    (value : CShape.Value shape) :
    terminal modulus m
        (stored.write
          (MeasurementCells.liftWrite 2 (readyWrite modulus.size 2 output) (2 * m)) value) =
      (terminal modulus m stored).write
        (MeasurementCells.liftWrite 2 (oldBaseWrite modulus.size m output) (2 * m)) value :=
  underCells_write_input (baseStore modulus.size m) 2
    (readyWrite modulus.size 2 output) (oldBaseWrite modulus.size m output)
    (fun original next => baseStore_write modulus.size m original output next) (2 * m) stored value

/-- Actual writable retained head of the existing one-cell history frame. -/
def historyCell (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat) :
    CWriteRef (Circuit.measurementCellFrame ctx dimension count) (.finite dimension) where
  toCStorageRef :=
    { key := (MeasurementCells.context ctx dimension count).canonicalFreshKey
      role := .retained
      slot := .here }
  writable := by intro equal; cases equal

/-- A one-cell history Store is its actual finite value plus a unique empty-tail marker. -/
def historyCellValue (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat) :
    Store (Circuit.measurementCellFrame ctx dimension count) ≃ Fin dimension where
  toFun stored := stored.cells.1.toFin
  invFun value := ⟨(.finite value, ())⟩
  left_inv stored := by
    obtain ⟨stored⟩ := stored
    obtain ⟨value, marker⟩ := stored
    cases value
    cases marker
    rfl
  right_inv _ := rfl

lemma historyCellValue_read (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (stored : Store (Circuit.measurementCellFrame ctx dimension count)) :
    historyCellValue ctx dimension count stored =
      (stored.read (.storage (historyCell ctx dimension count).toCStorageRef)).toFin := rfl

private def consValues (dimension : ℕ+) (count : Nat) :
    (Fin dimension × (Fin count → Fin dimension)) ≃ (Fin (count + 1) → Fin dimension) where
  toFun pair := Fin.cons pair.1 pair.2
  invFun values := (values 0, fun index => values index.succ)
  left_inv _ := rfl
  right_inv values := by
    funext index
    exact Fin.cases rfl (fun _ => rfl) index

/-- Complete real cell histories in newest-first allocation-index coordinates. -/
def historyValues (ctx : RuntimeCtx kind) (dimension : ℕ+) : (count : Nat) →
    Circuit.measurementCellsHistory ctx dimension count ≃ (Fin count → Fin dimension)
  | 0 =>
      { toFun := fun _ => Fin.elim0
        invFun := fun _ => ()
        left_inv := by intro value; cases value; rfl
        right_inv := by intro values; funext index; exact Fin.elim0 index }
  | count + 1 =>
      ((historyValues ctx dimension count).prodCongr (historyCellValue ctx dimension count)).trans
        ((Equiv.prodComm _ _).trans (consValues dimension count))

/-- Read the original finite Store in the indexed actual history slot. -/
def historyRead (ctx : RuntimeCtx kind) (dimension : ℕ+) : (count : Nat) →
    Circuit.measurementCellsHistory ctx dimension count → Fin count → Fin dimension
  | 0, _, index => Fin.elim0 index
  | count + 1, history, index =>
      Fin.cases
        ((history.2.read (.storage (historyCell ctx dimension count).toCStorageRef)).toFin)
        (fun previous => historyRead ctx dimension count history.1 previous) index

/-- Write the actual finite cell Store in one indexed history slot. -/
def historyWrite (ctx : RuntimeCtx kind) (dimension : ℕ+) : (count : Nat) →
    Circuit.measurementCellsHistory ctx dimension count → Fin count → Fin dimension →
      Circuit.measurementCellsHistory ctx dimension count
  | 0, _, index, _ => Fin.elim0 index
  | count + 1, history, index, value =>
      Fin.cases
        (history.1, history.2.write (historyCell ctx dimension count) (.finite value))
        (fun previous =>
          (historyWrite ctx dimension count history.1 previous value, history.2)) index

lemma historyValues_read (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (history : Circuit.measurementCellsHistory ctx dimension count) (index : Fin count) :
    historyValues ctx dimension count history index =
      historyRead ctx dimension count history index := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      refine Fin.cases rfl (fun previous => ?_) index
      exact ih history.1 previous

lemma historyValues_write (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (history : Circuit.measurementCellsHistory ctx dimension count) (index : Fin count)
    (value : Fin dimension) :
    historyValues ctx dimension count (historyWrite ctx dimension count history index value) =
      Function.update (historyValues ctx dimension count history) index value := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      refine Fin.cases ?_ (fun previous => ?_) index
      · funext observed
        refine Fin.cases ?_ (fun earlier => ?_) observed
        · change value =
            Function.update (historyValues ctx dimension (count + 1) history) 0 value 0
          exact (Function.update_self 0 value
            (historyValues ctx dimension (count + 1) history)).symm
        · change historyValues ctx dimension count history.1 earlier =
            Function.update (historyValues ctx dimension (count + 1) history) 0 value earlier.succ
          exact (Function.update_of_ne (Fin.succ_ne_zero earlier) value
            (historyValues ctx dimension (count + 1) history)).symm
      · funext observed
        refine Fin.cases ?_ (fun earlier => ?_) observed
        · change historyCellValue ctx dimension count history.2 =
            Function.update (historyValues ctx dimension (count + 1) history) previous.succ value 0
          exact (Function.update_of_ne (Ne.symm (Fin.succ_ne_zero previous)) value
            (historyValues ctx dimension (count + 1) history)).symm
        · change historyValues ctx dimension count
              (historyWrite ctx dimension count history.1 previous value) earlier =
            Function.update (historyValues ctx dimension (count + 1) history)
              previous.succ value earlier.succ
          have tailEquality := congrFun (ih history.1 previous) earlier
          by_cases same : earlier = previous
          · subst earlier
            exact (tailEquality.trans (Function.update_self previous value
              (historyValues ctx dimension count history.1))).trans
                (Function.update_self previous.succ value
                  (historyValues ctx dimension (count + 1) history)).symm
          · have distinct : earlier.succ ≠ previous.succ :=
              fun equality => same (Fin.succ_injective count equality)
            have tailValue : historyValues ctx dimension count history.1 earlier =
                historyValues ctx dimension (count + 1) history earlier.succ := rfl
            exact ((tailEquality.trans (Function.update_of_ne same value
              (historyValues ctx dimension count history.1))).trans tailValue).trans
                (Function.update_of_ne distinct value
                  (historyValues ctx dimension (count + 1) history)).symm

/-- Real histories across different base contexts retain all and only their same indexed values. -/
def historyTransport (source target : RuntimeCtx kind) (dimension : ℕ+) (count : Nat) :
    Circuit.measurementCellsHistory source dimension count ≃
      Circuit.measurementCellsHistory target dimension count :=
  (historyValues source dimension count).trans (historyValues target dimension count).symm

lemma historyTransport_values (source target : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (history : Circuit.measurementCellsHistory source dimension count) :
    historyValues target dimension count (historyTransport source target dimension count history) =
      historyValues source dimension count history :=
  (historyValues target dimension count).apply_symm_apply _

lemma historyTransport_read (source target : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (history : Circuit.measurementCellsHistory source dimension count) (index : Fin count) :
    historyRead target dimension count
        (historyTransport source target dimension count history) index =
      historyRead source dimension count history index := by
  rw [← historyValues_read, ← historyValues_read, historyTransport_values]

lemma historyTransport_write (source target : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (history : Circuit.measurementCellsHistory source dimension count) (index : Fin count)
    (value : Fin dimension) :
    historyTransport source target dimension count
        (historyWrite source dimension count history index value) =
      historyWrite target dimension count
        (historyTransport source target dimension count history) index value := by
  apply (historyValues target dimension count).injective
  rw [historyTransport_values, historyValues_write, historyValues_write, historyTransport_values]

/-- Bare new and old result-cell histories have the same actual allocation-index values. -/
def terminalHistory (modulus m : Nat) :
    Circuit.measurementCellsHistory (Recovery.Layout.bank modulus.size) 2 (2 * m) ≃
      Circuit.measurementCellsHistory (Allocation.after modulus.size (2 * m)) 2 (2 * m) :=
  historyTransport _ _ 2 (2 * m)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.BareStores
