/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Base.Accounting.Context.Embedding.Construction
import all QuantumAlg.Core.Execution.Context.Embedding.Union
import all QuantumAlg.Core.Execution.Store.Ext
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Workspace.Basis
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Workspace.Placement
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Chronology of the actual retained Fourier cells

Only existing pure context/Store descriptors and the trace-valid read induction
are assembled. No circuit body, full stage matrix, PathWord or PathDensity
instrument theorem is imported.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Layout

noncomputable section

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement

abbrev bank (width : Nat) : RuntimeCtx .quantum := readyContext width 2

abbrev terminal (width m : Nat) : RuntimeCtx .quantum :=
  MeasurementCells.context (bank width) 2 (2 * m)

def bankPosition (width : Nat) (index : Fin 3) : Fin (bank width).systemCount :=
  ContextUnion.rightPosition (NumeratorMeasurement.context width)
    (indexedContext width (List.range 3) List.nodup_range)
    (indexedContext_disjoint width (List.range 3) List.nodup_range)
    (rangePosition width 3 index)

lemma bankPosition_wire (width : Nat) (index : Fin 3) :
    (bank width).quantumLayout.wire (bankPosition width index) =
      QuantumWire.mk (InPlaceControlled.frameWidth width + index.val) 2 := by
  rw [bankPosition, ContextUnion.contextUnion_right_wire, rangePosition_wire]

def position (width m : Nat) (index : Fin 3) : Fin (terminal width m).systemCount :=
  MeasurementCells.wireEquiv (bank width) 2 (2 * m) (bankPosition width index)

lemma position_wire (width m : Nat) (index : Fin 3) :
    (terminal width m).quantumLayout.wire (position width m index) =
      QuantumWire.mk (InPlaceControlled.frameWidth width + index.val) 2 := by
  rw [position, MeasurementCells.wireEquiv_preserved, bankPosition_wire]

lemma position_qubit (width m : Nat) (index : Fin 3) :
    ((terminal width m).quantumLayout.wire (position width m index)).dimension = 2 := by
  rw [position_wire]

def resultCell (width m : Nat) (index : Fin (2 * m)) :
    CWriteRef (terminal width m) (.finite 2) :=
  MeasurementCells.reference (bank width) 2 (2 * m) index

lemma resultCell_keys_injective (width m : Nat) :
    Function.Injective (fun index : Fin (2 * m) => (resultCell width m index).key) :=
  MeasurementCells.reference_key_injective (bank width) 2 (2 * m)

abbrev feeds (m : Nat) (previous current : Fin (2 * m)) : Prop :=
  previous.val < current.val ∧ previous.val / m = current.val / m

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Layout

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

noncomputable section

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private def cellEntries {kind : ProblemKind} (ctx : RuntimeCtx kind) (dimension : ℕ+) :
    Nat → List (RuntimeEntry kind)
  | 0 => []
  | count + 1 =>
      .storage (MeasurementCells.context ctx dimension count).canonicalFreshKey
        .retained (.finite dimension) :: cellEntries ctx dimension count

private lemma cellEntries_context {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (dimension : ℕ+) (count : Nat) :
    (MeasurementCells.context ctx dimension count).entries =
      cellEntries ctx dimension count ++ ctx.entries := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change RuntimeEntry.storage
        (MeasurementCells.context ctx dimension count).canonicalFreshKey
        .retained (.finite dimension) ::
          (MeasurementCells.context ctx dimension count).entries = _
      rw [ih]
      rfl

private lemma cellEntries_quantumWires {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (dimension : ℕ+) (count : Nat) :
    (cellEntries ctx dimension count).flatMap RuntimeEntry.quantumWires = [] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa only [cellEntries, List.flatMap_cons, RuntimeEntry.quantumWires,
        List.nil_append] using ih

private lemma cellEntries_keysNodup {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (dimension : ℕ+) (count : Nat) :
    ((cellEntries ctx dimension count).map RuntimeEntry.key).Nodup := by
  have distinct := (MeasurementCells.context ctx dimension count).keysNodup
  rw [cellEntries_context, List.map_append] at distinct
  exact distinct.of_append_left

def cellFrame {kind : ProblemKind} (ctx : RuntimeCtx kind) (dimension : ℕ+)
    (count : Nat) : RuntimeCtx kind :=
  RuntimeCtx.ofEntries (cellEntries ctx dimension count)
    (cellEntries_keysNodup ctx dimension count) (by
      rw [cellEntries_quantumWires]
      exact List.nodup_nil)

private lemma cellFrame_disjoint {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (dimension : ℕ+) (count : Nat) :
    RuntimeCtx.StorageDisjoint ctx (cellFrame ctx dimension count) := by
  apply (RuntimeCtx.storageDisjoint_iff_listDisjoint _ _).mpr
  constructor
  · have distinct := (MeasurementCells.context ctx dimension count).keysNodup
    rw [cellEntries_context, List.map_append] at distinct
    exact distinct.disjoint.symm
  · change List.Disjoint ctx.physicalIdx
      (((cellEntries ctx dimension count).flatMap RuntimeEntry.quantumWires).map
        QuantumWire.identity)
    rw [cellEntries_quantumWires, List.map_nil]
    simp

def cellsPlacement {kind : ProblemKind} (ctx : RuntimeCtx kind) (dimension : ℕ+)
    (count : Nat) : ContextEmbedding ctx (MeasurementCells.context ctx dimension count) where
  keys := Function.Embedding.refl _
  physical := Function.Embedding.refl _
  frame := cellFrame ctx dimension count
  separate := by
    simpa only [runtimeCtx_relabel_refl] using cellFrame_disjoint ctx dimension count
  covers := by
    change ((ctx.relabel _ _).entries ++ cellEntries ctx dimension count).Perm
      (MeasurementCells.context ctx dimension count).entries
    rw [runtimeCtx_relabel_refl, cellEntries_context]
    exact List.perm_append_comm

private def cellFrameReference {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (dimension : ℕ+) : (count : Nat) →
      Fin count → CStorageRef (cellFrame ctx dimension count) (.finite dimension)
  | 0, index => Fin.elim0 index
  | count + 1, index =>
      Fin.cases
        { key := (MeasurementCells.context ctx dimension count).canonicalFreshKey
          role := .retained
          slot := .here }
        (fun previous =>
          { key := (cellFrameReference ctx dimension count previous).key
            role := (cellFrameReference ctx dimension count previous).role
            slot := .there (cellFrameReference ctx dimension count previous).slot }) index

private lemma cellFrameReference_key {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (dimension : ℕ+) (count : Nat) (index : Fin count) :
    (cellFrameReference ctx dimension count index).key =
      (MeasurementCells.reference ctx dimension count index).key := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      refine Fin.cases rfl (fun previous => ?_) index
      exact ih previous

lemma cellsPlacement_read {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (dimension : ℕ+) (count : Nat)
    (stored : Store (MeasurementCells.context ctx dimension count)) (index : Fin count) :
    stored.read (.storage (MeasurementCells.reference ctx dimension count index).toCStorageRef) =
      ((cellsPlacement ctx dimension count).store stored).2.read
        (.storage (cellFrameReference ctx dimension count index)) := by
  let placement := cellsPlacement ctx dimension count
  have sameRef : placement.unionFrameInput
      (.storage (cellFrameReference ctx dimension count index)) =
        .storage (MeasurementCells.reference ctx dimension count index).toCStorageRef := by
    change CInputRef.storage _ = CInputRef.storage _
    apply congrArg CInputRef.storage
    apply CStorageRef.storageRef_eq_of_key
    change (cellFrameReference ctx dimension count index).key =
      (MeasurementCells.reference ctx dimension count index).key
    exact cellFrameReference_key ctx dimension count index
  rw [← sameRef]
  exact placement.split_frame_read stored
    (.storage (cellFrameReference ctx dimension count index))

def indexedPointPlacement (width : Nat) {count : Nat} (active : Fin count) :
    ContextEmbedding (MeasuredPointAddition.context width) (readyContext width count) where
  keys := storageMap width active
  physical := physicalMap width active
  frame := ambientContext width active
  separate := ambient_disjoint width active
  covers := framed_entries width active

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage

noncomputable section

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement Recovery.Point

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private abbrev Context (width m : Nat) := Recovery.Layout.terminal width m

def output (width m : Nat) (index : Fin (2 * m)) :
    CWriteRef (Context width m)
      (.finite ((Context width m).quantumLayout.wire (Recovery.Layout.position width m
        0)).dimension) :=
  by simpa only [Recovery.Layout.position_qubit] using Recovery.Layout.resultCell width m index

def retains (width m : Nat) (stored original : Store (Context width m)) : Prop :=
  let inner := indexedPointPlacement width (0 : Fin 2)
  let outer := cellsPlacement (readyContext width 2) 2 (2 * m)
  (inner.store (outer.store original).1).2 = (inner.store (outer.store stored).1).2 ∧
    (outer.store original).2 = (outer.store stored).2

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
namespace PointCoordinates.ReadoutRows

noncomputable section

open QuantumAlg QuantumAlg.Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private abbrev Interface (width m : Nat) := Recovery.Layout.terminal width m

def outcomeBit (width m : Nat)
    (outcome : Fin ((Interface width m).quantumLayout.wire
      (Recovery.Layout.position width m 0)).dimension) : Fin 2 :=
  Fin.cast (congrArg PNat.val (Recovery.Layout.position_qubit width m 0)) outcome

end

end PointCoordinates.ReadoutRows
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
namespace PointCoordinates.StageWord.PathWord.PathDensity

noncomputable section

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private abbrev Interface (width m : Nat) := Recovery.Layout.terminal width m

abbrev Branch (width m : Nat) :=
  Store (Interface width m) ×
    (Fin ((Interface width m).quantumLayout.wire
      (Recovery.Layout.position width m 0)).dimension × Store (MeasuredPointAddition.context width))

private def written (width m : Nat) (index : Fin (2 * m)) (branch : Branch width m) :
    Store (Interface width m) :=
  branch.1.write (output width m index) (.finite branch.2.1)

def traceValid (width m : Nat) :
    (count : Nat) → (Fin count → Fin (2 * m)) → (Fin count → Branch width m) →
      Store (Interface width m) → Store (Interface width m) → Prop
  | 0, _, _, original, final => original = final
  | count + 1, indices, path, original, final =>
      retains width m (path 0).1 original ∧
        traceValid width m count (Fin.tail indices) (Fin.tail path)
          (written width m (indices 0) (path 0)) final

end

end PointCoordinates.StageWord.PathWord.PathDensity
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
namespace PointCoordinates.StageWord.PathWord.PathDensity
namespace FeedbackReads

noncomputable section

open QuantumAlg QuantumAlg.Execution
open Recovery.Point
open Recovery.Stage.PointCoordinates.ReadoutRows

private abbrev Interface (width m : Nat) := Recovery.Layout.terminal width m

/-- The physical-dimension cast does not change the original retained cell key. -/
private lemma output_key (width m : Nat) (index : Fin (2 * m)) :
    (Recovery.Stage.output width m index).key = (Recovery.Layout.resultCell width m index).key := by
  have transport {first second : CShape} (same : first = second)
      (ref : CWriteRef (Recovery.Layout.terminal width m) second) :
      (Eq.mpr (congrArg (CWriteRef (Recovery.Layout.terminal width m)) same) ref).key =
        ref.key := by
    cases same
    rfl
  unfold Recovery.Stage.output
  exact transport (congrArg CShape.finite (Recovery.Layout.position_qubit width m 0))
    (Recovery.Layout.resultCell width m index)

/-- Same-key finite storage transports only its value along the dimension equality. -/
private lemma read_write_finite_cast {ctx : RuntimeCtx .quantum} (dimension : ℕ+)
    (sameDimension : dimension = 2) (stored : Store ctx)
    (output : CWriteRef ctx (.finite dimension)) (observed : CWriteRef ctx (.finite 2))
    (sameKey : output.key = observed.key) (outcome : Fin dimension) :
    (stored.write output (.finite outcome)).read (.storage observed.toCStorageRef) =
      .finite (Fin.cast (congrArg PNat.val sameDimension) outcome) := by
  subst dimension
  have refs : output.toCStorageRef = observed.toCStorageRef :=
    CStorageRef.storageRef_eq_of_key output.toCStorageRef observed.toCStorageRef sameKey
  simpa only [refs, Fin.cast_eq_self] using Store.read_write_same stored output (.finite outcome)

/-- An actual point call retains every real measurement-cell read in its full frame. -/
private lemma retains_resultCell (width m : Nat)
    (stored original : Store (Interface width m))
    (retained : Recovery.Stage.retains width m stored original) (index : Fin (2 * m)) :
    stored.read (.storage (Recovery.Layout.resultCell width m index).toCStorageRef) =
      original.read (.storage (Recovery.Layout.resultCell width m index).toCStorageRef) := by
  let outer := cellsPlacement (Recovery.Layout.bank width) 2 (2 * m)
  let observed := cellFrameReference (Recovery.Layout.bank width) 2 (2 * m) index
  have frameSame : (outer.store stored).2 = (outer.store original).2 := retained.2.symm
  calc
    _ = (outer.store stored).2.read (.storage observed) :=
      cellsPlacement_read (Recovery.Layout.bank width) 2 (2 * m) stored index
    _ = (outer.store original).2.read (.storage observed) :=
      congrArg (fun frame : Store outer.frame => frame.read (.storage observed)) frameSame
    _ = _ := (cellsPlacement_read (Recovery.Layout.bank width) 2 (2 * m) original index).symm

/-- The actual readout write stores precisely that branch's physical outcome bit. -/
private lemma written_resultCell_same (width m : Nat) (index : Fin (2 * m))
    (branch : Branch width m) :
    (written width m index branch).read
        (.storage (Recovery.Layout.resultCell width m index).toCStorageRef) =
      .finite (outcomeBit width m branch.2.1) := by
  exact read_write_finite_cast _ (Recovery.Layout.position_qubit width m 0)
    branch.1 (Recovery.Stage.output width m index) (Recovery.Layout.resultCell width m index)
    (output_key width m index) branch.2.1

/-- A later distinct stage writes its own real cell and preserves the earlier result. -/
private lemma written_resultCell_other (width m : Nat)
    (index observed : Fin (2 * m)) (different : index ≠ observed) (branch : Branch width m) :
    (written width m index branch).read
        (.storage (Recovery.Layout.resultCell width m observed).toCStorageRef) =
      branch.1.read (.storage (Recovery.Layout.resultCell width m observed).toCStorageRef) := by
  apply Store.read_write_other
  rw [output_key]
  exact fun same => different (Recovery.Layout.resultCell_keys_injective width m same)

/-- Before a chosen branch, a cell not written by earlier stages still has its input value. -/
private lemma traceValid_before_read (width m : Nat) (count : Nat)
    (indices : Fin count → Fin (2 * m)) (path : Fin count → Branch width m)
    (original final : Store (Interface width m))
    (valid : traceValid width m count indices path original final)
    (current : Fin count) (observed : Fin (2 * m))
    (avoids : ∀ earlier : Fin count, earlier.val < current.val → indices earlier ≠ observed) :
    (path current).1.read (.storage (Recovery.Layout.resultCell width m observed).toCStorageRef) =
      original.read (.storage (Recovery.Layout.resultCell width m observed).toCStorageRef) := by
  induction count generalizing original final with
  | zero => exact Fin.elim0 current
  | succ count ih =>
      obtain ⟨retained, tailValid⟩ := valid
      revert avoids
      refine Fin.cases ?_ (fun current => ?_) current
      · intro _
        exact retains_resultCell width m (path 0).1 original retained observed
      · intro avoids
        have tailAvoids : ∀ earlier : Fin count,
            earlier.val < current.val → (Fin.tail indices) earlier ≠ observed := by
          intro earlier bound
          exact avoids earlier.succ (Nat.succ_lt_succ bound)
        have headDifferent : indices 0 ≠ observed :=
          avoids 0 (Nat.zero_lt_succ current.val)
        exact (ih (Fin.tail indices) (Fin.tail path)
          (written width m (indices 0) (path 0)) final tailValid current tailAvoids).trans
          ((written_resultCell_other width m (indices 0) observed headDifferent (path 0)).trans
            (retains_resultCell width m (path 0).1 original retained observed))

/-- Every earlier actual outcome remains readable at each later legal stage on the same path. -/
lemma traceValid_previous_read (width m : Nat) (count : Nat)
    (indices : Fin count → Fin (2 * m)) (path : Fin count → Branch width m)
    (original final : Store (Interface width m))
    (valid : traceValid width m count indices path original final)
    (distinct : Function.Injective indices) (previous current : Fin count)
    (earlier : previous.val < current.val) :
    (path current).1.read
        (.storage (Recovery.Layout.resultCell width m (indices previous)).toCStorageRef) =
      .finite (outcomeBit width m (path previous).2.1) := by
  induction count generalizing original final with
  | zero => exact Fin.elim0 current
  | succ count ih =>
      obtain ⟨_, tailValid⟩ := valid
      revert previous earlier
      refine Fin.cases ?_ (fun current => ?_) current
      · intro previous earlier
        exact False.elim (Nat.not_lt_zero previous.val earlier)
      · intro previous
        refine Fin.cases ?_ (fun previous => ?_) previous
        · intro _
          have avoids : ∀ before : Fin count,
              before.val < current.val → (Fin.tail indices) before ≠ indices 0 := by
            intro before _ same
            have impossible : before.succ = (0 : Fin (count + 1)) := distinct same
            have values := congrArg Fin.val impossible
            exact Nat.succ_ne_zero before.val values
          exact (traceValid_before_read width m count (Fin.tail indices) (Fin.tail path)
            (written width m (indices 0) (path 0)) final tailValid current (indices 0)
            avoids).trans (written_resultCell_same width m (indices 0) (path 0))
        · intro earlier
          have tailDistinct : Function.Injective (Fin.tail indices) := by
            intro left right same
            exact Fin.succ_injective _ (distinct same)
          exact ih (Fin.tail indices) (Fin.tail path)
            (written width m (indices 0) (path 0)) final tailValid tailDistinct
            previous current (Nat.lt_of_succ_lt_succ earlier)

/-- The real feedback guard reads the historical bit already measured on the actual full path. -/
lemma full_trace_feedback_read (width m : Nat) (path : Fin (2 * m) → Branch width m)
    (original final : Store (Interface width m))
    (valid : traceValid width m (2 * m) id path original final)
    (previous current : Fin (2 * m)) (feeds : Recovery.Layout.feeds m previous current) :
    (path current).1.read (.storage (Recovery.Layout.resultCell width m previous).toCStorageRef) =
      .finite (outcomeBit width m (path previous).2.1) :=
  traceValid_previous_read width m (2 * m) id path original final valid
    Function.injective_id previous current feeds.1

end

end FeedbackReads
end PointCoordinates.StageWord.PathWord.PathDensity
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
