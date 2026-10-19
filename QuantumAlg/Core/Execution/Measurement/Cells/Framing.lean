/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Cells

/-!
# Allocate the original measurement cells beside a resident frame

The caller supplies a frame disjoint from the complete original allocation.
The actual retains use the original allocation keys, so adding the frame does
not change which cells later measurements name. Every frame entry remains live.
-/

namespace QuantumAlg.Execution.MeasurementCells

variable {kind : ProblemKind}

private lemma retained_disjoint {ctx frame : RuntimeCtx kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (separate : RuntimeCtx.StorageDisjoint (ctx.addRetained key shape fresh) frame) :
    RuntimeCtx.StorageDisjoint ctx frame := by
  constructor
  · apply (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mpr
    have keys := (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mp separate.1
    change List.Disjoint (key :: ctx.keys) frame.keys at keys
    exact List.disjoint_left.mpr fun _ present other =>
      List.disjoint_left.mp keys (List.mem_cons_of_mem _ present) other
  · exact separate.2

/-- Every original prefix remains disjoint from the entire resident frame. -/
lemma original_disjoint (ctx frame : RuntimeCtx kind) (dimension : ℕ+) :
    (count : Nat) → RuntimeCtx.StorageDisjoint (context ctx dimension count) frame →
      RuntimeCtx.StorageDisjoint ctx frame
  | 0, separate => separate
  | count + 1, separate =>
      original_disjoint ctx frame dimension count
        (retained_disjoint (context ctx dimension count).canonicalFreshKey (.finite dimension)
          (context ctx dimension count).canonicalFreshKey_fresh separate)

private lemma retained_fresh_union {ctx frame : RuntimeCtx kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (separate : RuntimeCtx.StorageDisjoint (ctx.addRetained key shape fresh) frame) :
    key ∉ (ctx.disjointUnion frame (retained_disjoint key shape fresh separate)).keys := by
  rw [RuntimeCtx.keys_disjointUnion]
  intro present
  rcases List.mem_append.mp present with original | framed
  · exact fresh original
  · have keys := (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mp separate.1
    change List.Disjoint (key :: ctx.keys) frame.keys at keys
    exact List.disjoint_left.mp keys List.mem_cons_self framed

/-- Emit the same original retained allocations with the entire frame physically present. -/
def allocateFramed {model : ExecutionModel} (ctx frame : RuntimeCtx model.kind) (dimension : ℕ+) :
    (count : Nat) → (separate : RuntimeCtx.StorageDisjoint (context ctx dimension count) frame) →
      Circuit model (ctx.disjointUnion frame
        (original_disjoint ctx frame dimension count separate))
        ((context ctx dimension count).disjointUnion frame separate)
  | 0, separate => .id (ctx.disjointUnion frame separate)
  | count + 1, separate =>
      let middle := context ctx dimension count
      let prefixSeparate := retained_disjoint middle.canonicalFreshKey (.finite dimension)
        middle.canonicalFreshKey_fresh separate
      .seq (allocateFramed (model := model) ctx frame dimension count prefixSeparate)
        (.retain (middle.disjointUnion frame prefixSeparate)
          middle.canonicalFreshKey (.finite dimension)
          (retained_fresh_union middle.canonicalFreshKey (.finite dimension)
            middle.canonicalFreshKey_fresh separate))

/-- Actual retained allocations emit no native event, while their cells remain resident. -/
lemma allocateFramed_eventTrace {model : ExecutionModel}
    (ctx frame : RuntimeCtx model.kind) (dimension : ℕ+)
    (count : Nat) (separate : RuntimeCtx.StorageDisjoint (context ctx dimension count) frame)
    (path : (allocateFramed (model := model) ctx frame dimension count separate).Path) :
    (allocateFramed (model := model) ctx frame dimension count separate).eventTrace path = [] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (allocateFramed ctx frame dimension count _).eventTrace path.1 ++ [] = []
      rw [ih, List.nil_append]

/-- The same literal retained prefix has zero evaluated event depth for every duration map. -/
lemma allocateFramed_depth {model : ExecutionModel}
    (ctx frame : RuntimeCtx model.kind) (dimension : ℕ+)
    (count : Nat) (separate : RuntimeCtx.StorageDisjoint (context ctx dimension count) frame)
    (duration : Resource.Event model → Nat)
    (path : (allocateFramed (model := model) ctx frame dimension count separate).Path) :
    (allocateFramed (model := model) ctx frame dimension count separate).depth
      duration path = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (allocateFramed ctx frame dimension count _).depth duration path.1 + 0 = 0
      rw [ih, Nat.add_zero]

end QuantumAlg.Execution.MeasurementCells
