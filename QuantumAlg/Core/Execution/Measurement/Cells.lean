/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Accounting.Space
public import QuantumAlg.Core.Execution.Circuit
public import QuantumAlg.Core.Base.Accounting.Context
public import Mathlib.Data.PNat.Notation

/-!
# Actual finite classical cells for measurement results

The construction allocates one retained classical cell per requested result.
Every cell has its own fresh storage key and a writable reference of exactly
the declared finite dimension. Allocation consists only of the existing
retain and sequential-composition instructions. Quantum wire identities,
dimensions, ordering, and the complete joint state are unaffected.

The vector input below is a structural collection of those actual cell
references. It introduces neither an additional runtime value nor an
uncharged conversion to a bit string.
-/

namespace QuantumAlg.Execution.MeasurementCells

variable {kind : ProblemKind}

/-- Extend the live context by exactly the requested number of finite cells. -/
@[implicit_reducible]
public def context (ctx : RuntimeCtx kind) (dimension : ℕ+) : Nat → RuntimeCtx kind
  | 0 => ctx
  | count + 1 =>
      (context ctx dimension count).addRetained
        (context ctx dimension count).canonicalFreshKey (.finite dimension)
        (context ctx dimension count).canonicalFreshKey_fresh

/-- The newest cell has index zero; all older cells retain their relative order. -/
@[implicit_reducible]
public def reference (ctx : RuntimeCtx kind) (dimension : ℕ+) :
    (count : Nat) → Fin count → CWriteRef (context ctx dimension count) (.finite dimension)
  | 0, index => Fin.elim0 index
  | count + 1, index =>
      Fin.cases
        (CWriteRef.retainedHead (context ctx dimension count)
          (context ctx dimension count).canonicalFreshKey (.finite dimension)
          (context ctx dimension count).canonicalFreshKey_fresh)
        (fun previous => (reference ctx dimension count previous).underRetained
          (context ctx dimension count).canonicalFreshKey (.finite dimension)
          (context ctx dimension count).canonicalFreshKey_fresh) index

/-- Read the actual cells in their indexed order using closed structural references. -/
def input (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat) :
    CInputRef (context ctx dimension count) (.fixedVector count (.finite dimension)) :=
  .fixedVector fun index => .storage (reference ctx dimension count index).toCStorageRef

/-- Existing writable storage keeps its identity underneath all new cells. -/
def liftWrite {ctx : RuntimeCtx kind} {shape : CShape} (dimension : ℕ+)
    (ref : CWriteRef ctx shape) :
    (count : Nat) → CWriteRef (context ctx dimension count) shape
  | 0 => ref
  | count + 1 =>
      (liftWrite dimension ref count).underRetained
        (context ctx dimension count).canonicalFreshKey (.finite dimension)
        (context ctx dimension count).canonicalFreshKey_fresh

/-- Allocate every cell through the single existing circuit interpreter. -/
@[implicit_reducible]
public def allocate {model : ExecutionModel} (ctx : RuntimeCtx model.kind) (dimension : ℕ+) :
    (count : Nat) → Circuit model ctx (context ctx dimension count)
  | 0 => .id ctx
  | count + 1 =>
      .seq (allocate (model := model) ctx dimension count)
        (.retain (context ctx dimension count)
          (context ctx dimension count).canonicalFreshKey (.finite dimension)
          (context ctx dimension count).canonicalFreshKey_fresh)

/-- The corresponding actual classical storage update initializes each new cell. -/
def pushStore {ctx : RuntimeCtx kind} (dimension : ℕ+) :
    (count : Nat) → Store ctx → Store (context ctx dimension count)
  | 0, store => store
  | count + 1, store =>
      (pushStore dimension count store).pushRetained
        (context ctx dimension count).canonicalFreshKey (.finite dimension)
        (context ctx dimension count).canonicalFreshKey_fresh

/-- No quantum wire is added, removed, reordered, or assigned a new dimension. -/
theorem context_quantumWires (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat) :
    (context ctx dimension count).quantumWires = ctx.quantumWires := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa only [context, RuntimeCtx.quantumWires_addRetained] using ih

/-- Classical allocation preserves the complete list of physical quantum identities. -/
theorem context_physicalIdx (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat) :
    (context ctx dimension count).physicalIdx = ctx.physicalIdx := by
  simp only [RuntimeCtx.physicalIdx, context_quantumWires]

/-- Every cell contributes its real finite encoding capacity to resident space. -/
theorem context_residentSpace (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat) :
    (context ctx dimension count).residentSpace =
      count • SpacePool.ofShape (.finite dimension) + ctx.residentSpace := by
  induction count with
  | zero => simp only [context, zero_nsmul, zero_add]
  | succ count ih =>
      rw [context, RuntimeCtx.residentSpace_addRetained, ih, succ_nsmul]
      ac_rfl

/-- The same retained cells also contribute to auxiliary space. -/
theorem context_auxiliarySpace (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat) :
    (context ctx dimension count).auxiliarySpace =
      count • SpacePool.ofShape (.finite dimension) + ctx.auxiliarySpace := by
  induction count with
  | zero => simp only [context, zero_nsmul, zero_add]
  | succ count ih =>
      rw [context, RuntimeCtx.auxiliarySpace_addRetained, ih, succ_nsmul]
      ac_rfl

/-- Retained cell allocation itself emits no native operation. -/
theorem allocate_eventTrace {model : ExecutionModel}
    (ctx : RuntimeCtx model.kind) (dimension : ℕ+) (count : Nat)
    (path : (allocate (model := model) ctx dimension count).Path) :
    (allocate (model := model) ctx dimension count).eventTrace path = [] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (allocate (model := model) ctx dimension count).eventTrace path.1 ++ [] = []
      rw [ih, List.append_nil]

/-- Cell allocation contributes no event duration, while still allocating real storage. -/
theorem allocate_depth {model : ExecutionModel}
    (ctx : RuntimeCtx model.kind) (dimension : ℕ+) (count : Nat)
    (duration : Resource.Event model → Nat)
    (path : (allocate (model := model) ctx dimension count).Path) :
    (allocate (model := model) ctx dimension count).depth duration path = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (allocate (model := model) ctx dimension count).depth duration path.1 + 0 = 0
      rw [ih, Nat.add_zero]

/-- Each newly allocated cell initially reads its declared finite zero encoding. -/
theorem read_pushStore_reference {ctx : RuntimeCtx kind} (dimension : ℕ+) (count : Nat)
    (store : Store ctx) (index : Fin count) :
    (pushStore dimension count store).read
      (.storage (reference ctx dimension count index).toCStorageRef) =
        CShape.initialValue (.finite dimension) := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      refine Fin.cases ?_ (fun previous => ?_) index
      · rfl
      · exact ih previous

/-- Allocation preserves every value in the older writable reference. -/
theorem read_pushStore_liftWrite {ctx : RuntimeCtx kind} {shape : CShape}
    (dimension : ℕ+) (count : Nat) (store : Store ctx) (ref : CWriteRef ctx shape) :
    (pushStore dimension count store).read
      (.storage (liftWrite dimension ref count).toCStorageRef) =
        store.read (.storage ref.toCStorageRef) := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

end QuantumAlg.Execution.MeasurementCells
