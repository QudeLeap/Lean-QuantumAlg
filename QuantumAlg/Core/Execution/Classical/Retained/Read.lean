/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Classical.Retained.Cells
public import QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Execution.Classical.Retained.Cells
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Execution.Borrowed.Classical

/-!
# Borrowed reads under actual heterogeneous retained allocations

Each `RetainedCells.pushStore` step adds its canonical initial value at a new
head. A lifted structural input still reads exactly the original Store value.
This is generic in the shapes and input; it does not unfold a P-256 bank.
-/

namespace QuantumAlg.Execution.Store

/-- An original structural operand reads the old store beneath a retained head. -/
lemma retainedTail_read {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (store : Store (ctx.addRetained key shape fresh)) {inputShape : CShape}
    (input : CInputRef ctx inputShape) :
    (Store.mk store.cells.2).read input =
      store.read (input.underRetained key shape fresh) := by
  induction input with
  | storage => rfl
  | product first second firstIH secondIH =>
      exact congrArg₂ CShape.Value.product firstIH secondIH
  | fixedVector entries entriesIH =>
      exact congrArg CShape.Value.fixedVector (funext entriesIH)
  | first source sourceIH => exact congrArg CShape.Value.first sourceIH
  | second source sourceIH => exact congrArg CShape.Value.second sourceIH
  | vectorGet source index sourceIH => exact congrArg (fun value => value.get index) sourceIH
  | bitsGet source index sourceIH => exact congrArg (fun value => value.bitGet index) sourceIH
  | wordBitGet source index sourceIH =>
      exact congrArg (fun value => value.wordBitGet index) sourceIH

end QuantumAlg.Execution.Store

namespace QuantumAlg.CInputRef

private lemma mapStorage_underRetained {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (input : CInputRef ctx shape)
    (key : StorageKey) (retainedShape : CShape) (fresh : key ∉ ctx.keys) :
    mapStorage (fun ref => ref.underRetained key retainedShape fresh) input =
      input.underRetained key retainedShape fresh := by
  induction input with
  | storage ref => rfl
  | product left right leftIH rightIH => exact congrArg₂ product leftIH rightIH
  | fixedVector entries entriesIH => exact congrArg fixedVector (funext entriesIH)
  | first input ih => exact congrArg first ih
  | second input ih => exact congrArg second ih
  | vectorGet input index ih => exact congrArg (fun source => vectorGet source index) ih
  | bitsGet input index ih => exact congrArg (fun source => bitsGet source index) ih
  | wordBitGet input index ih => exact congrArg (fun source => wordBitGet source index) ih

end QuantumAlg.CInputRef

namespace QuantumAlg.Execution.RetainedCells

noncomputable section

private lemma transport_liftInput_cons {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (head : CShape) (tail : List CShape)
    {shape : CShape} (input : CInputRef ctx shape) :
    (transport ctx (head :: tail)).liftInput input =
      ((transport ctx tail).liftInput input).underRetained
        (context ctx tail).canonicalFreshKey head
        (context ctx tail).canonicalFreshKey_fresh := by
  calc
    _ = CInputRef.mapStorage
          (fun ref => ((transport ctx tail).liftStorage ref).underRetained
            (context ctx tail).canonicalFreshKey head
            (context ctx tail).canonicalFreshKey_fresh) input := rfl
    _ = CInputRef.mapStorage
          (fun ref => ref.underRetained
            (context ctx tail).canonicalFreshKey head
            (context ctx tail).canonicalFreshKey_fresh)
          ((transport ctx tail).liftInput input) :=
      CInputRef.input_mapStorage_compose
        (fun {shape} (ref : CStorageRef ctx shape) =>
          (transport ctx tail).liftStorage ref)
        (fun {shape} (ref : CStorageRef (context ctx tail) shape) =>
          ref.underRetained
            (context ctx tail).canonicalFreshKey head
            (context ctx tail).canonicalFreshKey_fresh)
        input
    _ = _ := CInputRef.mapStorage_underRetained _ _ _ _

/-- Retaining heterogeneous cells preserves every actual borrowed input read. -/
public lemma pushStore_read_liftInput {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (shapes : List CShape) (store : Store ctx)
    {shape : CShape} (input : CInputRef ctx shape) :
    (pushStore ctx shapes store).read ((transport ctx shapes).liftInput input) =
      store.read input := by
  induction shapes with
  | nil =>
      simpa only [pushStore, transport] using
        congrArg (store.read) (ClassicalWorkspace.Transport.liftInput_id input)
  | cons head tail ih =>
      rw [transport_liftInput_cons]
      exact (Store.read_pushRetained_underRetained
        (pushStore ctx tail store)
        (context ctx tail).canonicalFreshKey head
        (context ctx tail).canonicalFreshKey_fresh
        ((transport ctx tail).liftInput input)).trans ih

/-- Each retained reference reads the canonical initial value of its own shape. -/
public def Cells.Initialized {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shapes : List CShape} (cells : Cells ctx shapes)
    (store : Store ctx) : Prop :=
  match cells with
  | .nil => True
  | .cons head tail =>
      store.read (.storage head.ref.toCStorageRef) = CShape.initialValue _ ∧
        Cells.Initialized tail store

public lemma Cells.Initialized.underRetained {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {shapes : List CShape}
    (cells : Cells ctx shapes) (store : Store ctx)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (initial : Cells.Initialized cells store) :
    Cells.Initialized (cells.underRetained key shape fresh)
      (store.pushRetained key shape fresh) := by
  induction cells with
  | nil => trivial
  | cons head tail ih =>
      change _ ∧ _ at initial ⊢
      refine ⟨?_, ih initial.2⟩
      change (store.pushRetained key shape fresh).read
        ((CInputRef.storage head.ref.toCStorageRef).underRetained key shape fresh) = _
      exact (Store.read_pushRetained_underRetained store key shape fresh
        (.storage head.ref.toCStorageRef)).trans initial.1

public lemma pushStore_initialized {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (shapes : List CShape) (store : Store ctx) :
    Cells.Initialized (references ctx shapes)
      (pushStore ctx shapes store) := by
  induction shapes with
  | nil => trivial
  | cons shape tail ih =>
      change _ ∧ _
      constructor
      · exact Store.read_pushRetained_head
          (pushStore ctx tail store)
          (context ctx tail).canonicalFreshKey shape
          (context ctx tail).canonicalFreshKey_fresh
      · exact Cells.Initialized.underRetained
          (references ctx tail)
          (pushStore ctx tail store)
          (context ctx tail).canonicalFreshKey shape
          (context ctx tail).canonicalFreshKey_fresh ih


/-- The original Store below the actual heterogeneous retained heads. -/
public def originalStore {kind : ProblemKind} (ctx : RuntimeCtx kind) :
    (shapes : List CShape) → Store (context ctx shapes) → Store ctx
  | [], store => store
  | _ :: tail, store => originalStore ctx tail ⟨store.cells.2⟩

/-- Every original structural input reads exactly the projected caller Store. -/
public lemma originalStore_read {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (shapes : List CShape) (store : Store (context ctx shapes))
    {shape : CShape} (input : CInputRef ctx shape) :
    (originalStore ctx shapes store).read input =
      store.read ((transport ctx shapes).liftInput input) := by
  induction shapes with
  | nil =>
      simpa only [originalStore, transport] using
        (congrArg store.read (ClassicalWorkspace.Transport.liftInput_id input)).symm
  | cons head tail ih =>
      rw [originalStore, ih, transport_liftInput_cons]
      exact Store.retainedTail_read _ _ _ store _

/-- Removing only retained Store heads keeps the entire borrowed observation. -/
lemma originalStore_borrowed {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (shapes : List CShape) (store : Store (context ctx shapes)) :
    HEq store.readBorrowedClassical (originalStore ctx shapes store).readBorrowedClassical := by
  induction shapes with
  | nil => rfl
  | cons head tail ih =>
      change HEq (Store.mk store.cells.2).readBorrowedClassical
        (originalStore ctx tail ⟨store.cells.2⟩).readBorrowedClassical
      exact ih _

end

end QuantumAlg.Execution.RetainedCells
