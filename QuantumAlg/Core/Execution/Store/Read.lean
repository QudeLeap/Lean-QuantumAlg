/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Execution.Store

/-!
# Structural read support and actual store updates

Every key below comes from a storage reference already present in the context.
Updating a cell outside that support leaves the complete structural read
unchanged. This includes products, fixed vectors and addressed bit slices;
it does not permit an arbitrary computation in a read reference.
-/

namespace QuantumAlg.CInputRef

/-- Actual stored keys traversed by one closed structural input reference. -/
@[expose] public def storageKeys {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape} :
    CInputRef ctx shape → List StorageKey
  | .storage ref => [ref.key]
  | .product left right => storageKeys left ++ storageKeys right
  | .fixedVector entries => (List.ofFn (fun index => storageKeys (entries index))).flatten
  | .first input => storageKeys input
  | .second input => storageKeys input
  | .vectorGet input _index => storageKeys input
  | .bitsGet input _index => storageKeys input
  | .wordBitGet input _index => storageKeys input

/-- Every structurally read key names a real existing context entry. -/
public lemma storageKeys_subset_context {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (input : CInputRef ctx shape) :
    input.storageKeys ⊆ ctx.keys := by
  induction input with
  | storage ref =>
      intro key present
      have same : key = ref.key := List.mem_singleton.mp present
      subst key
      exact List.mem_map_of_mem ref.present
  | product left right leftIH rightIH =>
      intro key present
      exact (List.mem_append.mp present).elim (leftIH ·) (rightIH ·)
  | fixedVector entries entriesIH =>
      intro key present
      obtain ⟨keys, listed, member⟩ := List.mem_flatten.mp present
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp listed
      exact entriesIH index member
  | first input ih => exact ih
  | second input ih => exact ih
  | vectorGet input index ih => exact ih
  | bitsGet input index ih => exact ih
  | wordBitGet input index ih => exact ih

/-- Lifting an old reference under a retained cell preserves its exact read support. -/
public lemma storageKeys_underRetained {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (input : CInputRef ctx shape)
    (key : StorageKey) (retainedShape : CShape) (fresh : key ∉ ctx.keys) :
    (input.underRetained key retainedShape fresh).storageKeys = input.storageKeys := by
  induction input with
  | storage ref => rfl
  | product left right leftIH rightIH => exact congrArg₂ List.append leftIH rightIH
  | fixedVector entries entriesIH =>
      exact congrArg List.flatten (congrArg List.ofFn (funext entriesIH))
  | first input ih => exact ih
  | second input ih => exact ih
  | vectorGet input index ih => exact ih
  | bitsGet input index ih => exact ih
  | wordBitGet input index ih => exact ih

/-- A fresh retained output cannot alias any pre-existing structural input. -/
public lemma fresh_not_mem_storageKeys_underRetained {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {shape : CShape} (input : CInputRef ctx shape)
    (key : StorageKey) (retainedShape : CShape) (fresh : key ∉ ctx.keys) :
    key ∉ (input.underRetained key retainedShape fresh).storageKeys := by
  rw [storageKeys_underRetained]
  exact fun present => fresh (storageKeys_subset_context input present)

end QuantumAlg.CInputRef

namespace QuantumAlg.Execution.Store

/-- A write outside the structural input's actual key support preserves its complete value. -/
public lemma read_write_of_not_mem_storageKeys {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {written observed : CShape} (store : Store ctx) (output : CWriteRef ctx written)
    (value : written.Value) (input : CInputRef ctx observed)
    (separate : output.key ∉ input.storageKeys) :
    (store.write output value).read input = store.read input := by
  induction input with
  | storage ref =>
      apply read_write_other
      intro same
      apply separate
      exact List.mem_singleton.mpr same
  | product left right leftIH rightIH =>
      apply congrArg₂ CShape.Value.product
      · exact leftIH (fun member => separate (List.mem_append_left _ member))
      · exact rightIH (fun member => separate (List.mem_append_right _ member))
  | fixedVector entries entriesIH =>
      apply congrArg CShape.Value.fixedVector
      funext index
      apply entriesIH index
      intro member
      apply separate
      exact List.mem_flatten.mpr ⟨(entries index).storageKeys,
        List.mem_ofFn.mpr ⟨index, rfl⟩, member⟩
  | first input ih => exact congrArg CShape.Value.first (ih separate)
  | second input ih => exact congrArg CShape.Value.second (ih separate)
  | vectorGet input index ih => exact congrArg (fun entry => entry.get index) (ih separate)
  | bitsGet input index ih => exact congrArg (fun entry => entry.bitGet index) (ih separate)
  | wordBitGet input index ih =>
      exact congrArg (fun entry => entry.wordBitGet index) (ih separate)

/-- A closed operation changes no structural input outside its actual written key. -/
public lemma read_applyOp_of_not_mem_storageKeys {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {input output observed : CShape} (store : Store ctx)
    (op : ClassicalOp input output ctx ctx) (other : CInputRef ctx observed)
    (separate : op.outputRef.key ∉ other.storageKeys) :
    (store.applyOp op).read other = store.read other :=
  read_write_of_not_mem_storageKeys store op.outputRef _ other separate

end QuantumAlg.Execution.Store
