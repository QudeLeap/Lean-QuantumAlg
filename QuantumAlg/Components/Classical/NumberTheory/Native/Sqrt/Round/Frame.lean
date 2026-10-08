/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Round
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Unchanged structural reads of the actual square-root round

The five actual destinations form the whole write footprint of the round.
Every structural input outside those keys has exactly its original value
after all instructions and the selected copy. A generated lexical layout
will establish this footprint's separation from every caller input.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Exact destination keys of the real addition, square, comparison, copy and shift. -/
def writeKeys (refs : RoundRefs ctx width) : List StorageKey :=
  [refs.candidate.key, refs.square.key, refs.tooLarge.key, refs.root.key, refs.half.key]

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

private theorem copy_preserves {shape : CShape} (refs : RoundRefs ctx width)
    (other : CInputRef ctx shape) (separate : refs.root.key ∉ other.storageKeys)
    (store : Store ctx) :
    ((selectStep (model := model) refs store).1).read other = store.read other := by
  unfold selectStep
  cases flagRead : store.read (.storage refs.tooLarge.toCStorageRef) with
  | bit flag =>
      cases flag with
      | false =>
          exact Store.read_applyOp_of_not_mem_storageKeys store (copyOp refs) other separate
      | true => rfl

/-- Every actual round retains all original values outside its five genuine destinations. -/
theorem nativeSqrt_round_read_unchanged
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : RoundRefs ctx width)
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : ∀ key ∈ writeKeys refs, key ∉ other.storageKeys) (store : Store ctx) :
    ((roundStep (model := model) input refs store).1).read other = store.read other := by
  let added := store.applyOp (addOp refs)
  let squared := added.applyOp (squareOp refs)
  let compared := squared.applyOp (compareOp input refs)
  let selected := selectStep (model := model) refs compared
  have afterShift := Store.read_applyOp_of_not_mem_storageKeys selected.1
    (shiftOp refs) other (separate refs.half.key (by simp [writeKeys]))
  have afterCopy := copy_preserves (model := model) refs other
    (separate refs.root.key (by simp [writeKeys])) compared
  have afterCompare := Store.read_applyOp_of_not_mem_storageKeys squared
    (compareOp input refs) other (separate refs.tooLarge.key (by simp [writeKeys]))
  have afterSquare := Store.read_applyOp_of_not_mem_storageKeys added
    (squareOp refs) other (separate refs.square.key (by simp [writeKeys]))
  have afterAdd := Store.read_applyOp_of_not_mem_storageKeys store
    (addOp refs) other (separate refs.candidate.key (by simp [writeKeys]))
  exact afterShift.trans (afterCopy.trans (afterCompare.trans (afterSquare.trans afterAdd)))

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt
