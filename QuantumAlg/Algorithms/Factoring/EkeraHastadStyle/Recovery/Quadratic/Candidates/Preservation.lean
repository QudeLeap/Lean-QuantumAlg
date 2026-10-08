/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Candidates.Initialized
import all QuantumAlg.Components.Classical.NumberTheory.Native.Sub.Preservation
import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Preservation

/-!
# Full original reads and borrowed restoration of actual candidate generation

The complete arithmetic chain writes only its four supplied writable cells.
All other structural reads retain their original values through the actual
subtraction and square-root scopes. Every actual execution restores the full
borrowed classical-quantum-reference state, with no quantum-free or initial
workspace assumption. The same conclusions hold after the real one loading.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic

open Execution
open ClassicalRoutines.NumberTheory

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Every actual input read outside the four arithmetic destinations keeps its complete value. -/
theorem nativeQuadratic_candidates_read_other (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Refs ctx width) {shape : CShape} (other : CInputRef ctx shape)
    (separated : ∀ key ∈ writeKeys refs, key ∉ other.storageKeys) (store : Store ctx) :
    (candidatesStep (model := model) input modulus refs store).1.read other = store.read other := by
  let widened := store.applyOp (widenOp input refs)
  let centered := widened.applyOp (centerOp refs)
  let squared := centered.applyOp (squareOp refs)
  let reduced := NativeSub.intoStep (model := model) (.storage refs.root.toCStorageRef) modulus
    refs.root squared
  let rooted := NativeSqrt.intoStep (model := model) (.storage refs.root.toCStorageRef) refs.root
    reduced.1
  let lower := NativeSub.intoStep (model := model) (.storage refs.center.toCStorageRef)
    (.storage refs.root.toCStorageRef) refs.first rooted.1
  have centerFree : refs.center.key ∉ other.storageKeys :=
    separated _ (by simp [writeKeys])
  have rootFree : refs.root.key ∉ other.storageKeys :=
    separated _ (by simp [writeKeys])
  have firstFree : refs.first.key ∉ other.storageKeys :=
    separated _ (by simp [writeKeys])
  have secondFree : refs.second.key ∉ other.storageKeys :=
    separated _ (by simp [writeKeys])
  exact (Store.read_applyOp_of_not_mem_storageKeys lower.1 (secondOp refs) other secondFree).trans
    ((NativeSub.nativeSub_into_read_unchanged (model := model) (.storage refs.center.toCStorageRef)
      (.storage refs.root.toCStorageRef) refs.first other firstFree rooted.1).trans
      ((NativeSqrt.nativeSqrt_into_read_unchanged (model := model) (.storage
        refs.root.toCStorageRef)
        refs.root other rootFree reduced.1).trans
        ((NativeSub.nativeSub_into_read_unchanged (model := model) (.storage
          refs.root.toCStorageRef)
          modulus refs.root other rootFree squared).trans
          ((Store.read_applyOp_of_not_mem_storageKeys centered (squareOp refs)
            other rootFree).trans
            ((Store.read_applyOp_of_not_mem_storageKeys widened (centerOp refs)
              other centerFree).trans
              (Store.read_applyOp_of_not_mem_storageKeys store (widenOp input refs)
                other centerFree))))))

/-- Actual one loading still writes only the same four candidate-generation destinations. -/
theorem nativeQuadratic_initialized_read_other (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Refs ctx width) {shape : CShape} (other : CInputRef ctx shape)
    (separated : ∀ key ∈ writeKeys refs, key ∉ other.storageKeys) (store : Store ctx) :
    (Initialized.step (model := model) input modulus refs store).1.read other = store.read other :=
  (CheckConstants.nativeQuadratic_check_one_read_other refs.center other
    (separated _ (by simp [writeKeys])) (candidatesStep (model := model) input modulus refs
      store).1).trans
    (nativeQuadratic_candidates_read_other input modulus refs other separated store)

/-- The actual candidate arithmetic restores every complete borrowed joint state. -/
theorem nativeQuadratic_candidates_borrowedRestored (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Refs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (candidates (model := model) input modulus refs).BorrowedRestored Reference state
      ((candidates (model := model) input modulus refs).execute Reference state) := by
  unfold candidates
  apply Circuit.borrowedRestored_seq
  · exact Circuit.borrowedRestored_classical _ state
  · apply Circuit.borrowedRestored_seq
    · exact Circuit.borrowedRestored_classical _ _
    · apply Circuit.borrowedRestored_seq
      · exact Circuit.borrowedRestored_classical _ _
      · apply Circuit.borrowedRestored_seq
        · exact NativeSub.nativeSub_into_borrowedRestored (model := model)
            (.storage refs.root.toCStorageRef) modulus refs.root Reference _
        · apply Circuit.borrowedRestored_seq
          · exact NativeSqrt.nativeSqrt_into_borrowedRestored (model := model)
              (.storage refs.root.toCStorageRef) refs.root Reference _
          · apply Circuit.borrowedRestored_seq
            · exact NativeSub.nativeSub_into_borrowedRestored (model := model)
                (.storage refs.center.toCStorageRef) (.storage refs.root.toCStorageRef)
                refs.first Reference _
            · exact Circuit.borrowedRestored_classical _ _

/-- Appending the two real one-loading instructions preserves the same full borrowed interface. -/
theorem nativeQuadratic_initialized_borrowedRestored (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Refs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Initialized.code (model := model) input modulus refs).BorrowedRestored Reference state
      ((Initialized.code (model := model) input modulus refs).execute Reference state) :=
  Circuit.borrowedRestored_seq (candidates (model := model) input modulus refs)
    (CheckConstants.code (model := model) refs.center)
    state (nativeQuadratic_candidates_borrowedRestored input modulus refs Reference state)
    (CheckConstants.nativeQuadratic_check_one_borrowedRestored refs.center Reference _)

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic
