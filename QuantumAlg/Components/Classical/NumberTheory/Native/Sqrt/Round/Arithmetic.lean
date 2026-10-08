/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Round.Readout
import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Separation
import all QuantumAlg.Util.Nat.Binary.Sqrt

/-!
# Exact arithmetic of the actual square-root round

The stored candidate, full square and selected copy implement one binary
refinement. The complete input is retained and the real increment is
halved. The midpoint bound is an internal loop invariant; the generated
six-cell layout supplies separation without any caller requirement.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem read_cell {source destination observed : CShape}
    (store : Store ctx) (op : ClassicalOp source destination ctx ctx)
    (cell : CWriteRef ctx observed) (different : op.outputRef.key ≠ cell.key) :
    (store.applyOp op).read (.storage cell.toCStorageRef) =
      store.read (.storage cell.toCStorageRef) := by
  apply Store.read_applyOp_of_not_mem_storageKeys
  simpa only [CInputRef.storageKeys, List.mem_singleton] using different

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- The actual final root is exactly the source refinement whenever its midpoint fits. -/
theorem nativeSqrt_round_root
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : RoundRefs ctx width)
    (separated : Separated input refs) (store : Store ctx)
    (midpointFits : (store.read (.storage refs.root.toCStorageRef)).toNat +
      (store.read (.storage refs.half.toCStorageRef)).toNat < 2 ^ width) :
    ((roundStep (model := model) input refs store).1.read (.storage
      refs.root.toCStorageRef)).toNat =
      Nat.BinarySqrt.refine (store.read input).toNat
        (store.read (.storage refs.half.toCStorageRef)).toNat
        (store.read (.storage refs.root.toCStorageRef)).toNat := by
  let added := store.applyOp (addOp refs)
  let squared := added.applyOp (squareOp refs)
  let compared := squared.applyOp (compareOp input refs)
  let selected := selectStep (model := model) refs compared
  have candidateAdded : (added.read (.storage refs.candidate.toCStorageRef)).toNat =
      (store.read (.storage refs.root.toCStorageRef)).toNat +
        (store.read (.storage refs.half.toCStorageRef)).toNat :=
    (nativeSqrt_add_read refs store).trans (Nat.mod_eq_of_lt midpointFits)
  have squareExact : (squared.read (.storage refs.square.toCStorageRef)).toNat =
      ((store.read (.storage refs.root.toCStorageRef)).toNat +
        (store.read (.storage refs.half.toCStorageRef)).toNat) *
      ((store.read (.storage refs.root.toCStorageRef)).toNat +
        (store.read (.storage refs.half.toCStorageRef)).toNat) :=
    (nativeSqrt_square_read refs added).trans
      (congrArg (fun candidate : Nat => candidate * candidate) candidateAdded)
  have inputSquared : squared.read input = store.read input :=
    (Store.read_applyOp_of_not_mem_storageKeys added (squareOp refs) input
      (separated.inputFree refs.square.key (by simp [writeKeys]))).trans
      (Store.read_applyOp_of_not_mem_storageKeys store (addOp refs) input
        (separated.inputFree refs.candidate.key (by simp [writeKeys])))
  have decision : (compared.read (.storage refs.tooLarge.toCStorageRef)).toBool =
      decide ((store.read input).toNat <
        ((store.read (.storage refs.root.toCStorageRef)).toNat +
          (store.read (.storage refs.half.toCStorageRef)).toNat) *
        ((store.read (.storage refs.root.toCStorageRef)).toNat +
          (store.read (.storage refs.half.toCStorageRef)).toNat)) :=
    (nativeSqrt_compare_read input refs squared).trans
      (congrArg₂ (fun original square : Nat => decide (original < square))
        (congrArg CShape.Value.toNat inputSquared) squareExact)
  have rootCompared : compared.read (.storage refs.root.toCStorageRef) =
      store.read (.storage refs.root.toCStorageRef) :=
    (read_cell squared (compareOp input refs) refs.root separated.decisionRoot).trans
      ((read_cell added (squareOp refs) refs.root separated.squareRoot).trans
        (read_cell store (addOp refs) refs.root separated.candidateRoot))
  have candidateCompared :
      (compared.read (.storage refs.candidate.toCStorageRef)).toNat =
      (store.read (.storage refs.root.toCStorageRef)).toNat +
        (store.read (.storage refs.half.toCStorageRef)).toNat :=
    (congrArg CShape.Value.toNat
      ((read_cell squared (compareOp input refs) refs.candidate
        separated.decisionCandidate).trans
        (read_cell added (squareOp refs) refs.candidate separated.squareCandidate))).trans
      candidateAdded
  have rootSelected := nativeSqrt_select_read (model := model) refs compared
  rw [decision, rootCompared, candidateCompared] at rootSelected
  have shifted := congrArg CShape.Value.toNat
    (read_cell selected.1 (shiftOp refs) refs.root separated.rootHalf.symm)
  refine shifted.trans (rootSelected.trans ?_)
  rw [Nat.BinarySqrt.refine_eq_tooLarge]
  simp only [decide_eq_true_eq]

/-- The same actual selected branch preserves and then halves the original increment. -/
theorem nativeSqrt_round_half
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : RoundRefs ctx width)
    (separated : Separated input refs) (store : Store ctx) :
    ((roundStep (model := model) input refs store).1.read (.storage
      refs.half.toCStorageRef)).toNat =
      (store.read (.storage refs.half.toCStorageRef)).toNat / 2 := by
  let added := store.applyOp (addOp refs)
  let squared := added.applyOp (squareOp refs)
  let compared := squared.applyOp (compareOp input refs)
  have halfCompared : compared.read (.storage refs.half.toCStorageRef) =
      store.read (.storage refs.half.toCStorageRef) :=
    (read_cell squared (compareOp input refs) refs.half separated.decisionHalf).trans
      ((read_cell added (squareOp refs) refs.half separated.squareHalf).trans
        (read_cell store (addOp refs) refs.half separated.candidateHalf))
  have halfSelected : (selectStep (model := model) refs compared).1.read (.storage
    refs.half.toCStorageRef) =
      compared.read (.storage refs.half.toCStorageRef) := by
    unfold selectStep
    cases flagRead : compared.read (.storage refs.tooLarge.toCStorageRef) with
    | bit flag =>
        cases flag with
        | false => exact read_cell compared (copyOp refs) refs.half separated.rootHalf
        | true => rfl
  exact (nativeSqrt_shift_read refs (selectStep (model := model) refs compared).1).trans
    (congrArg (fun value : CShape.Value (.unsignedWord width) => value.toNat / 2)
      (halfSelected.trans halfCompared))

/-- Every actual round preserves the complete widened original input. -/
theorem nativeSqrt_round_input
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : RoundRefs ctx width)
    (separated : Separated input refs) (store : Store ctx) :
    (roundStep (model := model) input refs store).1.read input = store.read input :=
  nativeSqrt_round_read_unchanged (model := model) input refs input separated.inputFree store

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt
