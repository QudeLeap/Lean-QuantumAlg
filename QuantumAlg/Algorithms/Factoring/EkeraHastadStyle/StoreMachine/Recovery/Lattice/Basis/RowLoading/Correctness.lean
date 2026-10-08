/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Basis.RowLoading

/-!
# Exact raw representation of actual lattice row loading

The actual resized words represent both original source values modulo the
supplied raw width. The initialized third coordinate and power loaders have
no incoming-zero premise. Exact signed decoding remains a separate width-bound
obligation, while the complete nonoutput caller frame is retained here.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeLoading

open Execution
open ClassicalRoutines
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N width : Nat}

/-- Actual native resize represents the original input word at the supplied raw output width. -/
theorem resize_represents {sourceWidth : Nat} (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    RawSignedRepresents
      ((store.applyOp (.wordResize sourceWidth width ctx input output)).read (writeInput output))
      ((store.read input).toNat : Int) := by
  simp only [Store.applyOp, ClassicalOp.outputRef, Store.read_write_same,
    ClassicalOp.inputRef, ClassicalOp.eval_wordResize]
  exact rawSignedWordRepresents_wordResize (store.read input)

/-- The initialized actual word represents the exact integer power modulo its supplied width. -/
theorem loadPowerOfTwoInto_represents {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    RawSignedRepresents ((powerStep count output store).1.read (writeInput output))
      ((2 : Int) ^ count) := by
  have encoded := Word.PowerOfTwo.into_read count output store
  have naturalCongruence :
      ((powerStep count output store).1.read (writeInput output)).toNat ≡ 2 ^ count
        [MOD 2 ^ width] := by
    rw [encoded]
    exact Nat.mod_modEq (2 ^ count) (2 ^ width)
  have integerCongruence := Int.natCast_modEq_iff.mpr naturalCongruence
  simpa only [RawSignedRepresents, CShape.wordModulus, Nat.cast_pow, Nat.cast_ofNat] using
    integerCongruence

/-- The complete actual first-row tail preserves every read outside its two supplied outputs. -/
theorem firstRowTailInto_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (store : Store ctx) {shape : CShape}
    (other : CInputRef ctx shape) (b12 : output.b12.key ∉ other.storageKeys)
    (b13 : output.b13.key ∉ other.storageKeys) :
    (firstRowTailStep pair output store).1.read other = store.read other := by
  change (Word.PowerOfTwo.step 0 output.b13 (store.applyOp (secondOp pair output))).1.read other = _
  rw [Word.PowerOfTwo.into_callerFrame _ _ _ other b13]
  exact Store.read_applyOp_of_not_mem_storageKeys store (secondOp pair output) other b12

/-- The complete actual row loader preserves every read outside its three original destinations. -/
theorem loadFirstBasisRowInto_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (store : Store ctx) {shape : CShape}
    (other : CInputRef ctx shape) (b11 : output.b11.key ∉ other.storageKeys)
    (b12 : output.b12.key ∉ other.storageKeys) (b13 : output.b13.key ∉ other.storageKeys) :
    (firstRowStep pair output store).1.read other = store.read other := by
  change (firstRowTailStep pair output (store.applyOp (firstOp pair output))).1.read other = _
  rw [firstRowTailInto_callerFrame _ _ _ other b12 b13]
  exact Store.read_applyOp_of_not_mem_storageKeys store (firstOp pair output) other b11

/-- All original raw first-row values and the complete actual nonoutput caller frame. -/
structure FirstBasisRowOutcome (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (before after : Store ctx) : Prop where
  first : RawSignedRepresents (after.read (writeInput output.b11))
    ((before.read (writeInput pair.first.j)).toNat : Int)
  second : RawSignedRepresents (after.read (writeInput output.b12))
    ((before.read (writeInput pair.second.j)).toNat : Int)
  third : RawSignedRepresents (after.read (writeInput output.b13)) 1
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    output.b11.key ∉ other.storageKeys → output.b12.key ∉ other.storageKeys →
      output.b13.key ∉ other.storageKeys → after.read other = before.read other

/-- Actual native loading realizes the original first basis row without an initial-value premise. -/
theorem loadFirstBasisRowInto_correct {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (separation : FirstBasisRowSeparation pair output)
    (store : Store ctx) :
    FirstBasisRowOutcome pair output store (firstRowStep pair output store).1 := by
  refine ⟨?_, ?_, ?_, loadFirstBasisRowInto_callerFrame pair output store⟩
  · change RawSignedRepresents
      ((firstRowTailStep pair output (store.applyOp (firstOp pair output))).1.read
        (writeInput output.b11)) _
    rw [firstRowTailInto_callerFrame _ _ _ _
      (by simpa only [CInputRef.storageKeys, List.mem_singleton] using separation.b11AvoidsB12)
      (by simpa only [CInputRef.storageKeys, List.mem_singleton] using separation.b11AvoidsB13)]
    exact resize_represents _ _ store
  · change RawSignedRepresents
      ((Word.PowerOfTwo.step 0 output.b13
        ((store.applyOp (firstOp pair output)).applyOp (secondOp pair output))).1.read
        (writeInput output.b12)) _
    rw [Word.PowerOfTwo.into_callerFrame _ _ _ _
      (by simpa only [CInputRef.storageKeys, List.mem_singleton] using separation.b12AvoidsB13)]
    have resized := resize_represents (writeInput pair.second.j) output.b12
      (store.applyOp (firstOp pair output))
    rw [Store.read_applyOp_of_not_mem_storageKeys store (firstOp pair output) _
      (by simpa only [firstOp, ClassicalOp.outputRef, CInputRef.storageKeys,
        List.mem_singleton] using separation.secondJAvoidsB11)] at resized
    exact resized
  · exact loadPowerOfTwoInto_represents 0 output.b13 _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeLoading
