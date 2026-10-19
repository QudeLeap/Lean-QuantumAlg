/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Terminal.Program.Execution

/-!
# Exact actual short-log decoder values and caller frame

The original stored bit order determines the actual full word and both source
registers. No initial accumulator value is required: a full-width native fold
eliminates its original contribution. Every read outside the four supplied
write cells is preserved.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.BatchMachine

open Execution
open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The original distinct write identities satisfy the native splitter's exact separation. -/
lemma split_separation (refs : Refs ctx N) (separation : Separation refs) :
    Word.Split.Separation (splitRefs refs) :=
  ⟨separation.scratchAvoidsK.symm, separation.scratchAvoidsJ.symm,
    separation.jAvoidsK.symm⟩

/-- The actual decoded full word equals the original source's packed terminal index. -/
lemma fullDecodeInto_read {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) :
    ((fullDecodeStep refs store).1.read (.storage refs.full.toCStorageRef)).toNat =
      (BatchRecovery.decodeFullRegisterIndex (shortLogBits N) (tradeoffBits N)
        (sourceBits N store (terminalInput refs))).val := by
  calc
    _ = (ClassicalAlgorithms.TerminalDecode.eval
        (TerminalDecode.decodeInputFromBitRefs .littleEndian store (decoderInputs refs))).val :=
      TerminalDecode.terminalDecode_intoFromBitRefs_read_output .littleEndian
        (decoderInputs refs) refs.full store (fun _ => separation.inputAvoidsFull)
    _ = Nat.ofBits (fun index => (store.read (decoderInputs refs index)).toBool) :=
      ClassicalAlgorithms.TerminalDecode.eval_littleEndian_val _
    _ = _ := rfl

/-- Actual full-word decoding changes no structural read outside its full-word output. -/
lemma fullDecodeInto_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx N) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (full : refs.full.key ∉ other.storageKeys) :
    (fullDecodeStep refs store).1.read other = store.read other :=
  TerminalDecode.terminalDecode_fold_read_other _ _ _ other full

/-- The native copy writes the complete actual full-word value into the original scratch cell. -/
lemma copy_read (refs : Refs ctx N) (store : Store ctx) :
    (store.applyOp (copyOp refs)).read (.storage refs.scratch.toCStorageRef) =
      store.read (.storage refs.full.toCStorageRef) := by
  simp only [Store.applyOp, copyOp, ClassicalOp.outputRef, Store.read_write_same,
    ClassicalOp.inputRef, ClassicalOp.eval_wordUnary]
  cases store.read (.storage refs.full.toCStorageRef)
  rfl

/-- Copying and native splitting preserve all reads outside the three actual split writes. -/
lemma copySplitInto_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx N) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (scratch : refs.scratch.key ∉ other.storageKeys) (j : refs.j.key ∉ other.storageKeys)
    (k : refs.k.key ∉ other.storageKeys) :
    (copySplitStep refs store).1.read other = store.read other := by
  change (Word.Split.splitStep (splitRefs refs) (store.applyOp (copyOp refs))).1.read other = _
  rw [Word.Split.splitInto_callerFrame _ _ other scratch j k]
  exact Store.read_applyOp_of_not_mem_storageKeys store (copyOp refs) other scratch

/-- The actual high source register is the exact high quotient of the incoming full word. -/
lemma copySplitInto_j {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) :
    ((copySplitStep refs store).1.read (.storage refs.j.toCStorageRef)).toNat =
      (store.read (.storage refs.full.toCStorageRef)).toNat / 2 ^ KWidth N := by
  change ((Word.Split.splitStep (splitRefs refs) (store.applyOp (copyOp refs))).1.read
    (.storage refs.j.toCStorageRef)).toNat = _
  rw [Word.Split.splitInto_high _ (split_separation refs separation)]
  change ((store.applyOp (copyOp refs)).read (.storage refs.scratch.toCStorageRef)).toNat / _ = _
  rw [copy_read]

/-- The actual low source register is the exact low remainder of the incoming full word. -/
lemma copySplitInto_k {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) :
    ((copySplitStep refs store).1.read (.storage refs.k.toCStorageRef)).toNat =
      (store.read (.storage refs.full.toCStorageRef)).toNat % 2 ^ KWidth N := by
  change ((Word.Split.splitStep (splitRefs refs) (store.applyOp (copyOp refs))).1.read
    (.storage refs.k.toCStorageRef)).toNat = _
  rw [Word.Split.splitInto_low _ (split_separation refs separation)]
  change ((store.applyOp (copyOp refs)).read (.storage refs.scratch.toCStorageRef)).toNat % _ = _
  rw [copy_read]

/-- The actual destructive scratch cell finishes at the same exact high quotient. -/
lemma copySplitInto_scratch {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) :
    ((copySplitStep refs store).1.read (.storage refs.scratch.toCStorageRef)).toNat =
      (store.read (.storage refs.full.toCStorageRef)).toNat / 2 ^ KWidth N := by
  change ((Word.Split.splitStep (splitRefs refs) (store.applyOp (copyOp refs))).1.read
    (.storage refs.scratch.toCStorageRef)).toNat = _
  rw [Word.Split.splitInto_work _ (split_separation refs separation)]
  change ((store.applyOp (copyOp refs)).read (.storage refs.scratch.toCStorageRef)).toNat / _ = _
  rw [copy_read]

/-- The original full word remains intact through the destructive scratch-word split. -/
lemma copySplitInto_full {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) :
    (copySplitStep refs store).1.read (.storage refs.full.toCStorageRef) =
      store.read (.storage refs.full.toCStorageRef) :=
  copySplitInto_callerFrame refs store _
    (by simpa only [CInputRef.storageKeys, List.mem_singleton] using separation.fullAvoidsScratch)
    (by simpa only [CInputRef.storageKeys, List.mem_singleton] using separation.fullAvoidsJ)
    (by simpa only [CInputRef.storageKeys, List.mem_singleton] using separation.fullAvoidsK)

/-- Complete structural caller separation from the four original decoder write identities. -/
def CallerSeparated (refs : Refs ctx N) {shape : CShape} (other : CInputRef ctx shape) : Prop :=
  ∀ slot, pairOutputKey refs slot ∉ other.storageKeys

/-- The complete actual decoder retains every caller read outside its four write cells. -/
lemma decodeInto_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx N) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : CallerSeparated refs other) :
    (decodeStep refs store).1.read other = store.read other := by
  change (copySplitStep refs (fullDecodeStep refs store).1).1.read other = _
  rw [copySplitInto_callerFrame refs _ other (separate .scratch) (separate .j) (separate .k)]
  exact fullDecodeInto_callerFrame refs store other (separate .full)

/-- Original source semantics of all four actual decoder outputs and every untouched read. -/
structure DecodeOutcome (refs : Refs ctx N) (before after : Store ctx) : Prop where
  full : (after.read (.storage refs.full.toCStorageRef)).toNat =
    (BatchRecovery.decodeFullRegisterIndex (shortLogBits N) (tradeoffBits N)
      (sourceBits N before (terminalInput refs))).val
  scratch : (after.read (.storage refs.scratch.toCStorageRef)).toNat =
    (sourceSample N before (terminalInput refs)).1.val
  j : (after.read (.storage refs.j.toCStorageRef)).toNat =
    (sourceSample N before (terminalInput refs)).1.val
  k : (after.read (.storage refs.k.toCStorageRef)).toNat =
    (sourceSample N before (terminalInput refs)).2.val
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    CallerSeparated refs other → after.read other = before.read other

/-- Arbitrary incoming accumulator words decode to the exact original terminal sample. -/
lemma decodeInto_correct {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) : DecodeOutcome refs store (decodeStep refs store).1 := by
  refine ⟨?_, ?_, ?_, ?_, decodeInto_callerFrame refs store⟩
  · change ((copySplitStep refs (fullDecodeStep refs store).1).1.read
      (.storage refs.full.toCStorageRef)).toNat = _
    rw [copySplitInto_full refs separation, fullDecodeInto_read refs separation]
  · change ((copySplitStep refs (fullDecodeStep refs store).1).1.read
      (.storage refs.scratch.toCStorageRef)).toNat = _
    rw [copySplitInto_scratch refs separation, fullDecodeInto_read refs separation,
      sourceSample_fst_val]
  · change ((copySplitStep refs (fullDecodeStep refs store).1).1.read
      (.storage refs.j.toCStorageRef)).toNat = _
    rw [copySplitInto_j refs separation, fullDecodeInto_read refs separation, sourceSample_fst_val]
  · change ((copySplitStep refs (fullDecodeStep refs store).1).1.read
      (.storage refs.k.toCStorageRef)).toNat = _
    rw [copySplitInto_k refs separation, fullDecodeInto_read refs separation, sourceSample_snd_val]

/-- Exact structural input preservation preserves the original pure bit interpretation. -/
lemma sourceBits_of_read_eq (input : CInputRef ctx (.bits (measurementBits N)))
    (before after : Store ctx) (same : after.read input = before.read input) :
    sourceBits N after input = sourceBits N before input := by
  funext index
  change ((after.read input).bitGet index).toBool = ((before.read input).bitGet index).toBool
  rw [same]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.BatchMachine
