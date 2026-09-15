/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Validation.Semantics
import all QuantumAlg.Components.Classical.TerminalDecode.Encoding
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.Store.Ext
import all QuantumAlg.Util.Classical.GF2

/-!
# Actual GF(2) validation columns and their original dot product

Every actual AND reads the current sample and candidate, then the actual XOR
updates parity. The ordered record fold preserves the source reads when its
two real temporary cells are separate from them. The row scope supplies that
separation and its actual parity clear; no original sample equation is assumed.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

private theorem avoids {left right : CShape} (output : CWriteRef ctx left)
    (other : CWriteRef ctx right) (separate : output.key ≠ other.key) :
    output.key ∉ (CInputRef.storage other.toCStorageRef).storageKeys := by
  simpa only [CInputRef.storageKeys, List.mem_singleton] using separate

private theorem bit_word_ne (bit : CWriteRef ctx .bit)
    (word : CWriteRef ctx (.unsignedWord width)) : bit.key ≠ word.key := by
  intro same
  have impossible := CStorageRef.storageRef_shape_eq_of_key bit.toCStorageRef
    word.toCStorageRef same
  cases impossible

/-- The actual AND output is consumed by the following XOR on the original parity. -/
theorem gf2ValidationColumn_parity
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (parity product : CWriteRef ctx .bit)
    (row : Fin rowCount) (column : Fin width) (store : Store ctx)
    (separate : product.key ≠ parity.key) :
    (validationColumnStep input candidate parity product row column store).1.read
      (.storage parity.toCStorageRef) =
      .bit ((store.read (.storage parity.toCStorageRef)).toBool ^^
        (((store.read input).get row).bitGet column).toBool &&
          ((store.read (.storage candidate.toCStorageRef)).wordBitGet column).toBool) := by
  change ((store.applyOp (validationProductOp input candidate product row column)).applyOp
    (validationParityOp parity product)).read _ = _
  refine (Store.read_applyOp_output _ (validationParityOp parity product)).trans ?_
  change Resource.BitOpcode.eval .xor (.product
    ((store.applyOp (validationProductOp input candidate product row column)).read
      (.storage parity.toCStorageRef))
    ((store.applyOp (validationProductOp input candidate product row column)).read
      (.storage product.toCStorageRef))) = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _
    (validationProductOp input candidate product row column) _ (avoids product parity separate)]
  have multiplied : (store.applyOp (validationProductOp input candidate product row column)).read
      (.storage product.toCStorageRef) = Resource.BitOpcode.eval .and (.product
        (((store.read input).get row).bitGet column)
        ((store.read (.storage candidate.toCStorageRef)).wordBitGet column)) :=
    Store.read_applyOp_output store (validationProductOp input candidate product row column)
  rw [multiplied]
  change Resource.BitOpcode.eval .xor (.product
    (store.read (.storage parity.toCStorageRef))
    (Resource.BitOpcode.eval .and (.product
      (((store.read input).get row).bitGet column)
      ((store.read (.storage candidate.toCStorageRef)).wordBitGet column)))) = _
  cases store.read (.storage parity.toCStorageRef)
  cases ((store.read input).get row).bitGet column
  cases (store.read (.storage candidate.toCStorageRef)).wordBitGet column
  rfl

/-- A real validation column writes only the actual product and parity cells. -/
theorem gf2ValidationColumn_read_other
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (parity product : CWriteRef ctx .bit)
    (row : Fin rowCount) (column : Fin width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (parityFree : parity.key ∉ other.storageKeys)
    (productFree : product.key ∉ other.storageKeys) :
    (validationColumnStep input candidate parity product row column store).1.read other =
      store.read other := by
  change ((store.applyOp (validationProductOp input candidate product row column)).applyOp
    (validationParityOp parity product)).read other = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (validationParityOp parity product)
      other parityFree,
    Store.read_applyOp_of_not_mem_storageKeys store
      (validationProductOp input candidate product row column) other productFree]

/-- The ordered actual column fold preserves every read outside its two temporary cells. -/
theorem gf2ValidationColumns_read_other
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (parity product : CWriteRef ctx .bit)
    (row : Fin rowCount) (count : Nat) (indices : Fin count → Fin width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (parityFree : parity.key ∉ other.storageKeys)
    (productFree : product.key ∉ other.storageKeys) :
    (Circuit.forRangeRecord count
      (fun index => validationColumn input candidate parity product row (indices index))
      (fun index => validationColumnStep input candidate parity product row (indices index))
      store).1.read other = store.read other := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      change (Circuit.forRangeRecord count _ _
        (validationColumnStep input candidate parity product row (indices 0) store).1).1.read
          other = _
      exact (ih (fun index => indices index.succ) _).trans
        (gf2ValidationColumn_read_other input candidate parity product row (indices 0)
          store other parityFree productFree)

private theorem column_parity
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (parity product : CWriteRef ctx .bit)
    (row : Fin rowCount) (column : Fin width) (store : Store ctx)
    (separate : product.key ≠ parity.key)
    (rowWord candidateWord : ClassicalAlgorithms.Word width)
    (sampleValue : (store.read input).get row =
      .bits (ClassicalAlgorithms.GF2.testBit rowWord))
    (candidateValue : store.read (.storage candidate.toCStorageRef) =
      .unsignedWord candidateWord) :
    ((validationColumnStep input candidate parity product row column store).1.read
      (.storage parity.toCStorageRef)).toBool =
      ((store.read (.storage parity.toCStorageRef)).toBool ^^
        (ClassicalAlgorithms.GF2.testBit rowWord column &&
          ClassicalAlgorithms.GF2.testBit candidateWord column)) := by
  rw [gf2ValidationColumn_parity input candidate parity product row column store separate,
    sampleValue, candidateValue]
  simp only [CShape.Value.toBool, CShape.Value.bitGet, CShape.Value.wordBitGet]
  simp only [ClassicalAlgorithms.GF2.testBit_machine_coordinate]

private theorem columns_parity
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (parity product : CWriteRef ctx .bit)
    (row : Fin rowCount) (count : Nat) (indices : Fin count → Fin width) (store : Store ctx)
    (separate : product.key ≠ parity.key)
    (parityFree : parity.key ∉ input.storageKeys) (productFree : product.key ∉ input.storageKeys)
    (rowWord candidateWord : ClassicalAlgorithms.Word width)
    (sampleValue : (store.read input).get row =
      .bits (ClassicalAlgorithms.GF2.testBit rowWord))
    (candidateValue : store.read (.storage candidate.toCStorageRef) =
      .unsignedWord candidateWord) :
    ((Circuit.forRangeRecord count
      (fun index => validationColumn input candidate parity product row (indices index))
      (fun index => validationColumnStep input candidate parity product row (indices index))
      store).1.read (.storage parity.toCStorageRef)).toBool =
      (List.ofFn indices).foldl (fun current column => current ^^
        (ClassicalAlgorithms.GF2.testBit rowWord column &&
          ClassicalAlgorithms.GF2.testBit candidateWord column))
        (store.read (.storage parity.toCStorageRef)).toBool := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      let first := (validationColumnStep input candidate parity product row (indices 0) store).1
      have firstInput : first.read input = store.read input :=
        gf2ValidationColumn_read_other input candidate parity product row (indices 0) store
          input parityFree productFree
      have firstCandidate : first.read (.storage candidate.toCStorageRef) =
          .unsignedWord candidateWord :=
        (gf2ValidationColumn_read_other input candidate parity product row (indices 0) store
          (.storage candidate.toCStorageRef)
          (avoids parity candidate (bit_word_ne parity candidate))
          (avoids product candidate (bit_word_ne product candidate))).trans candidateValue
      have firstSample : (first.read input).get row =
          .bits (ClassicalAlgorithms.GF2.testBit rowWord) :=
        (congrArg (fun value => value.get row) firstInput).trans sampleValue
      change ((Circuit.forRangeRecord count _ _ first).1.read _).toBool = _
      rw [ih (fun index => indices index.succ) first firstSample firstCandidate,
        column_parity input candidate parity product row (indices 0) store separate
          rowWord candidateWord sampleValue candidateValue, List.ofFn_succ, List.foldl_cons]

/-- The same actual width traversal computes the original ordered Boolean parity. -/
theorem gf2ValidationColumns_parity
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (parity product : CWriteRef ctx .bit)
    (row : Fin rowCount) (store : Store ctx) (separate : product.key ≠ parity.key)
    (parityFree : parity.key ∉ input.storageKeys) (productFree : product.key ∉ input.storageKeys)
    (rowWord candidateWord : ClassicalAlgorithms.Word width)
    (sampleValue : (store.read input).get row =
      .bits (ClassicalAlgorithms.GF2.testBit rowWord))
    (candidateValue : store.read (.storage candidate.toCStorageRef) =
      .unsignedWord candidateWord) :
    ((Circuit.forRangeRecord width (validationColumn input candidate parity product row)
      (validationColumnStep input candidate parity product row) store).1.read
        (.storage parity.toCStorageRef)).toBool =
      (List.finRange width).foldl (fun current column => current ^^
        (ClassicalAlgorithms.GF2.testBit rowWord column &&
          ClassicalAlgorithms.GF2.testBit candidateWord column))
        (store.read (.storage parity.toCStorageRef)).toBool := by
  simpa only [List.ofFn_id, id_eq] using columns_parity input candidate parity product row width id
    store separate parityFree productFree rowWord candidateWord sampleValue candidateValue

/-- After the real row clear, the actual final parity is false exactly for a zero dot product. -/
theorem gf2ValidationColumns_zero_iff
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (parity product : CWriteRef ctx .bit)
    (row : Fin rowCount) (store : Store ctx) (separate : product.key ≠ parity.key)
    (parityFree : parity.key ∉ input.storageKeys) (productFree : product.key ∉ input.storageKeys)
    (rowWord candidateWord : ClassicalAlgorithms.Word width)
    (sampleValue : (store.read input).get row =
      .bits (ClassicalAlgorithms.GF2.testBit rowWord))
    (candidateValue : store.read (.storage candidate.toCStorageRef) =
      .unsignedWord candidateWord)
    (cleared : store.read (.storage parity.toCStorageRef) = .bit false) :
    ((Circuit.forRangeRecord width (validationColumn input candidate parity product row)
      (validationColumnStep input candidate parity product row) store).1.read
        (.storage parity.toCStorageRef)).toBool = false ↔
      ClassicalAlgorithms.GF2.dot rowWord candidateWord = 0 := by
  rw [gf2ValidationColumns_parity input candidate parity product row store separate
    parityFree productFree rowWord candidateWord sampleValue candidateValue,
    cleared, CShape.Value.toBool]
  exact ClassicalAlgorithms.GF2.logicalParity_eq_false_iff_dot_eq_zero rowWord candidateWord

/-- The original decoder and the original word-bit read use the same ordered sample bits. -/
theorem gf2ValidationDecodedBits (value : CShape.Value (.bits width)) :
    value = .bits (ClassicalAlgorithms.GF2.testBit (ClassicalAlgorithms.TerminalDecode.eval
      (TerminalDecode.decodeInput .bigEndian value))) := by
  cases value with
  | bits values =>
      apply congrArg CShape.Value.bits
      funext column
      change values column = ((ClassicalAlgorithms.TerminalDecode.eval
        ({ order := .bigEndian, bits := values } :
          ClassicalAlgorithms.TerminalDecode.Input width)).val).testBit (Fin.rev column).val
      rw [ClassicalAlgorithms.TerminalDecode.eval_bigEndian_val,
        Nat.testBit_ofBits_lt (values ∘ Fin.rev) (Fin.rev column).val (Fin.rev column).isLt]
      exact congrArg values (Fin.rev_rev column).symm

end

end QuantumAlg.ClassicalRoutines.GF2.Native
