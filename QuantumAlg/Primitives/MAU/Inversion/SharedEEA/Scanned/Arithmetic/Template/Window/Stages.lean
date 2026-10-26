/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Window.Source
import all QuantumAlg.Primitives.MAU.Addition.TTK.Gates
import all QuantumAlg.Util.List.Threshold.Finite

/-!
# The exact six original TTK stage words

Suppressing the static low-index masks gives the original source words.
Descending stages reverse their whole emitted word. In particular the
ascending carry-before-sum pair becomes the prescribed descending
sum-before-carry pair [TTK09, qic-loglogaddition-quant.tex:285-318].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticWindow

noncomputable section

open EncodedBit ArithmeticTemplate

private lemma rawPrefix_tail (length start : Nat) (stage : Stage)
    (action : Fin length → List (GateSpec (Addition.TTK.encoding length)))
    (source : ∀ index, rawSource length stage index =
      if within : index < length then
        if start ≤ index then action ⟨index, within⟩ else []
      else []) :
    rawPrefix length stage =
      (List.ofFn (fun index : Fin (length - start) =>
        action ⟨index.val + start, by have := index.isLt; omega⟩)).flatten := by
  rw [rawPrefix]
  have sources : rawSource length stage = (fun index =>
      if within : index < length then
        if start ≤ index then action ⟨index, within⟩ else []
      else []) := funext source
  rw [sources]
  exact ListThreshold.flatMap_bounded_range_mask length start action

/-- The first stream retains precisely the original non-low sum CNOTs. -/
lemma rawPrefix_preXor (length : Nat) :
    rawPrefix length .preXor = Addition.TTK.preXorGates length := by
  rw [rawPrefix_tail length 1 .preXor (fun index => [rawSum length index]) (by
    intro index
    by_cases within : index < length
    · simp only [rawSource, dif_pos within]
      by_cases positive : 0 < index
      · simp only [if_pos positive, if_pos (show 1 ≤ index by omega)]
      · simp only [if_neg positive, if_neg (show ¬1 ≤ index by omega)]
    · simp only [rawSource, dif_neg within])]
  rw [ListThreshold.flatten_ofFn_singleton]
  rfl

private lemma rawPrefix_chain (length : Nat) (stage : Stage)
    (chain : stage = .descendingXor ∨ stage = .ascendingXor) :
    rawPrefix length stage = (Addition.TTK.descendingXorGates length).reverse := by
  let action (index : Fin length) :=
    if positive : 0 < index.val then [rawChain length index positive] else []
  have source (index : Nat) : rawSource length stage index =
      if within : index < length then
        if 2 ≤ index then action ⟨index, within⟩ else []
      else [] := by
    rcases chain with rfl | rfl <;>
      (by_cases within : index < length
       · simp only [rawSource, dif_pos within]
         by_cases internal : 2 ≤ index
         · simp only [dif_pos internal, if_pos internal, action,
             dif_pos (show 0 < index by omega)]
         · simp only [dif_neg internal, if_neg internal]
       · simp only [rawSource, dif_neg within])
  rw [rawPrefix_tail length 2 stage action source]
  have entries : (fun index : Fin (length - 2) =>
      action ⟨index.val + 2, by have := index.isLt; omega⟩) =
      (fun index : Fin (length - 2) =>
        [rawChain length ⟨index.val + 2, by have := index.isLt; omega⟩
          (by change 0 < index.val + 2; omega)]) := by
    funext index
    simp only [action, dif_pos (show 0 < index.val + 2 by omega)]
  rw [entries, ListThreshold.flatten_ofFn_singleton, Addition.TTK.descendingXorGates,
    List.reverse_reverse]
  apply congrArg List.ofFn
  funext index
  have previous : before length (⟨index.val + 2, by have := index.isLt; omega⟩ : Fin length) =
      (⟨index.val + 1, by have := index.isLt; omega⟩ : Fin length) := by
    apply Fin.ext
    change index.val + 2 - 1 = index.val + 1
    omega
  simp only [rawChain, previous]

/-- Reversing the stream yields the exact original descending operand chain. -/
lemma rawPrefix_descendingXor (length : Nat) :
    (rawPrefix length .descendingXor).reverse = Addition.TTK.descendingXorGates length := by
  rw [rawPrefix_chain length .descendingXor (Or.inl rfl), List.reverse_reverse]

/-- The ascending stream restores the same operand chain in its source order. -/
lemma rawPrefix_ascendingXor (length : Nat) :
    rawPrefix length .ascendingXor = Addition.TTK.ascendingXorGates length := by
  rw [rawPrefix_chain length .ascendingXor (Or.inr rfl), Addition.TTK.ascendingXorGates]

/-- The carry stream contains exactly the original upward carry Toffolis. -/
lemma rawPrefix_carry (length : Nat) :
    rawPrefix length .carry = Addition.TTK.carryGates length := by
  let action (index : Fin length) :=
    if positive : 0 < index.val then [rawCarry length index positive] else []
  have source (index : Nat) : rawSource length .carry index =
      if within : index < length then
        if 1 ≤ index then action ⟨index, within⟩ else []
      else [] := by
    by_cases within : index < length
    · simp only [rawSource, dif_pos within]
      by_cases positive : 0 < index
      · simp only [dif_pos positive, if_pos (show 1 ≤ index by omega), action]
      · simp only [dif_neg positive, if_neg (show ¬1 ≤ index by omega)]
    · simp only [rawSource, dif_neg within]
  rw [rawPrefix_tail length 1 .carry action source]
  have entries : (fun index : Fin (length - 1) =>
      action ⟨index.val + 1, by have := index.isLt; omega⟩) =
      (fun index : Fin (length - 1) =>
        [rawCarry length ⟨index.val + 1, by have := index.isLt; omega⟩
          (by change 0 < index.val + 1; omega)]) := by
    funext index
    simp only [action, dif_pos (show 0 < index.val + 1 by omega)]
  rw [entries, ListThreshold.flatten_ofFn_singleton, Addition.TTK.carryGates]
  apply congrArg List.ofFn
  funext index
  have previous : before length (⟨index.val + 1, by have := index.isLt; omega⟩ : Fin length) =
      (⟨index.val, by have := index.isLt; omega⟩ : Fin length) := by
    apply Fin.ext
    change index.val + 1 - 1 = index.val
    omega
  simp only [rawCarry, previous]

/-- Reversing the whole ascending pair retains the original descending block order. -/
lemma rawPrefix_descendingUncompute (length : Nat) :
    (rawPrefix length .descendingUncompute).reverse =
      Addition.TTK.descendingUncomputeGates length := by
  let action (index : Fin length) := if positive : 0 < index.val then
    [rawCarry length index positive, rawSum length index] else []
  have source (index : Nat) : rawSource length .descendingUncompute index =
      if within : index < length then
        if 1 ≤ index then action ⟨index, within⟩ else []
      else [] := by
    by_cases within : index < length
    · simp only [rawSource, dif_pos within]
      by_cases positive : 0 < index
      · simp only [dif_pos positive, if_pos (show 1 ≤ index by omega), action]
      · simp only [dif_neg positive, if_neg (show ¬1 ≤ index by omega)]
    · simp only [rawSource, dif_neg within]
  rw [rawPrefix_tail length 1 .descendingUncompute action source]
  have entries : (fun index : Fin (length - 1) =>
      action ⟨index.val + 1, by have := index.isLt; omega⟩) =
      (fun index : Fin (length - 1) =>
        [rawCarry length ⟨index.val + 1, by have := index.isLt; omega⟩
          (by change 0 < index.val + 1; omega),
          rawSum length ⟨index.val + 1, by have := index.isLt; omega⟩]) := by
    funext index
    simp only [action, dif_pos (show 0 < index.val + 1 by omega)]
  rw [entries, List.reverse_flatten, List.map_ofFn, Addition.TTK.descendingUncomputeGates]
  apply congrArg List.flatten
  apply congrArg List.reverse
  apply congrArg List.ofFn
  funext index
  have previous : before length (⟨index.val + 1, by have := index.isLt; omega⟩ : Fin length) =
      (⟨index.val, by have := index.isLt; omega⟩ : Fin length) := by
    apply Fin.ext
    change index.val + 1 - 1 = index.val
    omega
  simp only [Function.comp_apply, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, rawCarry, rawSum, previous]

/-- Every source index, including the low bit, occurs in the final sum stream. -/
lemma rawPrefix_finalXor (length : Nat) :
    rawPrefix length .finalXor = Addition.TTK.finalXorGates length := by
  rw [rawPrefix_tail length 0 .finalXor (fun index => [rawSum length index]) (by
    intro index
    by_cases within : index < length
    · simp only [rawSource, dif_pos within, if_pos (Nat.zero_le index)]
    · simp only [rawSource, dif_neg within])]
  simp only [Nat.sub_zero, Nat.add_zero]
  rw [ListThreshold.flatten_ofFn_singleton]
  rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticWindow
