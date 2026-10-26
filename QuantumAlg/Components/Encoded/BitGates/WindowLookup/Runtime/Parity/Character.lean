/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Parity
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Parity.Row.Constant

/-!
# Exact measured character of paid runtime table parity

The fixed full-width AND/XOR computation has the same character as the
set-bit specification of the actual word read from the table array. Both
bit conventions are explicit: structural unsigned-word reads are reversed
once to match the original least-significant-position measured mask.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeParity

open Execution

noncomputable section

variable {ctx : RuntimeCtx .quantum} {width : Nat}

private lemma fold_filter (indices : List (Fin width))
    (constant : Fin (2 ^ width)) (mask : CShape.Value (.bits width)) :
    indices.foldr (fun index tail =>
      (constant.val.testBit index.val && (mask.bitGet index).toBool) ^^ tail) false =
      (indices.filter (fun index => constant.val.testBit index.val)).foldr
        (fun index tail => (mask.bitGet index).toBool ^^ tail) false := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      cases bit : constant.val.testBit index.val <;>
        simp only [List.foldr_cons, List.filter_cons, bit, Bool.false_and, Bool.true_and,
          Bool.false_xor, Bool.false_eq_true, if_false, if_true, ih]

/-- The complete runtime word/mask dot product is exactly the original selected-bit character. -/
lemma value_inputs (table : CInputRef ctx (.unsignedWord width))
    (measured : CInputRef ctx (.bits width)) (store : Store ctx) :
    value (inputs table measured) store = MaskParity.maskValue (store.read measured)
      ⟨(store.read table).toNat, (store.read table).toNat_lt⟩ := by
  have pairList : inputs table measured =
      (List.ofFn fun index : Fin width => index).map
        (fun index => (wordBit table index, CInputRef.bitsGet measured index)) :=
    List.ofFn_comp' (fun index : Fin width => index)
      (fun index => (wordBit table index, CInputRef.bitsGet measured index))
  unfold value
  rw [pairList, List.foldr_map]
  have contribution :
      (fun (index : Fin width) (tail : Bool) =>
        ((store.read (wordBit table index)).toBool &&
          (store.read (.bitsGet measured index)).toBool) ^^ tail) =
      (fun index tail => ((store.read table).toNat.testBit index.val &&
        ((store.read measured).bitGet index).toBool) ^^ tail) := by
    funext index tail
    rw [wordBit_read]
    rfl
  rw [contribution]
  exact fold_filter (List.ofFn fun index : Fin width => index)
    ⟨(store.read table).toNat, (store.read table).toNat_lt⟩ (store.read measured)

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeParity
