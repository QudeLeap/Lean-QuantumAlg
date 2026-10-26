/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Parity.Row.Character
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Parity.Row.Semantics

/-!
# Actual stored row constants expressed through the original measured mask

Each constant bit is the XOR of the real measured bits selected by its
static table column. The equality is proved from the paid native row's
actual final Store, so later phase selection cannot replace parity work
by a free mathematical callback.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.MaskParity

open Execution

noncomputable section

variable {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {wordWidth columns : Nat}

/-- Parity of the original mask positions selected by one actual static table word. -/
def maskValue (mask : CShape.Value (.bits wordWidth)) (constant : Fin (2 ^ wordWidth)) : Bool :=
  (Word.constantOneIndices constant).foldr
    (fun index tail => (mask.bitGet index).toBool ^^ tail) false

/-- Structural bit reads of the actual measured mask have precisely this selected parity. -/
lemma value_selectedInputs (measured : CInputRef ctx (.bits wordWidth))
    (constant : Fin (2 ^ wordWidth)) (store : Store ctx) :
    value (selectedInputs measured constant) store = maskValue (store.read measured) constant := by
  unfold value selectedInputs maskValue
  rw [List.foldr_map]
  rfl

/-- The original measured mask determines the ideal value of the actually computed row vector. -/
def rowConstant (table : Fin columns → Fin (2 ^ wordWidth))
    (mask : CShape.Value (.bits wordWidth)) : Fin (2 ^ columns) :=
  ⟨Nat.ofBits (fun index => maskValue mask (table index)), Nat.ofBits_lt_two_pow _⟩

/-- The real paid row Store selects the constant computed from its original measured mask. -/
lemma storedRowConstant_eq (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit)
    (distinct : Function.Injective (fun index => (parity index).key))
    (separate : ∀ index, (parity index).key ∉ measured.storageKeys)
    (table : Fin columns → Fin (2 ^ wordWidth)) (store : Store ctx) :
    storedConstant ((rowRecord (oracles := oracles) (services := services) measured parity table
      (List.ofFn fun index : Fin columns => index) store).1.read (rowInput parity)) =
      rowConstant table (store.read measured) := by
  unfold storedConstant rowConstant
  apply Fin.ext
  apply congrArg (fun bits : Fin columns → Bool => Nat.ofBits bits)
  funext index
  change (((rowRecord (oracles := oracles) (services := services) measured parity table
    (List.ofFn fun index : Fin columns => index) store).1).read
      (.storage (parity index).toCStorageRef)).toBool = _
  rw [rowRecord_read_parity measured parity distinct separate table _
    (List.nodup_ofFn_ofInjective (fun _ _ same => same)) index (List.mem_ofFn.mpr ⟨index, rfl⟩)]
  exact value_selectedInputs measured (table index) store

/-- Each actual row-constant bit is the original mask dot product with that table column. -/
lemma rowConstant_testBit (table : Fin columns → Fin (2 ^ wordWidth))
    (mask : CShape.Value (.bits wordWidth)) (index : Fin columns) :
    (rowConstant table mask).val.testBit index.val = maskValue mask (table index) :=
  Nat.testBit_ofBits_lt _ index.val index.isLt

end

end QuantumAlg.EncodedBit.WindowLookup.MaskParity
