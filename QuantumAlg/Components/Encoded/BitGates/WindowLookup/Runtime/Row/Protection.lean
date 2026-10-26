/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Row.Store

/-!
# Storage framing for actual runtime table rows

This proof-only record states which existing caller cells a paid parity
row may overwrite. It does not select a circuit or restrict quantum data,
references or environments. The actual programs remain defined and execute
without this record; their original-table interpretation uses these key laws.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeRow

open Execution

variable {ctx : RuntimeCtx .quantum} {wordWidth columns : Nat} {Rows : Type}

/-- Exact caller storage separation needed to preserve all runtime table and measured-mask reads. -/
structure Protection (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (table : Rows → Fin columns → CInputRef ctx (.unsignedWord wordWidth)) : Prop where
  parityDistinct : Function.Injective (fun index => (parity index).key)
  temporaryDifferent : ∀ index, (parity index).key ≠ temporary.key
  maskFree : ∀ index, (parity index).key ∉ measured.storageKeys
  temporaryMaskFree : temporary.key ∉ measured.storageKeys
  tableFree : ∀ index row column, (parity index).key ∉ (table row column).storageKeys
  temporaryTableFree : ∀ row column, temporary.key ∉ (table row column).storageKeys

/-- Restrict the same real protected table inputs to a selected family of rows. -/
lemma Protection.reindex {Rows' : Type} {measured : CInputRef ctx (.bits wordWidth)}
    {parity : Fin columns → CWriteRef ctx .bit} {temporary : CWriteRef ctx .bit}
    {table : Rows → Fin columns → CInputRef ctx (.unsignedWord wordWidth)}
    (protection : Protection measured parity temporary table) (rows : Rows' → Rows) :
    Protection measured parity temporary (fun row => table (rows row)) :=
  ⟨protection.parityDistinct, protection.temporaryDifferent, protection.maskFree,
    protection.temporaryMaskFree, fun index row => protection.tableFree index (rows row),
    fun row => protection.temporaryTableFree (rows row)⟩

end QuantumAlg.EncodedBit.WindowLookup.RuntimeRow
