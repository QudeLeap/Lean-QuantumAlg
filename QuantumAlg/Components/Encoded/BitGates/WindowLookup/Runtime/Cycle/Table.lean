/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Cycle.Circuit
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Row.Store

/-!
# Identical stored words in the actual loader and paid feedback table

Both reads use the original array and complete joined high/low address.
The unsigned-word value is the same finite word in both representations.
This equality supplies a concrete same-table graph without a table-value
assumption or a transformed source array.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeTable

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum} {wordWidth lowWidth highRemaining : Nat}

/-- Every actual feedback row reads precisely the word selected by the original loader. -/
lemma splitInputs_readTable (source : CInputRef ctx
    (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord wordWidth)))
    (store : Store ctx) :
    (fun top high => RuntimeRow.readTable (splitInputs source top high) store) =
      splitTable (tableValue (store.read source)) := by
  funext top high low
  change RuntimeRow.readTable (splitInputs source top high) store low =
    tableValue (store.read source) top (joinedAddress high low)
  rw [tableValue_read]
  change (⟨(store.read (.vectorGet source (index top (joinedAddress high low)))).toNat,
    (store.read (.vectorGet source (index top (joinedAddress high low)))).toNat_lt⟩ :
      Fin (2 ^ wordWidth)) =
    wordEncoding (store.read (.vectorGet source (index top (joinedAddress high low))))
  cases store.read (.vectorGet source (index top (joinedAddress high low)))
  rfl

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeTable
