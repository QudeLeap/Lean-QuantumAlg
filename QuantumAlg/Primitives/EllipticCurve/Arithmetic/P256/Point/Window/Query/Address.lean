/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Unlookup
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Cycle.Address
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Observation

/-!
# Same complete original address in each real point-query direction

The full loader and the split measured unlookup share the same top control
and every actual high/low address position. The proof preserves numerical
bit order and covers arbitrary original high/low widths, including zero.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryInsertion

noncomputable section

open EncodedBit.WindowLookup

/-- Actual point-frame wire positions discharge the complete split-address certificate. -/
lemma addressSplit (stream : Fin 2) (port : WordPort) (highRemaining lowWidth : Nat)
    (bounded : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8) :
    AddressSplit (selector stream (highRemaining + lowWidth) bounded)
      (unlookup stream port highRemaining lowWidth bounded lowBound).high
      (unlookup stream port highRemaining lowWidth bounded lowBound).low where
  root := rfl
  highWires _ := rfl
  lowWires index := by
    have within := index.isLt
    have reversed := index.rev.isLt
    change (addressBit ⟨highRemaining + index.rev.val, by omega⟩).wire =
      (addressBit ⟨highRemaining + lowWidth - 1 - index.val, by omega⟩).wire
    apply congrArg (fun position : Fin 15 => (addressBit position).wire)
    apply Fin.ext
    simp only [Fin.val_rev]
    omega

/-- The paid feedback table and original loader select the same complete physical address. -/
lemma tableAt_eq_lookup (stream : Fin 2) (port : WordPort)
    (highRemaining lowWidth : Nat) (bounded : highRemaining + lowWidth ≤ 15)
    (lowBound : lowWidth ≤ 8)
    (table : Bool → Fin (2 ^ (highRemaining + lowWidth)) → Fin (2 ^ 256)) (state : Raw) :
    (unlookup stream port highRemaining lowWidth bounded lowBound).tableAt
      (splitTable table) state =
      table (((selector stream (highRemaining + lowWidth) bounded).stack ⟨0, by omega⟩).get state)
        ((selector stream (highRemaining + lowWidth) bounded).addressLabelAt
          (highRemaining + lowWidth) 0 (by omega) 0 (by omega) state) := by
  have same := addressSplit stream port highRemaining lowWidth bounded lowBound
  dsimp only [UnlookupFrame.tableAt, splitTable]
  rw [← same.root_get state, ← same.addressLabel state]

end

end QueryInsertion

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
