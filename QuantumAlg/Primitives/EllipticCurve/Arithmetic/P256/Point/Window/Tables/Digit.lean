/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Tables.Selection
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Effect
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Address.Zero

/-!
# The genuine whole-digit selector and the original complete group-table row

The same top bit and every original current address bit determine both
the arithmetic enable and the full table row. Thus the original all-zero
digit is exactly identity row zero, including an empty address suffix.
No pool or arithmetic admission is needed for these original readouts.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Tables

noncomputable section

open EncodedBit.WindowLookup

/-- Full original row zero is precisely the genuine all-zero current digit. -/
lemma selectedRow_zero_iff (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) (state : Raw) :
    (selectedRow stream width bounded state).val = 0 ↔
      ∀ index, (Enable.digitBit stream width bounded index).get state = false := by
  change
    ((selector stream width bounded).addressLabelAt width 0 (by omega) 0 (by omega) state).val +
      (if (streamBit stream).get state then 2 ^ width else 0) = 0 ↔ _
  rw [Nat.add_eq_zero_iff, SelectorFrame.addressLabelAt_zero_iff]
  constructor
  · rintro ⟨addressZero, topZero⟩
    have root : (streamBit stream).get state = false := by
      apply Bool.eq_false_iff.mpr
      intro selected
      rw [if_pos selected] at topZero
      have positive := Nat.two_pow_pos width
      omega
    intro index
    refine Fin.cases root (fun address => ?_) index
    exact addressZero address
  · intro allZero
    refine ⟨fun address => allZero address.succ, ?_⟩
    have root : (streamBit stream).get state = false := allZero 0
    rw [root]
    rfl

/-- The real ordinary arithmetic enable is true exactly at the nonidentity full table rows. -/
lemma querySelected_ordinary_iff (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Raw) :
    QueryInsertion.querySelected stream width bounded false state = true ↔
      (selectedRow stream width bounded state).val ≠ 0 := by
  rw [ne_eq, selectedRow_zero_iff]
  simp [QueryInsertion.querySelected]

end

end Tables

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
