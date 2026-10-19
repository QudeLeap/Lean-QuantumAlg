/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Util.Nat.FixedWidth

/-!
# Zero labels characterized by their actual physical-wire readouts

The identity encoding reads physical wires in big-endian order. Its zero
predicate agrees with the original numerical basis label, including the
empty word; the proof reuses finite-word bit extensionality.
-/

namespace QuantumAlg.BinaryLabelEncoding

/-- All actual readouts of a raw binary word vanish exactly at basis label zero. -/
lemma finIdentity_all_zero_iff (width : Nat) (label : Fin (2 ^ width)) :
    (∀ wire, (finIdentityBit width wire).get label = false) ↔ label = 0 := by
  constructor
  · intro allZero
    apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    have actual := allZero bit.rev
    change label.val.testBit (WireAddress.bitIndex bit.rev).val = false at actual
    have position : (WireAddress.bitIndex bit.rev).val = bit.val := by
      dsimp [WireAddress.bitIndex, Fin.rev]
      omega
    rw [position] at actual
    simpa only [Fin.val_zero, Nat.zero_testBit] using actual
  · rintro rfl wire
    change (0 : Nat).testBit (WireAddress.bitIndex wire).val = false
    exact Nat.zero_testBit _

end QuantumAlg.BinaryLabelEncoding
