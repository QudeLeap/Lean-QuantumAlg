/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Clip.Latch
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Difference.Readout
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Difference.Frame

/-! # Exact original low operands and borrow retained by the actual activation word -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthClip

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The low address excludes the genuine high activation position at every metadata width. -/
lemma activeGates_low_address (width : Nat) (state : Data width) :
    LengthDifference.value width width.size false
        (GateSpec.stepList (activeGates width) state) =
      LengthDifference.value width width.size false state := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  let fits : width.size ≤ ScanMetadata.addressWidth width := by
    unfold ScanMetadata.addressWidth
    omega
  have actual := activeGates_get_observed width state
    (addressBit width (LengthDifference.index width width.size fits ⟨index, within⟩))
    (by
      apply address_address_ne
      intro same
      have values := congrArg Fin.val same
      change 0 = ScanMetadata.addressWidth width - width.size + index at values
      unfold ScanMetadata.addressWidth at values
      omega)
  change ((LengthDifference.word width width.size fits false).bit ⟨index, within⟩).get
      (GateSpec.stepList (activeGates width) state) =
    ((LengthDifference.word width width.size fits false).bit ⟨index, within⟩).get state at actual
  simpa only [LengthDifference.word_get] using actual

/-- All low prefix operands retain their exact incoming value while high address is activated. -/
lemma activeGates_low_prefix (width : Nat) (state : Data width) :
    LengthDifference.value width width.size true
        (GateSpec.stepList (activeGates width) state) =
      LengthDifference.value width width.size true state := by
  unfold LengthDifference.value
  rw [activeGates_prefix]
  rfl

/-- The existing conjunction stays unchanged before the real subtraction writes its borrow. -/
lemma activeGates_conjunction (width : Nat) (state : Data width) :
    (GateSpec.stepList (activeGates width) state).2.2.2 = state.2.2.2 :=
  activeGates_get_observed width state (conjunctionBit width) (address_conjunction_ne width _)

/-- The genuine high address position is zero exactly below the low-word capacity. -/
lemma active_zero_of_lt (width : Nat) (state : Data width)
    (fits : state.2.1.toNat < 2 ^ width.size) :
    (LengthCopy.active width true).get state = false := by
  change state.2.1.getMsbD 0 = false
  rw [high_get]
  exact decide_eq_false (Nat.not_le_of_gt fits)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthClip
