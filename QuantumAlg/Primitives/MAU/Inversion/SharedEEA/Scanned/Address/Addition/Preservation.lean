/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Address.Addition.Values
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Registers.BitExt
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.WordPair.Preservation

/-!
# Complete restoration by the actual address adder

The complete source frame and the entire prefix/conjunction workspace are
retained on every finite label. In particular the explicit high padding bit
is restored even when dirty; only the actual address changes.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.AddressAddition

noncomputable section

open EncodedBit NumberTheory.SharedEEA

private lemma step_observed (width : Nat) (state : Data width)
    (bit : EncodedBit (encoding width))
    (outside : ∀ index, (addressBit width index).wire ≠ bit.wire) :
    bit.get (step width state) = bit.get state :=
  wordPairStep_get_of_target_ne (source width) (AddressCopy.target width) _ _ _
    (encoding_surjective width) Addition.TTK.lowOutput (fun _ => rfl) bit outside state

/-- No original source field is changed by the actual full-carry address addition. -/
lemma step_source (width : Nat) (state : Data width) :
    (step width state).1 = state.1 := by
  apply Registers.eq_of_bit_get_eq
  intro bit
  exact step_observed width state (sourceBit width bit)
    (fun index => (source_address_ne width bit index).symm)

/-- All prefix bits survive the native adder, including its high padding source. -/
lemma step_prefix (width : Nat) (state : Data width) :
    (step width state).2.2.1 = state.2.2.1 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  simpa only [prefixBit_get] using
    step_observed width state (prefixBit width ⟨index, within⟩)
      (fun other => address_prefix_ne width other ⟨index, within⟩)

/-- The separate conjunction bit is physically outside the actual target word. -/
lemma step_conjunction (width : Nat) (state : Data width) :
    (step width state).2.2.2 = state.2.2.2 :=
  step_observed width state (conjunctionBit width) (address_conjunction_ne width)

/-- Complete all-label semantics expose the actual arithmetic and every restored field. -/
lemma step_eq (width : Nat) (state : Data width) :
    step width state = (state.1, (value width state + state.2.1, state.2.2)) :=
  Prod.ext (step_source width state)
    (Prod.ext (step_address width state)
      (Prod.ext (step_prefix width state) (step_conjunction width state)))

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.AddressAddition
