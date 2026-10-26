/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.WordPair

/-!
# Full-frame preservation outside the target of a placed word operation

An operation that retains its first operand also retains every actual bit
outside its second operand. The proof covers bits inside the first operand
and every complementary wire, including arbitrary dirty workspace.
-/

namespace QuantumAlg.EncodedBit

noncomputable section

open BinaryLabelEncoding

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- An exact placed two-word action cannot alter any bit outside its target word. -/
lemma wordPairStep_get_of_target_ne (first second : Word encoding width)
    (firstDistinct : Function.Injective (fun index => (first.bit index).wire))
    (secondDistinct : Function.Injective (fun index => (second.bit index).wire))
    (separate : ∀ left right, (first.bit left).wire ≠ (second.bit right).wire)
    (onto : Function.Surjective encoding.encode)
    (action : (Fin (2 ^ width) × Fin (2 ^ width)) → Fin (2 ^ width) × Fin (2 ^ width))
    (preserves : ∀ pair, (action pair).1 = pair.1)
    (observed : EncodedBit encoding)
    (outsideTarget : ∀ index, (second.bit index).wire ≠ observed.wire) (state : Data) :
    observed.get
      (((wordPairSubsystem first second firstDistinct secondDistinct separate).full
        (prodEquiv (m := width) (n := width)).surjective onto).step
          (fun pair => (action pair.1, pair.2)) state) = observed.get state := by
  let placement := wordPairSubsystem first second firstDistinct secondDistinct separate
  let sourceOnto := (prodEquiv (m := width) (n := width)).surjective
  by_cases inside : observed.wire ∈ Set.range placement.wires
  · obtain ⟨wire, same⟩ := inside
    obtain ⟨selected, rfl⟩ := finSumFinEquiv.surjective wire
    cases selected with
    | inl index =>
        let sourceBit := prodLeftBit (finIdentity width) (finIdentity width)
          (finIdentityBit width index)
        have location : placement.wires sourceBit.wire = observed.wire := same
        have after := placement.full_step_source_read sourceOnto onto sourceBit observed
          location action state
        have before := placement.full_source_read sourceOnto onto sourceBit observed
          location state
        change observed.get _ = (finIdentityBit width index).get (action _).1 at after
        rw [preserves] at after
        exact after.trans before
    | inr index =>
        have location : (second.bit index).wire = observed.wire := by
          exact (wordPairSubsystem_right first second firstDistinct secondDistinct separate
            index).symm.trans same
        exact False.elim (outsideTarget index location)
  · exact placement.full_step_other_read sourceOnto onto observed inside action state

end

end QuantumAlg.EncodedBit
