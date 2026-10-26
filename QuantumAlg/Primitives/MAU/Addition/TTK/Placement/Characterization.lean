/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Placement
import all QuantumAlg.Components.Encoded.BitGates.StateEquality
import all QuantumAlg.Components.Encoded.BitGates.BitEquality

/-!
# Complete target-and-complement characterization of placed actual TTK arithmetic

The target readouts give the exact finite modular sum. Equality of all
other original physical readouts then determines the complete result,
without unfolding a concrete frame or enumerating its basis labels.
-/

namespace QuantumAlg.MAU.Addition.TTK.WordPlacement

noncomputable section

open EncodedBit

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Exact target arithmetic and the entire retained complement determine the full output. -/
lemma step_eq_of_target_complement (placement : WordPlacement encoding width)
    (state output : Data) (addend target : BitVec width)
    (addendReads : ∀ index, (placement.addend.bit index).get state = addend.getMsbD index.val)
    (targetReads : ∀ index, (placement.target.bit index).get state = target.getMsbD index.val)
    (outputReads : ∀ index, (placement.target.bit index).get output =
      (addend + target).getMsbD index.val)
    (outsideReads : ∀ observed : EncodedBit encoding,
      (∀ index, (placement.target.bit index).wire ≠ observed.wire) →
      observed.get output = observed.get state) :
    placement.step state = output := by
  apply state_eq_of_get_eq placement.onto
  intro observed
  by_cases inside : ∃ index, (placement.target.bit index).wire = observed.wire
  · obtain ⟨index, same⟩ := inside
    have lenses : placement.target.bit index = observed := eq_of_wire_eq _ _ same
    rw [← lenses]
    exact (placement.step_target_get state addend target addendReads targetReads index).trans
      (outputReads index).symm
  · have outside : ∀ index, (placement.target.bit index).wire ≠ observed.wire := by
      intro index same
      exact inside ⟨index, same⟩
    exact (placement.step_get_of_target_ne state observed outside).trans
      (outsideReads observed outside).symm

end

end QuantumAlg.MAU.Addition.TTK.WordPlacement
