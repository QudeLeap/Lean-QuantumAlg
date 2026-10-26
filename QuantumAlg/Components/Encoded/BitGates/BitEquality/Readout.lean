/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.BitEquality

/-!
# Complete encoded bit lenses from their readouts

For a full binary encoding, equal readouts imply equal physical positions.
A zero label and one symbolic flip distinguish any two different wires.
This gives a dimension-independent lens equality without normalizing a
concrete placement or constructing its exponentially large basis space.
-/

namespace QuantumAlg.EncodedBit

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- All complete-label readouts determine the original physical wire. -/
lemma wire_eq_of_get_eq (onto : Function.Surjective encoding.encode)
    (first second : EncodedBit encoding) (reads : ∀ state, first.get state = second.get state) :
    first.wire = second.wire := by
  by_contra different
  obtain ⟨zero, encoded⟩ := onto ⟨0, Nat.two_pow_pos encoding.width⟩
  have firstZero : first.get zero = false := by
    rw [← first.get_eq, encoded]
    exact Nat.zero_testBit _
  have secondZero : second.get zero = false := by
    rw [← second.get_eq, encoded]
    exact Nat.zero_testBit _
  have distinctReads := reads (first.flip zero)
  rw [get_flip_self, firstZero, get_flip_of_wire_ne first second different, secondZero]
    at distinctReads
  contradiction

/-- Readout equality fixes both flips and reads of a complete encoded bit. -/
lemma eq_of_get_eq (onto : Function.Surjective encoding.encode)
    (first second : EncodedBit encoding) (reads : ∀ state, first.get state = second.get state) :
    first = second :=
  eq_of_wire_eq first second (wire_eq_of_get_eq onto first second reads)

end

end QuantumAlg.EncodedBit
