/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-! # Actual native conjunction with one negative quantum control -/

namespace QuantumAlg.EncodedBit.GateSpec

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- The negative control is flipped, used by one real Toffoli, and restored. -/
def negativeConjunction (positive negative target : EncodedBit encoding)
    (controls : positive.wire ≠ negative.wire) (first : positive.wire ≠ target.wire)
    (second : negative.wire ≠ target.wire) : List (GateSpec encoding) :=
  [.x negative, .toffoli positive negative target controls first second, .x negative]

/-- Every caller coordinate except the selected target is retained by the actual gate word. -/
lemma negativeConjunction_step (positive negative target : EncodedBit encoding)
    (controls : positive.wire ≠ negative.wire) (first : positive.wire ≠ target.wire)
    (second : negative.wire ≠ target.wire) (state : Data) :
    stepList (negativeConjunction positive negative target controls first second) state =
      if positive.get state && !negative.get state then target.flip state else state := by
  change negative.flip (toffoliStep positive negative target (negative.flip state)) = _
  rw [toffoliStep, get_flip_of_wire_ne negative positive controls.symm,
    get_flip_self]
  split
  · rw [flip_comm negative target, flip_flip]
  · exact flip_flip negative state

end

end QuantumAlg.EncodedBit.GateSpec
