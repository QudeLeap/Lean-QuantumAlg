/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Basic

/-! # A complete encoded semantic bit is determined by its actual wire -/

namespace QuantumAlg.EncodedBit

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- Equal original wire positions have equal readouts, flips, and complete semantic lenses. -/
lemma eq_of_wire_eq (first second : EncodedBit encoding) (same : first.wire = second.wire) :
    first = second := by
  have reads : first.get = second.get := by
    funext state
    rw [← first.get_eq, ← second.get_eq, same]
  have flips : first.flip = second.flip := by
    funext state
    apply encoding.encode_injective
    rw [first.encode_flip, second.encode_flip, same]
  cases first
  cases second
  cases same
  cases reads
  cases flips
  rfl

end

end QuantumAlg.EncodedBit
