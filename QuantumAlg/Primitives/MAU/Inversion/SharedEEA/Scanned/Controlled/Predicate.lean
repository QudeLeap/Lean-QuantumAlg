/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Frame
import all QuantumAlg.Components.Encoded.BitGates.Dirty.Predicate

/-! # Full source-state identities for an actual externally selected predicate flip -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledFrame

noncomputable section

open EncodedBit

/-- A genuine source predicate flip retains both original external coordinates. -/
lemma source_predicateFlip (width : Nat) (bit : EncodedBit (Scanned.encoding width))
    (predicate : Scanned.Data width → Bool) (state : Data width) :
    predicateFlip (sourceBit width bit) (fun value => predicate value.1) state =
      (predicateFlip bit predicate state.1, state.2) := by
  unfold predicateFlip
  split <;> rfl

/-- External false is full identity without a nonzero, phase, metadata or work-value premise. -/
lemma selected_predicateFlip (width : Nat) (bit : EncodedBit (Scanned.encoding width))
    (predicate : Scanned.Data width → Bool) (state : Data width) :
    predicateFlip (sourceBit width bit) (fun value => value.2.1 && predicate value.1) state =
      (if state.2.1 then predicateFlip bit predicate state.1 else state.1, state.2) := by
  cases selected : state.2.1 <;> cases enabled : predicate state.1 <;>
    simp only [predicateFlip, selected, enabled, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, if_false, if_true, sourceBit_flip]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledFrame
