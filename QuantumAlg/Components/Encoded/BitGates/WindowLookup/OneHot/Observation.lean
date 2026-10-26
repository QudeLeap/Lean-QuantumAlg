/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.OneHot.Program

/-!
# Complete spectator readout preservation by actual unary preparation

Only the supplied unary target systems are changed. Every original readout
outside that entire supplied target range survives the initial native X and
all doubling stages, independently of any clean initialization promise.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.UnaryFrame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Every actual remaining unary stage preserves an arbitrary readout outside all targets. -/
lemma stagesStepAt_observed (frame : UnaryFrame encoding width) (observed : EncodedBit encoding)
    (outside : ∀ index, (frame.target index).wire ≠ observed.wire)
    (remaining depth : Nat) (fits : depth + remaining = width) (state : Data) :
    observed.get (frame.stagesStepAt remaining depth fits state) = observed.get state := by
  induction remaining generalizing depth state with
  | zero => rfl
  | succ remaining ih =>
      dsimp only [stagesStepAt]
      rw [ih]
      exact (frame.stage depth (by omega)).observed_get observed
        (fun _ => outside _) (fun _ => outside _) state

/-- The seed X and every actual unary stage preserve all original external readouts. -/
lemma step_observed (frame : UnaryFrame encoding width) (observed : EncodedBit encoding)
    (outside : ∀ index, (frame.target index).wire ≠ observed.wire) (state : Data) :
    observed.get (frame.step state) = observed.get state := by
  unfold step
  rw [frame.stagesStepAt_observed observed outside]
  exact EncodedBit.get_flip_of_wire_ne _ _ (outside _) state

end

end QuantumAlg.EncodedBit.WindowLookup.UnaryFrame
