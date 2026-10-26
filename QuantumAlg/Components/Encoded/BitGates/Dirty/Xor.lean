/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Dirty.Predicate

/-! # Exact composition of two retained-predicate toggles on the same physical output -/

namespace QuantumAlg.EncodedBit

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- Sequential actual toggles combine by XOR when the second predicate ignores the output. -/
lemma predicateFlip_comp (target : EncodedBit encoding) (first second : Data → Bool)
    (stable : ∀ state, second (target.flip state) = second state) (state : Data) :
    predicateFlip target second (predicateFlip target first state) =
      predicateFlip target (fun value => first value ^^ second value) state := by
  cases firstValue : first state <;> cases secondValue : second state <;>
    simp only [predicateFlip, firstValue, secondValue, Bool.false_eq_true, if_false,
      if_true, stable, flip_flip, Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true]

end

end QuantumAlg.EncodedBit
