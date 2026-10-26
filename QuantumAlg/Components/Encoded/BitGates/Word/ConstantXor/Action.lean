/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor

/-! # Complete finite-word commutation from its actual original bit flips -/

namespace QuantumAlg.EncodedBit.Word

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Commutation with each original output flip gives commutation with its finite XOR mask. -/
lemma action_xorConstantStep_comm (action : Data → Data) (output : Word encoding width)
    (constant : Fin (2 ^ width))
    (commute : ∀ bit state, action ((output.bit bit).flip state) =
      (output.bit bit).flip (action state)) (state : Data) :
    action (xorConstantStep output constant state) =
      xorConstantStep output constant (action state) := by
  rw [xorConstantStep_eq_indicesStep]
  have commutes (indices : List (Fin width)) (state : Data) :
      action (xorConstantIndicesStep output indices state) =
        xorConstantIndicesStep output indices (action state) := by
    induction indices generalizing state with
    | nil => rfl
    | cons bit rest ih =>
        change action (xorConstantIndicesStep output rest ((output.bit bit).flip state)) = _
        rw [ih, commute]
        rfl
  exact commutes _ state

end

end QuantumAlg.EncodedBit.Word
