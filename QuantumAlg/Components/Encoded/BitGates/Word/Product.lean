/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Fiber
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding

/-!
# Complete word labels in a product encoding

Original word bits act only on their original component. Finite XOR and
the mathematical word setter therefore keep the entire other component,
with both register widths and all values left abstract.
-/

namespace QuantumAlg.EncodedBit.Word

noncomputable section

variable {Data Extra : Type} {encoding : BinaryLabelEncoding Data}
    (extra : BinaryLabelEncoding Extra) {width : Nat}

/-- The original word occupies the same left component of the complete product. -/
def onProductLeft (word : Word encoding width) :
    Word (BinaryLabelEncoding.prod encoding extra) width :=
  ⟨fun index => BinaryLabelEncoding.prodLeftBit encoding extra (word.bit index)⟩

/-- Every original finite XOR leaves the complete other component unchanged. -/
lemma xorConstantStep_onProductLeft (word : Word encoding width) (constant : Fin (2 ^ width))
    (state : Data) (other : Extra) :
    xorConstantStep (onProductLeft extra word) constant (state, other) =
      (xorConstantStep word constant state, other) := by
  rw [xorConstantStep_eq_indicesStep, xorConstantStep_eq_indicesStep]
  have fold (indices : List (Fin width)) (state : Data) :
      xorConstantIndicesStep (onProductLeft extra word) indices (state, other) =
        (xorConstantIndicesStep word indices state, other) := by
    induction indices generalizing state with
    | nil => rfl
    | cons index rest ih =>
        change xorConstantIndicesStep (onProductLeft extra word) rest
            ((word.bit index).flip state, other) =
          (xorConstantIndicesStep word rest ((word.bit index).flip state), other)
        exact ih _
  exact fold _ state

/-- The same full-label setter keeps every original coordinate in the other component. -/
lemma resultSetConstant_onProductLeft (word : Word encoding width) (value : Fin (2 ^ width))
    (state : Data) (other : Extra) :
    WindowLookup.resultSetConstant (onProductLeft extra word) value (state, other) =
      (WindowLookup.resultSetConstant word value state, other) := by
  unfold WindowLookup.resultSetConstant
  exact xorConstantStep_onProductLeft extra word _ state other

end

end QuantumAlg.EncodedBit.Word
