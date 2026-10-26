/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Gates
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Fiber

/-!
# Original word labels under a complete physical placement

Placing each original bit transports its finite XOR and mathematical
word setter through the same full grouping. Both proofs keep word width
abstract and preserve every other field of the original complete label.
-/

namespace QuantumAlg.EncodedBit.FullPlacement

noncomputable section

variable {Source Target : Type} {source : BinaryLabelEncoding Source}
    {target : BinaryLabelEncoding Target} (placement : FullPlacement source target) {width : Nat}

/-- All original word bits follow their actual complete physical placement. -/
def placeWord (word : Word source width) : Word target width :=
  ⟨fun index => placement.placeBit (word.bit index)⟩

lemma grouping_xorConstantStep (word : Word source width) (constant : Fin (2 ^ width))
    (state : Target) :
    placement.grouping (Word.xorConstantStep (placement.placeWord word) constant state) =
      Word.xorConstantStep word constant (placement.grouping state) := by
  rw [Word.xorConstantStep_eq_indicesStep, Word.xorConstantStep_eq_indicesStep]
  have fold (indices : List (Fin width)) (state : Target) :
      placement.grouping
        (Word.xorConstantIndicesStep (placement.placeWord word) indices state) =
      Word.xorConstantIndicesStep word indices (placement.grouping state) := by
    induction indices generalizing state with
    | nil => rfl
    | cons index rest ih =>
        change placement.grouping
          (Word.xorConstantIndicesStep (placement.placeWord word) rest
            ((placement.placeBit (word.bit index)).flip state)) =
          Word.xorConstantIndicesStep word rest ((word.bit index).flip (placement.grouping state))
        simpa only [placeBit, Equiv.apply_symm_apply] using
          ih ((placement.placeBit (word.bit index)).flip state)
  exact fold _ state

/-- The complete ordinary word setter commutes with its literal physical grouping. -/
lemma grouping_resultSetConstant (word : Word source width) (value : Fin (2 ^ width))
    (state : Target) :
    placement.grouping
        (WindowLookup.resultSetConstant (placement.placeWord word) value state) =
      WindowLookup.resultSetConstant word value (placement.grouping state) := by
  unfold WindowLookup.resultSetConstant
  exact placement.grouping_xorConstantStep word _ state

/-- The same equality in the original complete target-label coordinates. -/
lemma resultSetConstant_placeWord (word : Word source width) (value : Fin (2 ^ width))
    (state : Target) :
    WindowLookup.resultSetConstant (placement.placeWord word) value state =
      placement.grouping.symm
        (WindowLookup.resultSetConstant word value (placement.grouping state)) := by
  apply placement.grouping.injective
  rw [placement.grouping_resultSetConstant, Equiv.apply_symm_apply]

end

end QuantumAlg.EncodedBit.FullPlacement
