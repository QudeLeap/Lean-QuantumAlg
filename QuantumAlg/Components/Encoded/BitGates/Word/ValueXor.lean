/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.Xor
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Components.Encoded.BitGates.StateEquality
import all QuantumAlg.Components.Encoded.BitGates.BitEquality

/-!
# Pointwise complete value characterization of actual quantum word copying

One fixed native CNOT word acts on actual quantum operands. For a basis
label with stated source bits, its complete output agrees with finite
target XOR by that mathematical value. This is a readout theorem, not
an input-dependent program constructor or a free constant-loading step.
-/

namespace QuantumAlg.EncodedBit.Word

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Complete arbitrary-target XOR follows from the actual retained source and target supports. -/
lemma xorIntoStep_eq_xorConstantStep (source target : Word encoding width)
    (separate : ∀ sourceIndex targetIndex,
      (source.bit sourceIndex).wire ≠ (target.bit targetIndex).wire)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (onto : Function.Surjective encoding.encode) (constant : Fin (2 ^ width)) (state : Data)
    (reads : ∀ index, (source.bit index).get state = constant.val.testBit index.val) :
    xorIntoStep source target (fun index => separate index index) state =
      xorConstantStep target constant state := by
  apply state_eq_of_get_eq onto
  intro observed
  have target_ne (other index : Fin width) (different : other ≠ index) :
      (target.bit other).wire ≠ (target.bit index).wire := fun same => different (distinct same)
  by_cases inside : observed.wire ∈ Set.range (fun index => (target.bit index).wire)
  · obtain ⟨index, location⟩ := inside
    have lenses := eq_of_wire_eq (target.bit index) observed location
    rw [← lenses]
    have actual := xorIntoStep_get_target source target (fun bit => separate bit bit) index
      (fun other different => target_ne other index different)
      (fun other => (separate index other).symm) state
    have expected := xorConstantStep_get_target target constant index
      (fun other different => target_ne other index different) state
    rw [reads] at actual
    exact actual.trans expected.symm
  · have outside : ∀ index, (target.bit index).wire ≠ observed.wire :=
      fun index same => inside ⟨index, same⟩
    exact (xorIntoStep_get_observed_of_target_ne source target (fun bit => separate bit bit)
      observed outside state).trans
        (xorConstantStep_get_observed_of_target_ne target constant observed outside state).symm

end

end QuantumAlg.EncodedBit.Word
