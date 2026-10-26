/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Barrel
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor.Action

/-! # Complete native barrel commutation with the original independent complement -/

namespace QuantumAlg.EncodedBit.PermutationBarrel

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {size controls : Nat}

/-- An original flip outside both the complete word and all controls commutes with every stage. -/
lemma gates_flip_outside (barrel : PermutationBarrel encoding size controls)
    (permutation : Equiv.Perm (Fin size)) (stages : List (Fin controls × Nat))
    (observed : EncodedBit encoding)
    (outside : ∀ index, (barrel.bit index).wire ≠ observed.wire)
    (separate : ∀ index, observed.wire ≠ (barrel.control index).wire) (state : Data) :
    GateSpec.stepList (barrel.gates permutation stages) (observed.flip state) =
      observed.flip (GateSpec.stepList (barrel.gates permutation stages) state) := by
  induction stages generalizing state with
  | nil => rfl
  | cons stage rest ih =>
      simp only [gates, stageGates, GateSpec.stepList_append]
      have first := (barrel.frame stage.1).gates_flip_outside
        (Permutation.transpositions (permutation ^ stage.2)) observed outside (separate stage.1)
        state
      rw [first, ih]

/-- Any finite output word outside the native barrel's complete read/write support commutes. -/
lemma gates_xorConstantStep_comm (barrel : PermutationBarrel encoding size controls)
    (permutation : Equiv.Perm (Fin size)) (stages : List (Fin controls × Nat)) {width : Nat}
    (output : Word encoding width) (constant : Fin (2 ^ width))
    (outside : ∀ bit index, (barrel.bit index).wire ≠ (output.bit bit).wire)
    (separate : ∀ bit index, (output.bit bit).wire ≠ (barrel.control index).wire) (state : Data) :
    GateSpec.stepList (barrel.gates permutation stages)
        (Word.xorConstantStep output constant state) =
      Word.xorConstantStep output constant
        (GateSpec.stepList (barrel.gates permutation stages) state) :=
  Word.action_xorConstantStep_comm _ output constant
    (fun bit state => barrel.gates_flip_outside permutation stages (output.bit bit)
      (outside bit) (separate bit) state) state

end

end QuantumAlg.EncodedBit.PermutationBarrel
