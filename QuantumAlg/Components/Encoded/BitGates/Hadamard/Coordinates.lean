/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Util.FinPow.BinaryBasis
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Prod

/-!
# The actual target wire and its remaining binary coordinates

The split reads one original wire and retains every other original wire in
place. Its inverse inserts that value at the same position; no basis is
chosen from a cardinality argument.
-/

namespace QuantumAlg.EncodedBit

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- The untouched coordinates retain their original physical positions. -/
abbrev RemainingRegister (target : EncodedBit encoding) : Register where
  Index := {wire : Fin encoding.width // wire ≠ target.wire} → Fin 2
  fintype := inferInstance
  decEq := inferInstance

/-- Split a full binary label into the actual target and the remaining wires. -/
def targetBasisEquiv (target : EncodedBit encoding) :
    (Qubits encoding.width).Index ≃
      (Register.prod (Qubits 1) target.RemainingRegister).Index :=
  (BinaryBasis.bigEndianEquiv encoding.width).symm |>.trans
    (Equiv.funSplitAt target.wire (Fin 2))

/-- The first coordinate is precisely the encoded target value. -/
theorem targetBasisEquiv_first (target : EncodedBit encoding) (state : Data) :
    (target.targetBasisEquiv (encoding.encode state)).1 =
      finTwoEquiv.symm (target.get state) := by
  change finTwoEquiv.symm
    ((encoding.encode state).val.testBit target.wire.rev.val) = _
  have address : target.wire.rev = WireAddress.bitIndex target.wire := by
    apply Fin.ext
    dsimp [Fin.rev, WireAddress.bitIndex]
    omega
  rw [address, target.get_eq]

/-- Flipping the target toggles just the first coordinate of the same split. -/
theorem targetBasisEquiv_flip (target : EncodedBit encoding) (state : Data) :
    target.targetBasisEquiv (encoding.encode (target.flip state)) =
      (finTwoEquiv.symm (!target.get state),
        (target.targetBasisEquiv (encoding.encode state)).2) := by
  apply Prod.ext
  · rw [targetBasisEquiv_first, get_flip_self]
  · funext wire
    change finTwoEquiv.symm
        ((encoding.encode (target.flip state)).val.testBit wire.val.rev.val) =
      finTwoEquiv.symm ((encoding.encode state).val.testBit wire.val.rev.val)
    have address : wire.val.rev = WireAddress.bitIndex wire.val := by
      apply Fin.ext
      dsimp [Fin.rev, WireAddress.bitIndex]
      omega
    rw [target.encode_flip, address, WireAddress.bit_flipBit_of_ne wire.property.symm]

/-- Equal complementary coordinates give exactly the two target-bit possibilities. -/
theorem targetBasisEquiv_fiber (target : EncodedBit encoding) (state : Data)
    (label : (Qubits encoding.width).Index)
    (same : (target.targetBasisEquiv label).2 =
      (target.targetBasisEquiv (encoding.encode state)).2) :
    label = encoding.encode state ∨ label = encoding.encode (target.flip state) := by
  have binary (left right : Fin 2) :
      left = right ∨ left = finTwoEquiv.symm (!finTwoEquiv right) := by
    fin_cases left <;> fin_cases right <;> decide
  rcases binary (target.targetBasisEquiv label).1
      (finTwoEquiv.symm (target.get state)) with original | flipped
  · left
    apply target.targetBasisEquiv.injective
    apply Prod.ext
    · exact original.trans (target.targetBasisEquiv_first state).symm
    · exact same
  · right
    apply target.targetBasisEquiv.injective
    rw [targetBasisEquiv_flip]
    apply Prod.ext
    · simpa only [Equiv.apply_symm_apply] using flipped
    · exact same

end

end QuantumAlg.EncodedBit
