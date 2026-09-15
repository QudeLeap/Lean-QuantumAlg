/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.FinPow
import Mathlib.Logic.Equiv.Defs

/-!
# Big-endian finite binary coordinates

The first coordinate is the most significant bit. The explicit equivalence
connects a vector of two-valued coordinates to its existing finite binary
label, without changing the wire order or introducing padding coordinates.
-/

namespace QuantumAlg.BinaryBasis

/-- Encode finite binary coordinates in the library's big-endian order. -/
def bigEndianEquiv (width : Nat) : (Fin width → Fin 2) ≃ Fin (2 ^ width) where
  toFun basis := ⟨Nat.ofBits (fun index => finTwoEquiv (basis index.rev)),
    Nat.ofBits_lt_two_pow _⟩
  invFun label := fun index => finTwoEquiv.symm (label.val.testBit index.rev.val)
  left_inv basis := by
    funext index
    apply finTwoEquiv.injective
    simp only [Equiv.apply_symm_apply]
    rw [Nat.testBit_ofBits_lt]
    · exact congrArg (fun position => finTwoEquiv (basis position)) (Fin.rev_rev index)
    · exact index.rev.isLt
  right_inv label := by
    apply Fin.val_injective
    change Nat.ofBits (fun index : Fin width =>
      finTwoEquiv (finTwoEquiv.symm (label.val.testBit index.rev.rev.val))) = label.val
    simp only [Equiv.apply_symm_apply, Fin.rev_rev, Nat.ofBits_testBit,
      Nat.mod_eq_of_lt label.isLt]

/-- The logical wire index selects the corresponding most-significant-first bit. -/
theorem bigEndianEquiv_bit (width : Nat) (basis : Fin width → Fin 2) (index : Fin width) :
    (bigEndianEquiv width basis).val.testBit index.rev.val = finTwoEquiv (basis index) := by
  change (Nat.ofBits fun position : Fin width => finTwoEquiv (basis position.rev)).testBit
    index.rev.val = finTwoEquiv (basis index)
  rw [Nat.testBit_ofBits_lt]
  · exact congrArg (fun position => finTwoEquiv (basis position)) (Fin.rev_rev index)
  · exact index.rev.isLt

/-- Decoding a label yields the original finite value on every logical wire. -/
theorem bigEndianEquiv_symm_value (width : Nat) (label : Fin (2 ^ width))
    (index : Fin width) :
    (bigEndianEquiv width).symm label index =
      finTwoEquiv.symm (label.val.testBit index.rev.val) := rfl

end QuantumAlg.BinaryBasis
