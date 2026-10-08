/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.FinPow.BinaryBasis
import all QuantumAlg.Util.FinPow
import Mathlib.Data.Fin.Rev

/-!
# Binary coordinates of appended registers

The integer tensor-product label decodes to the original big-endian coordinates
of the left and right registers, in that order, including empty registers.
-/

namespace QuantumAlg.BinaryBasis

/-- The left physical segment decodes to precisely the original left binary label. -/
theorem bigEndianEquiv_prod_left {leftWidth rightWidth : Nat}
    (left : Fin (2 ^ leftWidth)) (right : Fin (2 ^ rightWidth)) (index : Fin leftWidth) :
    (bigEndianEquiv (leftWidth + rightWidth)).symm (prodEquiv (left, right))
        (Fin.castAdd rightWidth index) = (bigEndianEquiv leftWidth).symm left index := by
  simp only [bigEndianEquiv_symm_value]
  have position : (Fin.castAdd rightWidth index).rev.val = rightWidth + index.rev.val := by
    simp only [Fin.val_rev, Fin.val_castAdd]
    omega
  rw [position, prodEquiv_testBit_left]

/-- The right physical segment decodes to precisely the original right binary label. -/
theorem bigEndianEquiv_prod_right {leftWidth rightWidth : Nat}
    (left : Fin (2 ^ leftWidth)) (right : Fin (2 ^ rightWidth)) (index : Fin rightWidth) :
    (bigEndianEquiv (leftWidth + rightWidth)).symm (prodEquiv (left, right))
        (Fin.natAdd leftWidth index) = (bigEndianEquiv rightWidth).symm right index := by
  simp only [bigEndianEquiv_symm_value]
  have position : (Fin.natAdd leftWidth index).rev.val = index.rev.val := by
    simp only [Fin.val_rev, Fin.val_natAdd]
    omega
  rw [position, prodEquiv_testBit_right]

/-- Tensor-product integer labels preserve both original coordinate segments exactly. -/
theorem bigEndianEquiv_symm_prod {leftWidth rightWidth : Nat}
    (left : Fin (2 ^ leftWidth)) (right : Fin (2 ^ rightWidth)) :
    (bigEndianEquiv (leftWidth + rightWidth)).symm (prodEquiv (left, right)) =
      Fin.addCases ((bigEndianEquiv leftWidth).symm left)
        ((bigEndianEquiv rightWidth).symm right) := by
  funext index
  refine Fin.addCases (fun first => ?_) (fun last => ?_) index
  · simpa only [Fin.addCases_left] using bigEndianEquiv_prod_left left right first
  · simpa only [Fin.addCases_right] using bigEndianEquiv_prod_right left right last

end QuantumAlg.BinaryBasis
