/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.GroupTheory.Perm.Fin

/-! # Exact nonwrapping positions under a power of the inverse finite unit rotation -/

namespace QuantumAlg.Permutation

/-- Moving an admitted finite position down by its complete distance loses no boundary bit. -/
lemma inverseRotation_pow_apply_of_le {size : Nat} [NeZero size]
    (distance : Nat) (index : Fin size) (fits : distance ≤ index.val) :
    (((finRotate size)⁻¹ ^ distance) index).val = index.val - distance := by
  induction distance generalizing index with
  | zero => simp
  | succ distance ih =>
      have nonzero : index ≠ 0 := by
        intro same
        have zero : index.val = 0 := congrArg Fin.val same
        omega
      have previous : (((finRotate size)⁻¹) index).val = index.val - 1 :=
        coe_finRotate_symm_of_ne_zero nonzero
      have smaller : distance ≤ (((finRotate size)⁻¹) index).val := by
        rw [previous]
        omega
      rw [pow_succ, Equiv.Perm.mul_apply, ih _ smaller, previous]
      omega

end QuantumAlg.Permutation
