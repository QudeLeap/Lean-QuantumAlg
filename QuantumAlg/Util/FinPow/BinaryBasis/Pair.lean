/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.FinPow.BinaryBasis
import all QuantumAlg.Util.FinPow.BitReverse
import all QuantumAlg.Util.FinPow
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# Leading-bit decomposition of big-endian coordinates

Prepending one binary coordinate places it above all tail bits in the encoded
natural label. The pairing convention agrees with the original finite product.
-/

namespace QuantumAlg.BinaryBasis

theorem bigEndianEquiv_cons_value (n : Nat) (head : Fin 2) (tail : Fin n → Fin 2) :
    (bigEndianEquiv (n + 1) (Fin.cons head tail)).val =
      (bigEndianEquiv n tail).val + 2 ^ n * head.val := by
  change Nat.ofBits (fun index : Fin (n + 1) =>
      finTwoEquiv (Fin.cons (α := fun _ => Fin 2) head tail index.rev)) =
    Nat.ofBits (fun index : Fin n => finTwoEquiv (tail index.rev)) + 2 ^ n * head.val
  rw [nat_ofBits_succ_last]
  congr 1
  · apply congrArg Nat.ofBits
    funext index
    simp only [Function.comp_apply, Fin.rev_castSucc, Fin.cons_succ]
  · simp only [Fin.rev_last, Fin.cons_zero]
    congr 1
    fin_cases head <;> rfl

theorem bigEndianEquiv_cons_pair (n : Nat) (head : Fin 2) (tail : Fin n → Fin 2) :
    bigEndianEquiv (n + 1) (Fin.cons head tail) =
      qftPairEquiv n (head, bigEndianEquiv n tail) := by
  apply Fin.ext
  rw [bigEndianEquiv_cons_value, qftPairEquiv_apply_val]

end QuantumAlg.BinaryBasis
