/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Unitary
public import QuantumAlg.Core.Base.State.Normalized
import Mathlib.Data.Nat.Bitwise
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# The source modular-exponentiation permutation

The original query updates an arbitrary target by XOR with x^a modulo N.
Only positive modulus and sufficient target capacity are required. Physical
placement and native query accounting belong to the circuit owner.
-/

namespace QuantumAlg

open NormalizedVector

noncomputable section

namespace OrderFinding

/-- Register assumptions for the modular-exponentiation oracle. -/
public structure ModExpOracleAccess (N x t m : Nat) where
  modulus_pos : 0 < N
  register_fits : N ≤ 2 ^ m

/-- Target update `y -> y xor (x^a mod N)`. -/
public def modExpOracleTarget {N x t m : Nat} (A : ModExpOracleAccess N x t m)
    (a : Fin (2 ^ t)) (y : Fin (2 ^ m)) : Fin (2 ^ m) :=
  ⟨Nat.xor y.val (x ^ a.val % N),
    Nat.xor_lt_two_pow y.isLt
      (lt_of_lt_of_le (Nat.mod_lt _ A.modulus_pos) A.register_fits)⟩

@[simp]
theorem modExpOracleTarget_val {N x t m : Nat} (A : ModExpOracleAccess N x t m)
    (a : Fin (2 ^ t)) (y : Fin (2 ^ m)) :
    (modExpOracleTarget A a y).val = Nat.xor y.val (x ^ a.val % N) :=
  rfl

/-- Basis permutation underlying the modular-exponentiation oracle. -/
public def modExpOraclePerm {N x t m : Nat} (A : ModExpOracleAccess N x t m) :
    Equiv.Perm (Fin (2 ^ t) × Fin (2 ^ m)) where
  toFun p := (p.1, modExpOracleTarget A p.1 p.2)
  invFun p := (p.1, modExpOracleTarget A p.1 p.2)
  left_inv p := by
    ext <;> simp [modExpOracleTarget, Nat.xor_xor_cancel_right]
  right_inv p := by
    ext <;> simp [modExpOracleTarget, Nat.xor_xor_cancel_right]

@[simp]
theorem modExpOraclePerm_apply {N x t m : Nat} (A : ModExpOracleAccess N x t m)
    (p : Fin (2 ^ t) × Fin (2 ^ m)) :
    modExpOraclePerm A p = (p.1, modExpOracleTarget A p.1 p.2) :=
  rfl

@[simp]
theorem modExpOraclePerm_symm {N x t m : Nat} (A : ModExpOracleAccess N x t m) :
    (modExpOraclePerm A).symm = modExpOraclePerm A :=
  rfl

/-- Metadata-free unitary oracle from the public access equation. -/
public def modExpOracle {N x t m : Nat} (A : ModExpOracleAccess N x t m) :
    UnitaryOperator (Qubits (t + m)) :=
  UnitaryOperator.ofPerm (prodEquiv.permCongr (modExpOraclePerm A))

/-- Basis action of the modular-exponentiation oracle. -/
theorem modExpOracle_apply_ket {N x t m : Nat} (A : ModExpOracleAccess N x t m)
    (a : Fin (2 ^ t)) (y : Fin (2 ^ m)) :
    (modExpOracle A).apply (ket (prodEquiv (a, y))) =
      ket (prodEquiv (a, modExpOracleTarget A a y)) := by
  rw [modExpOracle, UnitaryOperator.ofPerm_apply_ket]
  congr 1
  change prodEquiv ((modExpOraclePerm A).symm (prodEquiv.symm (prodEquiv (a, y)))) =
      prodEquiv (a, modExpOracleTarget A a y)
  rw [Equiv.symm_apply_apply, modExpOraclePerm_symm, modExpOraclePerm_apply]

end OrderFinding

end

end QuantumAlg
