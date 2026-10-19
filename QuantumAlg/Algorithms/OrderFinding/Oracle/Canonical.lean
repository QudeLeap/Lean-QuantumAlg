/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Oracle
public import QuantumAlg.Util.Order.Finding.Widths
public import QuantumAlg.Util.Order.Finding.Signed
import all QuantumAlg.Algorithms.OrderFinding.Oracle

/-! # Modular-exponentiation access at the minimum target width -/

namespace QuantumAlg.OrderFinding

noncomputable section

/-- The source query needs no target-capacity premise beyond a nontrivial modulus. -/
public lemma canonicalAccess {N : Nat} (modulus : 2 ≤ N) (x t : Nat) :
    ModExpOracleAccess N x t (targetWidth N) where
  modulus_pos := by omega
  register_fits := orderFinding_targetWidth_fits N

/-- The same physical XOR oracle acts on the original signed modular powers. -/
public lemma orderFinding_canonicalAccess_signed_target {N : Nat}
    (modulus : 2 ≤ N) (x : Int) (t : Nat)
    (a : Fin (2 ^ t)) (y : Fin (2 ^ targetWidth N)) :
    (modExpOracleTarget (canonicalAccess modulus (x : ZMod N).val t) a y).val =
      Nat.xor y.val (((x : ZMod N) ^ a.val).val) := by
  rw [modExpOracleTarget_val, orderFinding_signedResidue_power (by omega)]

end

end QuantumAlg.OrderFinding
