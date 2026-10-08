/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.BornProbability.Source
import all QuantumAlg.Primitives.ShortDLP.Oracle.Graph
import all QuantumAlg.Primitives.WalshHadamard.Mathematics

/-!
# Group-query graph state from the declared source operator

The exact reversible query applied to a uniform exponent state and zero
workspace produces the source graph vector. This statement is independent of
the preparation and inverse-Fourier implementation proofs.
-/

namespace QuantumAlg.ShortDLP.BornProbability

open NormalizedVector

noncomputable section

private theorem invSqrtCard_add (left right : Nat) :
    WalshHadamard.invSqrtCard (left + right) =
      WalshHadamard.invSqrtCard left * WalshHadamard.invSqrtCard right := by
  induction right with
  | zero => simp [WalshHadamard.invSqrtCard]
  | succ right ih =>
      rw [Nat.add_succ, WalshHadamard.invSqrtCard_succ, ih,
        WalshHadamard.invSqrtCard_succ]
      ring

/-- Source preparation vector before the group query, in the same three-register
binary basis as the actual declared stage. -/
def preOracleVec (params : RegisterParameters) :
    HilbertVector (Qubits (totalQubits params)) :=
  HilbertVector.tensor
    (WalshHadamard.uniformState (firstBits params + params.ell) :
      HilbertVector (Qubits (firstBits params + params.ell)))
    (NormalizedVector.ket (R := Qubits params.workspaceBits)
      (0 : Fin (2 ^ params.workspaceBits)) :
        HilbertVector (Qubits params.workspaceBits))

/-- The declared group permutation maps the uniform zero-workspace input to
the exact source group-operation graph, with every exponent basis amplitude. -/
theorem oracleOperator_apply_preOracle {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ) :
    (oracleOperator encoding g x).applyVec (preOracleVec params) =
      postOracleVec encoding g x := by
  apply WithLp.ofLp_injective
  funext basis
  rw [oracleOperator, UnitaryOperator.ofPerm_applyVec]
  simp only [Equiv.permCongr_apply]
  let triple := (tripleEquiv params).symm basis
  change preOracleVec params
      (tripleEquiv params (oraclePerm encoding g x triple)) = _
  change HilbertVector.tensor
      (WalshHadamard.uniformState (firstBits params + params.ell) :
        HilbertVector (Qubits (firstBits params + params.ell)))
      (NormalizedVector.ket (R := Qubits params.workspaceBits)
        (0 : Fin (2 ^ params.workspaceBits)) :
          HilbertVector (Qubits params.workspaceBits))
      (prodEquiv
        (prodEquiv (triple.1.1, triple.1.2),
          oracleTarget encoding g x triple.1.1 triple.1.2 triple.2)) = _
  rw [HilbertVector.tensor_apply_prod, WalshHadamard.uniformState_apply,
    NormalizedVector.ket_apply, invSqrtCard_add]
  change _ =
    if triple.2 = encodeUnit encoding
        (oracleValue g x triple.1.1.val triple.1.2.val) then
      WalshHadamard.invSqrtCard (firstBits params) *
        WalshHadamard.invSqrtCard params.ell
    else 0
  rw [if_congr
    (oracleTarget_eq_zero_iff encoding g x triple.1.1 triple.1.2 triple.2)
    rfl rfl]
  by_cases target : triple.2 = encodeUnit encoding
      (oracleValue g x triple.1.1.val triple.1.2.val)
  · rw [if_pos target, if_pos target, mul_one]
  · rw [if_neg target, if_neg target, mul_zero]

end

end QuantumAlg.ShortDLP.BornProbability
