/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Oracle.Xor.Operator
public import QuantumAlg.Components.Kets
import all QuantumAlg.Components.Oracle.Xor.Operator
import all QuantumAlg.Components.Kets
public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Util.FinPow

/-!
# Exact XOR phase kickback

The original XOR operator acts by the Boolean sign on an input basis state
with a minus target. This is a mathematical identity on normalized input
vectors; native query access is supplied separately by the oracle model
[dW19, qcnotes.tex:1167-1173].
-/

namespace QuantumAlg

open NormalizedVector

noncomputable section

variable {n : Nat}

/-- **Phase kickback**: on a `|−⟩` target the XOR oracle acts as the phase
oracle `|x⟩ ↦ (−1)^{f(x)} |x⟩`; the sign `(−1)^{f(x)}` is written
`if f x then -1 else 1`. -/
public theorem PhaseKickback.xor_action (f : Fin (2 ^ n) → Bool) (x : Fin (2 ^ n)) :
    (xorOracleOp f).applyVec
        (((ket x : NormalizedVector (Qubits n)).tensor ketMinus :
          NormalizedVector (Qubits (n + 1))) : HilbertVector (Qubits (n + 1)))
      = (if f x then (-1 : ℂ) else 1)
          • (((ket x : NormalizedVector (Qubits n)).tensor ketMinus :
              NormalizedVector (Qubits (n + 1))) : HilbertVector (Qubits (n + 1))) := by
  apply WithLp.ofLp_injective
  funext i
  rcases (prodEquiv (m := n) (n := 1)).surjective i with ⟨⟨y, b⟩, rfl⟩
  rw [xorOracleOp_apply]
  simp only [NormalizedVector.tensor_apply_prod, Equiv.symm_apply_apply,
    xorPerm_apply]
  by_cases hy : y = x
  · subst y
    by_cases h : f x
    · fin_cases b <;>
        simp [h, ketMinus_apply]
    · simp [h, ketMinus_apply]
  · by_cases hx : f x <;> by_cases h : f y <;> fin_cases b <;>
      simp [hx, h, hy, NormalizedVector.ket_apply]

end

end QuantumAlg
