/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Base.Tensor
public import QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Core.Base.State.Normalized
public import Mathlib.Data.Real.Basic

/-!
# Leading-qubit marginal weights and probabilities

Circuit- and measurement-object-independent marginal helpers for finite
vectors. A raw vector has only a Born weight; the probability name is reserved
for the wrapper whose input carries unit normalization intrinsically.
-/

section

namespace QuantumAlg
namespace HilbertVector

noncomputable section

/-- Born weight of the leading-qubit outcome `b` for an arbitrary raw vector. -/
def leadingQubitWeight {n : Nat} (ψ : HilbertVector (Qubits (1 + n)))
    (b : Fin (2 ^ 1)) : ℝ :=
  ∑ y : Fin (2 ^ n), ‖ψ (prodEquiv (b, y))‖ ^ 2

lemma leadingQubitWeight_nonneg {n : Nat} (ψ : HilbertVector (Qubits (1 + n)))
    (b : Fin (2 ^ 1)) :
    0 ≤ leadingQubitWeight ψ b :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Scaling a raw vector scales its marginal weight by the squared
scalar norm. -/
lemma leadingQubitWeight_smul {n : Nat} (c : ℂ)
    (ψ : HilbertVector (Qubits (1 + n))) (b : Fin (2 ^ 1)) :
    leadingQubitWeight (c • ψ) b = ‖c‖ ^ 2 * leadingQubitWeight ψ b := by
  rw [leadingQubitWeight, leadingQubitWeight, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [PiLp.smul_apply, smul_eq_mul, norm_mul, mul_pow]

end

end HilbertVector

namespace NormalizedVector

noncomputable section

/-- Probability of the leading-qubit outcome `b` for a normalized vector. -/
public def probQubit0 {n : Nat} (ψ : NormalizedVector (Qubits (1 + n)))
    (b : Fin (2 ^ 1)) : ℝ :=
  HilbertVector.leadingQubitWeight (ψ : HilbertVector (Qubits (1 + n))) b

lemma probQubit0_nonneg {n : Nat} (ψ : NormalizedVector (Qubits (1 + n)))
    (b : Fin (2 ^ 1)) :
    0 ≤ probQubit0 ψ b :=
  by
    change 0 ≤ HilbertVector.leadingQubitWeight
      (ψ : HilbertVector (Qubits (1 + n))) b
    exact HilbertVector.leadingQubitWeight_nonneg
      (ψ : HilbertVector (Qubits (1 + n))) b

end

end NormalizedVector
end QuantumAlg

end
