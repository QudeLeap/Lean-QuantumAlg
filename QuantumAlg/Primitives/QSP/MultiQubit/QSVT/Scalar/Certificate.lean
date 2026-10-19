/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Scalar
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Average

/-!
# Constant source polynomials in actual native execution

The source interval bound certifies the known constant coefficient. One native
single-qubit dilation realizes the polynomial with no source query, including
zero-width source and signal registers.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Scalar
noncomputable section

/-- The original interval bound certifies the constant coefficient without accessing the oracle. -/
lemma constant_coefficient_bound (P : Polynomial ℂ)
    (bounded : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    Complex.normSq (P.coeff 0) ≤ 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simpa only [Complex.ofReal_zero] using bounded 0 (by constructor <;> norm_num)

/-- The single executed native gate realizes a constant source polynomial on the full domain. -/
lemma scalarCircuit_constant_polynomial {m n : Nat} (oracles : OracleModel)
    (P : Polynomial ℂ) (A : HilbertOperator (Qubits n)) (degree : P.natDegree = 0)
    (bounded : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1)
      (environment : oracles.Interpretation) :
    ExactBlockEncoding (1 + m) n
      (reassociatePhaseAncillaOperator (m := m) (n := n)
        ((circuit oracles m n (P.coeff 0) (constant_coefficient_bound P bounded)).binaryMatrix
          environment))
      (polynomialOperator P A) := by
  rw [circuit_source_matrix]
  exact exactBlockEncoding_constantPolynomialWithSourceAncillas P A degree _

end
end QuantumAlg.QSP.MultiQubit.QSVT.Scalar
