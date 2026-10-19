/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Constant
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Complement
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Certificate
import all QuantumAlg.Util.Polynomial.Basic

/-!
# Degree-zero projected singular-value transformation

A constant real polynomial requires one phase rotation on the transformation
ancilla and no source or projector query. The target is the constant times
the input projector, including its complement and any zero-width source.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Native
noncomputable section

private lemma evenSquareQuotient_constant (c : ℂ) :
    evenSquareQuotient (Polynomial.C c) = Polynomial.C c := by
  simpa only [evenSquareQuotient_one, Polynomial.smul_eq_C_mul, mul_one] using
    evenSquareQuotient_smul c (1 : Polynomial ℂ)

/-- The degree-zero singular-value transform is scalar on the input projector. -/
lemma singularValuePolynomial_constant {N : Nat} (input : OrthogonalProjector N)
    (P : Polynomial ℂ) (A : HilbertOperator (Qubits N)) (degree : P.natDegree = 0) :
    singularValuePolynomial input 0 P A = P.coeff 0 • input.op := by
  simp only [singularValuePolynomial, Nat.zero_mod, ↓reduceIte, evenSingularValuePolynomial]
  rw [Polynomial.eq_C_of_natDegree_eq_zero degree, evenSquareQuotient_constant,
    polynomialOperator_C]
  simp only [Matrix.mul_smul, mul_one, Matrix.smul_mul, input.idempotent,
    Polynomial.coeff_C_zero]

/-- The actual single rotation implements every admissible real degree-zero projected target. -/
lemma exists_native_constant_word {N : Nat} {P : Polynomial ℝ}
    (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N)
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity 0 P) :
    ∃ word : UnitaryCircuit AlgorithmGate.model (ProjectedSignal.model N)
        (ProjectorPhase.layout N),
      projectedPhasePlusBlock right right (word.binaryMatrix (ProjectedSignal.interpretation U
        left right)) =
        singularValuePolynomial right 0 (realPolynomialToComplex P)
          (projectedUnitaryBlock left right U) ∧
      word.eventCost = ResourcePool.singleton
        (model := .quantum AlgorithmGate.model (ProjectedSignal.model N))
        (.gate .singleQubit) ∧
      word.evaluatedEventDepth (fun _ => 1) = 1 := by
  have bound : |P.coeff 0| ≤ 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact source.bounded 0 (by constructor <;> norm_num)
  have degree : (realPolynomialToComplex P).natDegree = 0 := by
    rw [realPolynomialToComplex_natDegree]
    exact Nat.eq_zero_of_le_zero source.degree_le
  refine ⟨Shared.constantInitial (ProjectedSignal.model N) N (P.coeff 0),
    ?_, rfl, rfl⟩
  rw [projectedPhasePlusBlock,
    Shared.constantInitial_correct _ _ _ (abs_le.mp bound).1 (abs_le.mp bound).2
      (ProjectedSignal.interpretation U left right),
    singularValuePolynomial_constant right _ _ degree]
  simp only [Matrix.mul_smul, mul_one, Matrix.smul_mul, right.idempotent]
  congr 1
  exact (Polynomial.coeff_map (p := P) (algebraMap ℝ ℂ) 0).symm

end
end QuantumAlg.QSP.MultiQubit.QSVT.Native
