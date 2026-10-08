/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Source
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Assembly
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Execution.Block

/-!
# Certified polynomial branches in the shared native execution

Each branch receives its own source synthesis certificate. Only the two
short branches may have degree bound zero; their constant initialization
is implemented before the shared source word.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
noncomputable section

/-- Four matching-parity source certificates yield one native execution and its exact budget. -/
theorem exists_four_polynomial_execution {m n L : Nat}
    (U : UnitaryOperator (Qubits (m + n))) (positive : 0 < n)
    (A : HilbertOperator (Qubits n)) (encoding : ExactBlockEncoding m n U A)
    (hermitian : A.IsHermitian) (R S T V : Polynomial ℝ)
    (r : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L R)
    (s : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity (L + 1) S)
    (t : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L T)
    (v : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity (L + 1) V) :
    ∃ phases : List ((ℝ × ℝ) × (ℝ × ℝ)), ∃ realAngle imaginaryAngle realConstant
      imaginaryConstant : ℝ,
      phases.length = L ∧
      projectedBlock (1 + (1 + (1 + m))) n
        (reassociateThree (complexWord U positive phases realAngle imaginaryAngle
          realConstant imaginaryConstant).binaryMatrix) =
        (1 / 4 : ℂ) • polynomialOperator (realPolynomialToComplex R) A +
        (1 / 4 : ℂ) • polynomialOperator (realPolynomialToComplex S) A +
        ((1 / 4 : ℂ) • Complex.I • polynomialOperator (realPolynomialToComplex T) A +
          (1 / 4 : ℂ) • Complex.I • polynomialOperator (realPolynomialToComplex V) A) ∧
      (complexWord U positive phases realAngle imaginaryAngle
        realConstant imaginaryConstant).eventCost = complexBudget U L := by
  obtain ⟨rs, rc, rl, _, rb⟩ :=
    exists_initialized_polynomial_branch U positive A encoding hermitian r
  obtain ⟨ss, sc, sl, si, sb⟩ :=
    exists_initialized_polynomial_branch U positive A encoding hermitian s
  obtain ⟨ts, tc, tl, _, tb⟩ :=
    exists_initialized_polynomial_branch U positive A encoding hermitian t
  obtain ⟨vs, vc, vl, vi, vb⟩ :=
    exists_initialized_polynomial_branch U positive A encoding hermitian v
  have scOne := si (Nat.zero_lt_succ L)
  have vcOne := vi (Nat.zero_lt_succ L)
  subst sc
  subst vc
  obtain ⟨phases, ra, ia, length, matrix, budget⟩ := exists_complexWord_for_lists U positive
    rs ss ts vs (by omega) (by omega) (by omega) rc tc
  refine ⟨phases, ra, ia, rc, tc, length.trans rl, ?_, ?_⟩
  · rw [matrix, threeAverage_projected_block, phasePlusBlock_scaled, phasePlusBlock_scaled,
      projectedBlock_smul, projectedBlock_smul, rb, sb, tb, vb]
  · simpa only [rl] using budget

end
end QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
