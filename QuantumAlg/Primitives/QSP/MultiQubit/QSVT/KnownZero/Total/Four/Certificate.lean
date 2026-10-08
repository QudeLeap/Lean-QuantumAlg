/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Polynomial

/-!
# Complex Hermitian polynomials from actual shared native execution

For positive degree bounds on every original signal width, the real and imaginary
parity components share the source query slots. The unmatched slot uses one
controlled source call. The standard output block has normalization four.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
open SharedFour
noncomputable section

/-- Original complex interval bounds synthesize a normalization-four native execution. -/
theorem exists_total_complex_polynomial_execution {m n L : Nat}
    (U : UnitaryOperator (Qubits (m + n)))
    (A : HilbertOperator (Qubits n)) (encoding : ExactBlockEncoding m n U A)
    (hermitian : A.IsHermitian) (P : Polynomial ℂ) (degree : P.natDegree ≤ L)
    (positiveDegree : 0 < L)
    (bounded : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ∃ phases : List ((ℝ × ℝ) × (ℝ × ℝ)), ∃ realAngle imaginaryAngle realConstant
      imaginaryConstant : ℝ,
      phases.length = L - 1 ∧
      projectedBlock (1 + (1 + (1 + m))) n
        (reassociateThree (complexWord U phases realAngle imaginaryAngle
          realConstant imaginaryConstant).binaryMatrix) =
        (1 / 4 : ℂ) • polynomialOperator P A ∧
      (complexWord U phases realAngle imaginaryAngle
        realConstant imaginaryConstant).eventCost = complexBudget U (L - 1) := by
  have re := ReflectionQSPPhaseSynthesis.realBoundedMatchingParity_realEvenPart_branch_of_normSq_le
    P degree bounded
  have im := ReflectionQSPPhaseSynthesis.realBoundedMatchingParity_imagEvenPart_branch_of_normSq_le
    P degree bounded
  have ro := ReflectionQSPPhaseSynthesis.realBoundedMatchingParity_realOddPart_branch_of_normSq_le
    P degree positiveDegree bounded
  have io := ReflectionQSPPhaseSynthesis.realBoundedMatchingParity_imagOddPart_branch_of_normSq_le
    P degree positiveDegree bounded
  have successor : L - 1 + 1 = L := by omega
  by_cases even : L % 2 = 0
  · simp only [ReflectionQSPPhaseSynthesis.evenBranchDegree,
      ReflectionQSPPhaseSynthesis.oddBranchDegree, even, if_true] at re im ro io
    obtain ⟨phases, ra, ia, rc, ic, length, block, budget⟩ :=
      exists_total_four_polynomial_execution (L := L - 1) U A encoding hermitian
        _ _ _ _ ro (by simpa only [successor] using re)
        io (by simpa only [successor] using im)
    refine ⟨phases, ra, ia, rc, ic, length, ?_, budget⟩
    rw [block]
    have recomposed := polynomialOperator_complex_fourPart_average_recompose P A
    rw [add_comm ((1 / 4 : ℂ) • polynomialOperator
      (realPolynomialToComplex (realPolynomialEvenPart (complexPolynomialRealPart P))) A),
      add_comm ((1 / 4 : ℂ) • Complex.I • polynomialOperator
        (realPolynomialToComplex (realPolynomialEvenPart (complexPolynomialImagPart P))) A)]
      at recomposed
    exact recomposed
  · have odd : L % 2 = 1 := by omega
    simp only [ReflectionQSPPhaseSynthesis.evenBranchDegree,
      ReflectionQSPPhaseSynthesis.oddBranchDegree, odd, if_true] at re im ro io
    obtain ⟨phases, ra, ia, rc, ic, length, block, budget⟩ :=
      exists_total_four_polynomial_execution (L := L - 1) U A encoding hermitian
        _ _ _ _ re (by simpa only [successor] using ro)
        im (by simpa only [successor] using io)
    refine ⟨phases, ra, ia, rc, ic, length, ?_, budget⟩
    rw [block]
    exact polynomialOperator_complex_fourPart_average_recompose P A

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
