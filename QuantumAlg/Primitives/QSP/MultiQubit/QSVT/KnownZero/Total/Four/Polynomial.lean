/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Source
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Assembly
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Execution.Block

/-!
# Certified polynomial branches in the shared native execution

Each branch receives its own source synthesis certificate. Only the two
short branches may have degree bound zero; their constant initialization
is implemented before the shared source word.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
open SharedFour
noncomputable section

/-- Four scalar certificates fix phase data uniformly for every encoded Hermitian operator. -/
lemma exists_total_four_polynomial_execution {L : Nat}
    (R S T V : Polynomial ℝ)
    (r : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L R)
    (s : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity (L + 1) S)
    (t : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L T)
    (v : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity (L + 1) V) :
    ∃ phases : List ((ℝ × ℝ) × (ℝ × ℝ)), ∃ realAngle imaginaryAngle realConstant
      imaginaryConstant : ℝ,
      phases.length = L ∧
      ∀ (m n : Nat) (U : UnitaryOperator (Qubits (m + n)))
        (A : HilbertOperator (Qubits n)), ExactBlockEncoding m n U A → A.IsHermitian →
      projectedBlock (1 + (1 + (1 + m))) n
        (reassociateThree ((complexWord (m := m) (n := n) phases realAngle imaginaryAngle
          realConstant imaginaryConstant).binaryMatrix
            (UnitarySource.interpretation U true true false))) =
        (1 / 4 : ℂ) • polynomialOperator (realPolynomialToComplex R) A +
        (1 / 4 : ℂ) • polynomialOperator (realPolynomialToComplex S) A +
        ((1 / 4 : ℂ) • Complex.I • polynomialOperator (realPolynomialToComplex T) A +
          (1 / 4 : ℂ) • Complex.I • polynomialOperator (realPolynomialToComplex V) A) ∧
      (complexWord (m := m) (n := n) phases realAngle imaginaryAngle
        realConstant imaginaryConstant).eventCost = complexBudget (m := m) (n := n) L := by
  obtain ⟨rs, rc, rl, _, rb⟩ :=
    exists_total_initialized_polynomial_branch r
  obtain ⟨ss, sc, sl, si, sb⟩ :=
    exists_total_initialized_polynomial_branch s
  obtain ⟨ts, tc, tl, _, tb⟩ :=
    exists_total_initialized_polynomial_branch t
  obtain ⟨vs, vc, vl, vi, vb⟩ :=
    exists_total_initialized_polynomial_branch v
  have scOne := si (Nat.zero_lt_succ L)
  have vcOne := vi (Nat.zero_lt_succ L)
  subst sc
  subst vc
  obtain ⟨phases, ra, ia, length, packed⟩ := exists_totalComplexWord_for_lists
    rs ss ts vs (by omega) (by omega) (by omega) rc tc
  refine ⟨phases, ra, ia, rc, tc, length.trans rl, ?_⟩
  intro m n U A encoding hermitian
  obtain ⟨matrix, budget⟩ := packed m n U
  constructor
  · rw [matrix, threeAverage_projected_block, phasePlusBlock_scaled, phasePlusBlock_scaled,
      projectedBlock_smul, projectedBlock_smul,
      rb m n U A encoding hermitian, sb m n U A encoding hermitian,
      tb m n U A encoding hermitian, vb m n U A encoding hermitian]
  · simpa only [rl] using budget

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
