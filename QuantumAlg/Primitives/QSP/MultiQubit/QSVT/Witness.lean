/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Signal

/-!
# QSVT public witnesses

Registry-facing staged endpoints for projected and Hermitian QSVT.
-/

@[expose] public section

namespace QuantumAlg

namespace QSP.MultiQubit

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace QSVT.Witness

namespace Projected

/-- Staged public projected-QSVT endpoint. -/
theorem main {N L : Nat} {PRe : Polynomial ℝ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (hP : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L PRe)
    (hL : 0 < L) :
    ∃ realization :
        RealProjectedQSVTRealization U left right L
          (singularValuePolynomial right L (realPolynomialToComplex PRe)
            (projectedUnitaryBlock left right U)),
      ProjectedResourceProfile.HasExactCounts
        (ProjectedResourceProfile.ofLength L) L ∧
        ResourceProfile.HasExactCounts realization.circuit.resources L 0 L 0 := by
  exact QSVT.Decomposition.Projected.sourceMain U left right hP hL

end Projected

namespace HermitianRealParity

/-- Staged public real matching-parity Hermitian QSVT endpoint. -/
theorem main {m n L : Nat} {U : Gate (Qubits (m + n))} {A : HilbertOperator (Qubits n)}
    (PRe : Polynomial ℝ) (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hP : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L PRe)
    (hLpos : 0 < L) :
    ∃ word : HermitianQSVTWord m (1 + m) n A,
      word.UsesSignal U ∧
        ExactBlockEncoding (1 + m) n word.output
          (polynomialOperator (realPolynomialToComplex PRe) A) ∧
        word.totalBlockAncilla = m + 1 ∧
        word.resources = realParityResources m L ∧
        (realPolynomialToComplex PRe).natDegree ≤ L ∧
        HasParity (realPolynomialToComplex PRe) L ∧
        HermitianResourceProfile.HasExactCounts word.resources L 0 1 ((m + 1) * L) ∧
        NatBigO (fun d : ℕ => (realParityResources m d).oracleQueries) (fun d : ℕ => d) ∧
        NatBigO (fun d : ℕ => (realParityResources m d).elementaryGates)
          (fun d : ℕ => (m + 1) * d) := by
  exact QSVT.Signal.HermitianRealParity.sourceMain PRe hbe hA hP hLpos

end HermitianRealParity

namespace HermitianRealArbitrary

/-- Staged internal real arbitrary-parity Hermitian QSVT endpoint. -/
theorem main {m n L : Nat}
    {U : Gate (Qubits (m + n))} {A : HilbertOperator (Qubits n)}
    (PRe : Polynomial ℝ) (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hdegree : PRe.natDegree ≤ L)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → |PRe.eval x| ≤ (1 / 2 : ℝ)) :
    ∃ word : HermitianQSVTWord m (1 + (1 + m)) n A,
      word.UsesSignal U ∧
        ExactBlockEncoding (1 + (1 + m)) n word.output
          (polynomialOperator (realPolynomialToComplex PRe) A) ∧
        word.totalBlockAncilla = m + 2 ∧
        word.resources = hermitianComplexResources m L ∧
        NatBigO (fun d : ℕ => (hermitianComplexResources m d).oracleQueries)
          (fun d : ℕ => d) ∧
        NatBigO (fun d : ℕ => (hermitianComplexResources m d).elementaryGates)
          (fun d : ℕ => (m + 1) * d) := by
  exact QSVT.Signal.HermitianRealArbitrary.sourceMain PRe hbe hA hdegree hbound

end HermitianRealArbitrary

namespace HermitianComplex

/-- Staged public complex Hermitian QSVT endpoint. -/
theorem main {m n L : Nat}
    {U : Gate (Qubits (m + n))} {A : HilbertOperator (Qubits n)}
    (P : Polynomial ℂ) (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hdegree : P.natDegree ≤ L)
    (hbound :
      ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
        Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ∃ word : HermitianQSVTWord m (1 + (1 + (1 + m))) n A,
      word.UsesSignal U ∧
        BlockEncoding 4 (1 + (1 + (1 + m))) n 0 word.output
          (polynomialOperator P A) ∧
        word.totalBlockAncilla = m + 3 ∧
        word.resources = hermitianComplexFourBranchResources m L ∧
        P.natDegree ≤ L ∧
        HermitianResourceProfile.HasExactCounts word.resources
          (4 * L) 4 3 (4 * ((m + 1) * L)) ∧
        NatBigO (fun d : ℕ =>
            (hermitianComplexFourBranchResources m d).oracleQueries)
          (fun d : ℕ => d) ∧
        NatBigO (fun d : ℕ =>
            (hermitianComplexFourBranchResources m d).elementaryGates)
          (fun d : ℕ => (m + 1) * d) := by
  exact QSVT.Signal.HermitianComplex.sourceMain P hbe hA hdegree hbound

end HermitianComplex

end QSVT.Witness

end QSP.MultiQubit

end QuantumAlg
