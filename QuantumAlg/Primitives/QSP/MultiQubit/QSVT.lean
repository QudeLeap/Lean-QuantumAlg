/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base
public import QuantumAlg.Core.Base.Accounting.Space
public import QuantumAlg.Components.Oracle.Reflection
public import QuantumAlg.Components.Oracle.BlockEncoding
public import QuantumAlg.Util.Polynomial.Basic
public import QuantumAlg.Util.Asymptotics
public import QuantumAlg.Primitives.QSP.SingleQubit.PhaseSynthesis
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Complement
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Decomposition
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Signal
public import Mathlib.LinearAlgebra.Matrix.Hermitian
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Decomposition
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Signal

import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Witness

/-!
# Quantum singular value transformation

Public projected and Hermitian QSVT endpoints. Each theorem binds the operator
transformation, event counts, and live space to the same constructed circuit.
-/

namespace QuantumAlg.QSP.MultiQubit

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace QSVT.Witness

namespace Projected

/-- Staged public projected-QSVT endpoint. -/
public theorem main {N L : Nat} {PRe : Polynomial ℝ}
    (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N)
    (hP : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L PRe)
    (hL : 0 < L) :
    ∃ realization :
        RealProjectedQSVTRealization U left right L
          (singularValuePolynomial right L (realPolynomialToComplex PRe)
            (projectedUnitaryBlock left right U)),
      ProjectedEventProfile.HasExactCounts N L realization.circuit.eventCost ∧
        SpacePool.count (.quantumSystems 2) realization.liveSpace = 1 + N := by
  rcases QSVT.Decomposition.Projected.sourceMain U left right hP hL with
    ⟨realization, hevents⟩
  exact ⟨realization, hevents, by simp⟩

end Projected

namespace HermitianRealParity

/-- Staged public real matching-parity Hermitian QSVT endpoint. -/
public theorem main {m n L : Nat}
    {U : UnitaryOperator (Qubits (m + n))} {A : HilbertOperator (Qubits n)}
    (PRe : Polynomial ℝ) (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hP : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L PRe)
    (hLpos : 0 < L) :
    ∃ word : HermitianQSVTWord m (1 + m) n A,
      word.UsesSignal U ∧
        ExactBlockEncoding (1 + m) n word.circuit.matrix
          (polynomialOperator (realPolynomialToComplex PRe) A) ∧
        word.totalBlockAncilla = m + 1 ∧
        word.eventProfile = realParityEventProfile m L ∧
        HermitianEventProfile.HasExactEvents word.eventProfile
          word.circuit.eventCost ∧
        SpacePool.count (.quantumSystems 2) word.extraAncillaSpace = 1 ∧
        SpacePool.count (.quantumSystems 2) word.liveSpace = (1 + m) + n ∧
        (realPolynomialToComplex PRe).natDegree ≤ L ∧
        HasParity (realPolynomialToComplex PRe) L ∧
        HermitianEventProfile.HasExactCounts word.eventProfile
          L 0 (3 * L + 2) ∧
        NatBigO (fun d : ℕ => (realParityEventProfile m d).oracleQueries)
          (fun d : ℕ => d) ∧
        NatBigO (fun d : ℕ => (realParityEventProfile m d).elementaryEvents)
          (fun d : ℕ => (m + 1) * d) := by
  rcases QSVT.Signal.HermitianRealParity.sourceMain PRe hbe hA hP hLpos with
    ⟨word, huses, henc, htotal, hevents, hdegree, hparity⟩
  have hcounts := realParityEventProfile_exact m L
  rw [← hevents] at hcounts
  have hextra : word.extraAncillaQubits = 1 := by
    have hfield := word.totalBlockAncilla_eq
    omega
  exact ⟨word, huses, henc, htotal, hevents, word.circuit_events,
    by simp [hextra],
    word.liveSpace_logicalQubits,
    hdegree, hparity, hcounts,
    realParityEventOracleQueries_bigO m, realParityElementaryEvents_bigO m⟩

end HermitianRealParity

namespace HermitianComplex

/-- Staged public complex Hermitian QSVT endpoint. -/
public theorem main {m n L : Nat}
    {U : UnitaryOperator (Qubits (m + n))} {A : HilbertOperator (Qubits n)}
    (P : Polynomial ℂ) (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hdegree : P.natDegree ≤ L)
    (hbound :
      ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
        Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ∃ word : HermitianQSVTWord m (1 + (1 + (1 + m))) n A,
      word.UsesSignal U ∧
        BlockEncoding 4 (1 + (1 + (1 + m))) n 0 word.circuit.matrix
          (polynomialOperator P A) ∧
        word.totalBlockAncilla = m + 3 ∧
        word.eventProfile = hermitianComplexFourBranchEventProfile m L ∧
        HermitianEventProfile.HasExactEvents word.eventProfile
          word.circuit.eventCost ∧
        SpacePool.count (.quantumSystems 2) word.extraAncillaSpace = 3 ∧
        SpacePool.count (.quantumSystems 2) word.liveSpace =
          (1 + (1 + (1 + m))) + n ∧
        P.natDegree ≤ L ∧
        HermitianEventProfile.HasExactCounts word.eventProfile
          (6 * ReflectionQSPPhaseSynthesis.evenBranchDegree L +
            3 * ReflectionQSPPhaseSynthesis.oddBranchDegree L)
          (5 * ReflectionQSPPhaseSynthesis.evenBranchDegree L +
            3 * ReflectionQSPPhaseSynthesis.oddBranchDegree L)
          (6 * matchingParityElementaryGates
              (ReflectionQSPPhaseSynthesis.evenBranchDegree L) +
            3 * matchingParityElementaryGates
              (ReflectionQSPPhaseSynthesis.oddBranchDegree L) + 11) ∧
        NatBigO (fun d : ℕ =>
            (hermitianComplexFourBranchEventProfile m d).oracleQueries)
          (fun d : ℕ => d) ∧
        NatBigO (fun d : ℕ =>
            (hermitianComplexFourBranchEventProfile m d).elementaryEvents)
          (fun d : ℕ => (m + 1) * d) := by
  rcases QSVT.Signal.HermitianComplex.sourceMain P hbe hA hdegree hbound with
    ⟨word, huses, henc, htotal, hevents, hdegree'⟩
  have hcounts := hermitianComplexFourBranchEventProfile_exact m L
  rw [← hevents] at hcounts
  have hextra : word.extraAncillaQubits = 3 := by
    have hfield := word.totalBlockAncilla_eq
    omega
  exact ⟨word, huses, henc, htotal, hevents, word.circuit_events,
    by simp [hextra],
    word.liveSpace_logicalQubits, hdegree', hcounts,
    hermitianComplexFourBranchEventOracleQueries_bigO m,
    hermitianComplexFourBranchElementaryEvents_bigO m⟩

end HermitianComplex

end QSVT.Witness

end QuantumAlg.QSP.MultiQubit
