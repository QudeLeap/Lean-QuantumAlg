/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import QuantumAlg.Core.Base
import QuantumAlg.Core.Base.Accounting.Space
import QuantumAlg.Components.Oracle.Reflection
import QuantumAlg.Components.Oracle.BlockEncoding
import QuantumAlg.Util.Polynomial.Basic
import QuantumAlg.Util.Asymptotics
import QuantumAlg.Primitives.QSP.SingleQubit.PhaseSynthesis
import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Complement
import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Decomposition
import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Signal
import Mathlib.LinearAlgebra.Matrix.Hermitian
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Decomposition
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Signal

/-!
# Internal Hermitian QSVT witness

The arbitrary-real construction is an internal consequence of the signal implementation.
-/

section

namespace QuantumAlg

namespace QSP.MultiQubit

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace QSVT.Witness

namespace HermitianRealArbitrary

/-- Staged internal real arbitrary-parity Hermitian QSVT endpoint. -/
theorem main {m n L : Nat}
    {U : UnitaryOperator (Qubits (m + n))} {A : HilbertOperator (Qubits n)}
    (PRe : Polynomial ℝ) (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hdegree : PRe.natDegree ≤ L)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → |PRe.eval x| ≤ (1 / 2 : ℝ)) :
    ∃ word : HermitianQSVTWord m (1 + (1 + m)) n A,
      word.UsesSignal U ∧
        ExactBlockEncoding (1 + (1 + m)) n word.output
          (polynomialOperator (realPolynomialToComplex PRe) A) ∧
        word.totalBlockAncilla = m + 2 ∧
        word.eventProfile = hermitianComplexEventProfile m L ∧
        HermitianEventProfile.HasExactEvents word.eventProfile
          word.circuit.eventCost ∧
        SpacePool.count (.quantumSystems 2) word.extraAncillaSpace = 2 ∧
        SpacePool.count (.quantumSystems 2) word.liveSpace = (1 + (1 + m)) + n ∧
        HermitianEventProfile.HasExactCounts word.eventProfile
          (2 * ReflectionQSPPhaseSynthesis.evenBranchDegree L +
            ReflectionQSPPhaseSynthesis.oddBranchDegree L)
          (ReflectionQSPPhaseSynthesis.evenBranchDegree L +
            ReflectionQSPPhaseSynthesis.oddBranchDegree L)
          (2 * matchingParityElementaryGates
              (ReflectionQSPPhaseSynthesis.evenBranchDegree L) +
            matchingParityElementaryGates
              (ReflectionQSPPhaseSynthesis.oddBranchDegree L) + 2) ∧
        NatBigO (fun d : ℕ => (hermitianComplexEventProfile m d).oracleQueries)
          (fun d : ℕ => d) ∧
        NatBigO
          (fun d : ℕ => (hermitianComplexEventProfile m d).elementaryEvents)
          (fun d : ℕ => (m + 1) * d) := by
  rcases QSVT.Signal.HermitianRealArbitrary.sourceMain PRe hbe hA hdegree hbound with
    ⟨word, huses, henc, htotal, hevents⟩
  have hcounts := hermitianComplexEventProfile_exact m L
  rw [← hevents] at hcounts
  have hextra : word.extraAncillaQubits = 2 := by
    have hfield := word.totalBlockAncilla_eq
    omega
  exact ⟨word, huses, henc, htotal, hevents, word.circuit_events,
    by simp [hextra],
    word.liveSpace_logicalQubits, hcounts,
    hermitianComplexEventOracleQueries_bigO m,
    hermitianComplexElementaryEvents_bigO m⟩

end HermitianRealArbitrary

end QSVT.Witness

end QSP.MultiQubit

end QuantumAlg

end
