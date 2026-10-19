/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Certificate.Execution
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Gates
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Queries
import all QuantumAlg.Components.Gates.Toffoli.Refinement.Counts
import all QuantumAlg.Components.Gates.Toffoli.Refinement.Queries
import all QuantumAlg.Components.Gates.Toffoli.Refinement.Depth
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary

/-!
# Matching-parity Hermitian execution using only one- and two-qubit gates

The exact native substitution preserves the single transformation ancilla and
all original source systems. Every source query remains in the original access
model, while complete gate and dependency-depth bounds include both Hadamards.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total
open Gate.Toffoli
noncomputable section

/-- Positive-degree matching-parity execution has actual one- and two-qubit resource bounds. -/
lemma exists_total_real_expanded_execution {m n L : Nat} {P : Polynomial ℝ}
    (U : UnitaryOperator (Qubits (m + n)))
    (A : HilbertOperator (Qubits n)) (encoding : ExactBlockEncoding m n U A)
    (hermitian : A.IsHermitian)
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P)
    (positiveDegree : 0 < L) :
    ∃ word : UnitaryCircuit AlgorithmGate.model (UnitarySource.model (m + n) false true false)
        (ProjectorPhase.layout (m + n)),
      ExactBlockEncoding (1 + m) n
        (reassociatePhaseAncillaOperator (m := m) (n := n) (word.binaryMatrix
          (UnitarySource.interpretation U false true false)))
        (polynomialOperator (realPolynomialToComplex P) A) ∧
      word.eventCost = expandedBudget (UnitarySource.model (m + n) false true false)
        (budget (m := m) (n := n) false L + 2 • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false))
          (.gate .singleQubit)) ∧
      word.evaluatedEventDepth (fun _ => 1) ≤ 15 * ((40 * m + 4) * L + 2) ∧
      nativeGateCount word.eventCost ≤ 15 * ((40 * m + 3) * L + 2) ∧
      ResourcePool.count
        (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false))
        (.gate .toffoli) word.eventCost = 0 := by
  obtain ⟨word, block, events, depth⟩ := exists_total_real_native_execution
    U A encoding hermitian source positiveDegree
  refine ⟨expand word, ?_, ?_, ?_, ?_, toffoliExpansion_expanded_toffoli_count word⟩
  · have same : ((expand word).binaryMatrix
    (UnitarySource.interpretation U false true false))
    = (word.binaryMatrix (UnitarySource.interpretation U false true false)) := by
      unfold UnitaryCircuit.binaryMatrix
      rw [toffoliExpansion_preserves_matrix]
    rw [same]
    exact block
  · rw [toffoliExpansion_expanded_eventCost, events]
  · exact (toffoliExpansion_depth_le word).trans (Nat.mul_le_mul_left 15 depth)
  · have nativeBound : nativeGateCount word.eventCost ≤ (40 * m + 3) * L + 2 := by
      rw [events, nativeGateCount_add, nativeGateCount_nsmul,
        nativeGateCount_singleton_gate, Nat.mul_one]
      exact Nat.add_le_add_right (totalRealBudget_native_gate_bound (m := m) (n := n) false L) 2
    exact (toffoliExpansion_native_gate_bound word).trans (Nat.mul_le_mul_left 15 nativeBound)

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total
