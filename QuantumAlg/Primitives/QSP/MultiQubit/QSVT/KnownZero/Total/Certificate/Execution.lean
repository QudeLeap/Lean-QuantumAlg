/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Certificate
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Block

/-!
# Actual matching-parity Hermitian execution on every source width

One phase ancilla, all original source systems and the original alternating
source queries determine the execution. Known projectors are expanded into
native gates, and both boundary Hadamards remain in its resource accounting.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total
noncomputable section

/-- Source assumptions select one actual Hermitian polynomial circuit with its complete budget. -/
lemma exists_total_real_native_execution {m n L : Nat} {P : Polynomial ℝ}
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
      word.eventCost = budget (m := m) (n := n) false L +
        2 • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false))
          (.gate .singleQubit) ∧
      word.evaluatedEventDepth (fun _ => 1) ≤ (40 * m + 4) * L + 2 := by
  obtain ⟨phases, length, correct, events, _⟩ :=
    exists_total_real_word U false source positiveDegree
  refine ⟨zeroBlockCircuit (m := m) (n := n) false phases, ?_, ?_, ?_⟩
  · exact totalZeroBlockCircuit_correct U false phases encoding hermitian
      (ReflectionQSPPhaseSynthesis.hasParity_realPolynomialToComplex source.parity) correct
  · rw [totalZeroBlockCircuit_events, events]
  · rw [totalZeroBlockCircuit_depth, length]
    have bound := totalPhaseDepth_le m n
    exact Nat.add_le_add_right (Nat.mul_le_mul_right L (by omega)) 2

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total
