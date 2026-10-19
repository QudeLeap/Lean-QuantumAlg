/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Selected.Projected
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import QuantumAlg.Components.Oracle.BlockEncoding
public import QuantumAlg.Components.Oracle.UnitarySource.Model
public import QuantumAlg.Components.Oracle.SignalProcessing
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Selected.Projected
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Real
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Regroup
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Certificate.Expanded
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Certificate.Execution
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Block
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Counts
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Word
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Resources
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Gates
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Certificate
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Real
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Scalar.Real
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Scalar.Certificate
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Scalar
import all QuantumAlg.Components.Gates.Toffoli.Refinement.Counts
import all QuantumAlg.Components.Gates.Toffoli.Refinement.Depth

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Operator
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Average
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Complement
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Source.Projected
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Average.Block

import all QuantumAlg.Components.Oracle.SignalProcessing
import all QuantumAlg.Primitives.QSP.SingleQubit.PhaseSynthesis
import all QuantumAlg.Components.Gates.SingleQubit.First.Binary

/-!
# Independent matching-parity Hermitian target and its realization

The target is the mathematical direct sum determined by polynomial synthesis,
with Hadamard boundaries and the standard ancilla reassociation. Degree zero
uses the specified scalar dilation. No target is projected from a circuit.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Execution.Selected
open Gate.Toffoli
noncomputable section

/-- Full Hermitian target selected from the source polynomial before native compilation. -/
public def realTarget {m n L : Nat} {P : Polynomial ℝ}
    (U : UnitaryOperator (Qubits (m + n)))
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P) :
    UnitaryOperator (Qubits ((1 + m) + n)) :=
  if L = 0 then
    scalarDilationWithSourceAncillas (m := m) (n := n) ((realPolynomialToComplex P).coeff 0)
      (Scalar.constant_coefficient_bound _ (Scalar.real_polynomial_normSq_bound source))
  else
    reassociatePhaseAncillaOperator (m := m) (n := n)
      (phaseHadamardWrapperOperator
        (phaseControlledDirectSumOperator
          (Native.sourceWord U (OrthogonalProjector.zeroAncilla m n)
            (OrthogonalProjector.zeroAncilla m n) (realPhases source))
          (Native.sourceWord U (OrthogonalProjector.zeroAncilla m n)
            (OrthogonalProjector.zeroAncilla m n) (negPhases (realPhases source)))))

private lemma positive_realization (m n : Nat) {L : Nat} {P : Polynomial ℝ}
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P)
    (positive : 0 < L) :
    ∃ word : UnitaryCircuit AlgorithmGate.model (UnitarySource.model (m + n) false true false)
        (ProjectorPhase.layout (m + n)),
      (∀ (U : UnitaryOperator (Qubits (m + n))) (A : HilbertOperator (Qubits n)),
        ExactBlockEncoding m n U A → A.IsHermitian →
      reassociatePhaseAncillaOperator (m := m) (n := n) (word.binaryMatrix
        (UnitarySource.interpretation U false true false)) =
        realTarget U source ∧
      ExactBlockEncoding (1 + m) n
        (reassociatePhaseAncillaOperator (m := m) (n := n) (word.binaryMatrix
          (UnitarySource.interpretation U false true false)))
        (polynomialOperator (realPolynomialToComplex P) A)) ∧
      word.eventCost = realBudget m n L ∧
      word.evaluatedEventDepth (fun _ => 1) ≤ 15 * ((40 * m + 4) * L + 2) ∧
      nativeGateCount word.eventCost ≤ 15 * ((40 * m + 3) * L + 2) ∧
      ResourcePool.count
        (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false))
        (.gate .toffoli) word.eventCost = 0 := by
  let phases := realPhases source
  let raw := KnownZero.Total.zeroBlockCircuit (m := m) (n := n) false phases
  have length : phases.length = L := realPhases_length source
  have events : raw.eventCost = KnownZero.Total.budget (m := m) (n := n) false L +
      2 • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false))
        (.gate .singleQubit) := by
    rw [KnownZero.Total.totalZeroBlockCircuit_events, KnownZero.Total.totalCircuit_events,
      length]
  refine ⟨expand raw, ?_, ?_, ?_, ?_, toffoliExpansion_expanded_toffoli_count raw⟩
  · intro U A encoding hermitian
    have projected := Native.circuit_of_real_certificate U
      (OrthogonalProjector.zeroAncilla m n) (OrthogonalProjector.zeroAncilla m n) false
      (ReflectionQSPPhaseSynthesis.chooseRealBoundedPhaseCertificateOfSourceHypotheses source)
      positive
    have correct : projectedPhasePlusBlock (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n)
        ((KnownZero.Total.circuit (m := m) (n := n) false phases).binaryMatrix
          (UnitarySource.interpretation U false true false)) =
        singularValuePolynomial (OrthogonalProjector.zeroAncilla m n) L
          (realPolynomialToComplex P) (projectedUnitaryBlock (OrthogonalProjector.zeroAncilla m n)
            (OrthogonalProjector.zeroAncilla m n) U) := by
      rw [KnownZero.Total.totalCircuit_matrix]
      simpa only [projectedOutputProjector, ite_self, phases, realPhases] using projected
    have same : ((expand raw).binaryMatrix
      (UnitarySource.interpretation U false true false))
      = (raw.binaryMatrix (UnitarySource.interpretation U false true false)) := by
      unfold UnitaryCircuit.binaryMatrix
      rw [toffoliExpansion_preserves_matrix]
    constructor
    · rw [same]
      dsimp only [raw]
      rw [KnownZero.Total.totalZeroBlockCircuit_matrix, KnownZero.Total.totalCircuit_matrix,
        Native.circuit_source_operator]
      simp only [realTarget, Nat.ne_of_gt positive, ↓reduceIte, phases]
    · rw [same]
      exact KnownZero.Total.totalZeroBlockCircuit_correct U false phases encoding hermitian
        (ReflectionQSPPhaseSynthesis.hasParity_realPolynomialToComplex source.parity) correct
  · rw [toffoliExpansion_expanded_eventCost, events]
    simp only [realBudget, Nat.ne_of_gt positive, ↓reduceIte]
  · apply (toffoliExpansion_depth_le raw).trans
    apply Nat.mul_le_mul_left 15
    change (KnownZero.Total.zeroBlockCircuit (m := m) (n := n) false phases).evaluatedEventDepth _
      ≤ _
    rw [KnownZero.Total.totalZeroBlockCircuit_depth, length]
    have bound := KnownZero.Total.totalPhaseDepth_le m n
    exact Nat.add_le_add_right (Nat.mul_le_mul_right L (by omega)) 2
  · apply (toffoliExpansion_native_gate_bound raw).trans
    apply Nat.mul_le_mul_left 15
    rw [events, nativeGateCount_add, nativeGateCount_nsmul, nativeGateCount_singleton_gate,
      Nat.mul_one]
    exact Nat.add_le_add_right (KnownZero.Total.totalRealBudget_native_gate_bound (m := m) (n :=
      n) false L) 2

/-- The independently selected target retains full-state action and every native resource bound. -/
lemma exists_real_target_execution (m n : Nat) {L : Nat} {P : Polynomial ℝ}
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P) :
    ∃ word : UnitaryCircuit AlgorithmGate.model (UnitarySource.model (m + n) false true false)
        (QuantumSignature.qubits ((1 + m) + n)).canonicalPlacement.layout,
      (∀ (U : UnitaryOperator (Qubits (m + n))) (A : HilbertOperator (Qubits n)),
        ExactBlockEncoding m n U A → A.IsHermitian →
      (word.binaryMatrix (UnitarySource.interpretation U false true false)) = realTarget U source ∧
      ExactBlockEncoding (1 + m) n (word.binaryMatrix
        (UnitarySource.interpretation U false true false))
        (polynomialOperator (realPolynomialToComplex P) A)) ∧
      word.eventCost = realBudget m n L ∧
      word.evaluatedEventDepth (fun _ => 1) ≤ 15 * ((40 * m + 4) * L + 2) ∧
      nativeGateCount word.eventCost ≤ 15 * ((40 * m + 3) * L + 2) ∧
      ResourcePool.count
        (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false))
        (.gate .toffoli) word.eventCost = 0 := by
  by_cases zero : L = 0
  · subst L
    let polynomial := realPolynomialToComplex P
    have bounded := Scalar.real_polynomial_normSq_bound source
    let word := Scalar.circuit (UnitarySource.model (m + n) false true false) m n
      (polynomial.coeff 0) (Scalar.constant_coefficient_bound polynomial bounded)
    have degree : polynomial.natDegree = 0 := by
      rw [realPolynomialToComplex_natDegree]
      exact Nat.eq_zero_of_le_zero source.degree_le
    refine ⟨word.castQubitWidth (Nat.add_assoc 1 m n).symm, ?_, ?_, ?_, ?_, ?_⟩
    · intro U A _encoding _hermitian
      constructor
      · rw [regroup_one_binaryMatrix, Scalar.circuit_source_matrix]
        simp only [realTarget, ↓reduceIte, polynomial]
      · rw [regroup_one_binaryMatrix]
        exact Scalar.scalarCircuit_constant_polynomial _ polynomial A degree bounded
          (UnitarySource.interpretation U false true false)
    · rw [UnitaryCircuit.castQubitWidth_eventCost, Scalar.circuit_events]
      simp only [realBudget, ↓reduceIte]
    · rw [UnitaryCircuit.castQubitWidth_evaluatedEventDepth, Scalar.circuit_depth]
      omega
    · rw [UnitaryCircuit.castQubitWidth_eventCost, Scalar.circuit_events,
        nativeGateCount_singleton_gate]
      omega
    · rw [UnitaryCircuit.castQubitWidth_eventCost, Scalar.circuit_events]
      simp [ResourcePool.count, ResourcePool.singleton]
  · obtain ⟨word, semantic, cost, depth, gates, toffoli⟩ :=
      positive_realization m n source (Nat.pos_of_ne_zero zero)
    refine ⟨word.castQubitWidth (Nat.add_assoc 1 m n).symm, ?_, ?_, ?_, ?_, ?_⟩
    · intro U A encoding hermitian
      simpa only [regroup_one_binaryMatrix] using semantic U A encoding hermitian
    · simpa only [UnitaryCircuit.castQubitWidth_eventCost] using cost
    · simpa only [UnitaryCircuit.castQubitWidth_evaluatedEventDepth] using depth
    · simpa only [UnitaryCircuit.castQubitWidth_eventCost] using gates
    · simpa only [UnitaryCircuit.castQubitWidth_eventCost] using toffoli

/-- The full independently specified unitary has the required Hermitian polynomial block. -/
public lemma realTarget_block {m n L : Nat} {P : Polynomial ℝ}
    (U : UnitaryOperator (Qubits (m + n))) (A : HilbertOperator (Qubits n))
    (encoding : ExactBlockEncoding m n U A) (hermitian : A.IsHermitian)
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P) :
    ExactBlockEncoding (1 + m) n (realTarget U source)
      (polynomialOperator (realPolynomialToComplex P) A) := by
  obtain ⟨word, semantic, _, _, _, _⟩ := exists_real_target_execution m n source
  obtain ⟨matrix, block⟩ := semantic U A encoding hermitian
  simpa only [matrix] using block

end
end QuantumAlg.QSP.MultiQubit.QSVT.Execution.Selected
