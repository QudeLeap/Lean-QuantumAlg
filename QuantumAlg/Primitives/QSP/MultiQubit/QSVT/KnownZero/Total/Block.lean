/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Certificate
import all QuantumAlg.Components.Gates.SingleQubit.First.Binary

/-!
# Actual Hadamard boundaries of the known-projector word

The two native boundary gates turn the plus-state block into the standard
zero-ancilla block. Their events and dependency depth remain part of execution.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total
noncomputable section

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))
  (allowControlled : Bool)

/-- Prepare and unprepare the plus phase state using two actual native gates. -/
def zeroBlockCircuit (phases : List ℝ) :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model (m + n) allowControlled true false)
      (ProjectorPhase.layout (m + n)) :=
  ((KnownZero.hadamard (m := m) (n := n) allowControlled).seq
    (circuit (m := m) (n := n) allowControlled phases)).seq (KnownZero.hadamard (m := m) (n := n)
      allowControlled)

/-- The zero-block circuit has precisely the source Hadamard-conjugated operator. -/
lemma totalZeroBlockCircuit_matrix (phases : List ℝ) :
    ((zeroBlockCircuit (m := m) (n := n) allowControlled phases).binaryMatrix
      (UnitarySource.interpretation U allowControlled true false)) =
      phaseHadamardWrapperOperator
        ((circuit (m := m) (n := n) allowControlled phases).binaryMatrix
          (UnitarySource.interpretation U allowControlled true false)) := by
  rw [zeroBlockCircuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq]
  simp only [KnownZero.hadamard, Gate.singleQubitAt_first_binaryMatrix]
  apply Subtype.ext
  exact (Matrix.mul_assoc _ _ _).symm

/-- The two boundary Hadamards contribute two native events to the same circuit. -/
lemma totalZeroBlockCircuit_events (phases : List ℝ) :
    (zeroBlockCircuit (m := m) (n := n) allowControlled phases).eventCost =
      (circuit (m := m) (n := n) allowControlled phases).eventCost +
        2 • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model
            (UnitarySource.model (m + n) allowControlled true false)) (.gate .singleQubit) := by
  change (ResourcePool.singleton (model := .quantum AlgorithmGate.model
      (UnitarySource.model (m + n) allowControlled true false)) (.gate .singleQubit) +
    (circuit (m := m) (n := n) allowControlled phases).eventCost) +
      ResourcePool.singleton (model := .quantum AlgorithmGate.model
        (UnitarySource.model (m + n) allowControlled true false)) (.gate .singleQubit) = _
  rw [two_smul]
  ac_rfl

/-- Exact sequential depth includes every native slot and the two boundary gates. -/
lemma totalZeroBlockCircuit_depth (phases : List ℝ) :
    (zeroBlockCircuit (m := m) (n := n) allowControlled phases).evaluatedEventDepth (fun _ => 1) =
      (phaseDepth m n + 1) * phases.length + 2 := by
  change (1 + (circuit (m := m) (n := n) allowControlled phases).evaluatedEventDepth
    (fun _ => 1)) + 1 = _
  rw [totalCircuit_depth]
  omega


/-- An independently certified projected block yields the original Hermitian polynomial block. -/
lemma totalZeroBlockCircuit_correct {L : Nat} {P : Polynomial ℂ}
    {A : HilbertOperator (Qubits n)} (phases : List ℝ)
    (source : ExactBlockEncoding m n U A) (hermitian : A.IsHermitian)
    (parity : HasParity P L)
    (correct : projectedPhasePlusBlock (OrthogonalProjector.zeroAncilla m n)
      (OrthogonalProjector.zeroAncilla m n)
      ((circuit (m := m) (n := n) allowControlled phases).binaryMatrix
        (UnitarySource.interpretation U allowControlled true false)) =
        singularValuePolynomial (OrthogonalProjector.zeroAncilla m n) L P
          (projectedUnitaryBlock (OrthogonalProjector.zeroAncilla m n)
            (OrthogonalProjector.zeroAncilla m n) U)) :
    ExactBlockEncoding (1 + m) n
      (reassociatePhaseAncillaOperator (m := m) (n := n)
        ((zeroBlockCircuit (m := m) (n := n) allowControlled phases).binaryMatrix
          (UnitarySource.interpretation U allowControlled true false)))
      (polynomialOperator P A) := by
  have projected := congrArg (projectedBlock m n) correct
  have encoded := (exactBlockEncoding_to_projectedUnitaryEncoding source).block_eq
  rw [encoded] at projected
  rw [projectedBlock_singularValuePolynomial_zeroAncillaEmbeddedOperator_of_hermitian
    P A hermitian parity] at projected
  have actual : projectedBlock (1 + m) n
      (reassociatePhaseAncillaOperator (m := m) (n := n)
        ((zeroBlockCircuit (m := m) (n := n) allowControlled phases).binaryMatrix
          (UnitarySource.interpretation U allowControlled true false)) :
          HilbertOperator (Qubits ((1 + m) + n))) = polynomialOperator P A := by
    rw [totalZeroBlockCircuit_matrix, projectedBlock_reassociatedPhaseHadamardWrapper,
      ← projectedBlock_projectedPhasePlusBlock_zeroAncilla]
    exact projected
  exact ⟨fun row column => congrFun (congrFun actual row) column⟩

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total
