/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Certificate
import all QuantumAlg.Components.Gates.SingleQubit.First.Binary

/-!
# Actual Hadamard boundaries of the known-projector word

The two native boundary gates turn the plus-state block into the standard
zero-ancilla block. Their events and dependency depth remain part of execution.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero
noncomputable section

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))
  (positive : 0 < n) (allowControlled : Bool)

/-- A genuine native Hadamard on the phase wire, preserving the entire suffix. -/
def hadamard :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model U allowControlled true false)
      (ProjectorPhase.layout (m + n)) :=
  Gate.singleQubitAt (ProjectorPhase.layout (m + n))
    (UnitarySource.model U allowControlled true false) Gate.HOp (0 : Fin (1 + (m + n))) rfl

/-- Prepare and unprepare the plus phase state using two actual native gates. -/
def zeroBlockCircuit (phases : List ℝ) :
    UnitaryCircuit AlgorithmGate.model (UnitarySource.model U allowControlled true false)
      (ProjectorPhase.layout (m + n)) :=
  ((hadamard U allowControlled).seq
    (circuit U positive allowControlled phases)).seq (hadamard U allowControlled)

/-- The zero-block circuit has precisely the source Hadamard-conjugated operator. -/
theorem zeroBlockCircuit_matrix (phases : List ℝ) :
    (zeroBlockCircuit U positive allowControlled phases).binaryMatrix =
      phaseHadamardWrapperOperator
        (circuit U positive allowControlled phases).binaryMatrix := by
  rw [zeroBlockCircuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq]
  simp only [hadamard, Gate.singleQubitAt_first_binaryMatrix]
  apply Subtype.ext
  exact (Matrix.mul_assoc _ _ _).symm

/-- The two boundary Hadamards contribute two native events to the same circuit. -/
theorem zeroBlockCircuit_events (phases : List ℝ) :
    (zeroBlockCircuit U positive allowControlled phases).eventCost =
      (circuit U positive allowControlled phases).eventCost +
        2 • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model
            (UnitarySource.model U allowControlled true false)) (.gate .singleQubit) := by
  change (ResourcePool.singleton (model := .quantum AlgorithmGate.model
      (UnitarySource.model U allowControlled true false)) (.gate .singleQubit) +
    (circuit U positive allowControlled phases).eventCost) +
      ResourcePool.singleton (model := .quantum AlgorithmGate.model
        (UnitarySource.model U allowControlled true false)) (.gate .singleQubit) = _
  rw [two_smul]
  ac_rfl

/-- Exact sequential depth includes every native slot and the two boundary gates. -/
theorem zeroBlockCircuit_depth (phases : List ℝ) :
    (zeroBlockCircuit U positive allowControlled phases).evaluatedEventDepth (fun _ => 1) =
      (2 * (2 * m + EncodedBit.Word.OneDirtyLayout.gateCount m) + 2) * phases.length + 2 := by
  change (1 + (circuit U positive allowControlled phases).evaluatedEventDepth
    (fun _ => 1)) + 1 = _
  rw [circuit_depth]
  omega


/-- An independently certified projected block yields the original Hermitian polynomial block. -/
theorem zeroBlockCircuit_correct {L : Nat} {P : Polynomial ℂ}
    {A : HilbertOperator (Qubits n)} (phases : List ℝ)
    (source : ExactBlockEncoding m n U A) (hermitian : A.IsHermitian)
    (parity : HasParity P L)
    (correct : projectedPhasePlusBlock (OrthogonalProjector.zeroAncilla m n)
      (OrthogonalProjector.zeroAncilla m n)
      (circuit U positive allowControlled phases).binaryMatrix =
        singularValuePolynomial (OrthogonalProjector.zeroAncilla m n) L P
          (projectedUnitaryBlock (OrthogonalProjector.zeroAncilla m n)
            (OrthogonalProjector.zeroAncilla m n) U)) :
    ExactBlockEncoding (1 + m) n
      (reassociatePhaseAncillaOperator (m := m) (n := n)
        (zeroBlockCircuit U positive allowControlled phases).binaryMatrix)
      (polynomialOperator P A) := by
  have projected := congrArg (projectedBlock m n) correct
  have encoded := (exactBlockEncoding_to_projectedUnitaryEncoding source).block_eq
  rw [encoded] at projected
  rw [projectedBlock_singularValuePolynomial_zeroAncillaEmbeddedOperator_of_hermitian
    P A hermitian parity] at projected
  have actual : projectedBlock (1 + m) n
      (reassociatePhaseAncillaOperator (m := m) (n := n)
        (zeroBlockCircuit U positive allowControlled phases).binaryMatrix :
          HilbertOperator (Qubits ((1 + m) + n))) = polynomialOperator P A := by
    rw [zeroBlockCircuit_matrix, projectedBlock_reassociatedPhaseHadamardWrapper,
      ← projectedBlock_projectedPhasePlusBlock_zeroAncilla]
    exact projected
  exact ⟨fun row column => congrFun (congrFun actual row) column⟩

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero
