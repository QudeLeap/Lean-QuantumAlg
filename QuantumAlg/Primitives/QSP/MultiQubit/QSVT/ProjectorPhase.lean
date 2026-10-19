/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Oracle.Reflection
public import QuantumAlg.Components.Gates.SingleQubit.First.Binary
public import QuantumAlg.Components.Gates.Rotation.Operator
import all QuantumAlg.Components.Oracle.Reflection
import all QuantumAlg.Components.Gates.SingleQubit.First.Binary
import all QuantumAlg.Components.Gates.Rotation.Operator
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Core.Base.Tensor.Basic

/-!
# Native projector phase blocks

The actual circuit sandwiches a native phase-ancilla rotation between two
implementations of the same projector-controlled NOT
[GSLW19, BlockHam.tex:883-887]. Those implementations may be declared queries
or expanded native circuits; their actual events and depth are retained.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.ProjectorPhase

noncomputable section

/-- One phase ancilla followed by the complete original source word. -/
public abbrev layout (width : Nat) :=
  (QuantumSignature.qubits (1 + width)).canonicalPlacement.layout

variable {oracles : OracleModel} {width : Nat}

/-- The source gadget consists of flip, rotation, flip in actual execution order. -/
def circuit (flip : UnitaryCircuit AlgorithmGate.model oracles (layout width)) (φ : ℝ) :
    UnitaryCircuit AlgorithmGate.model oracles (layout width) :=
  (flip.seq (Gate.singleQubitAt (layout width) oracles (rotZStdOp φ)
    (0 : Fin (1 + width)) rfl)).seq flip

/-- The actual circuit realizes the complete sandwich operator. -/
lemma circuit_matrix
    (flip : UnitaryCircuit AlgorithmGate.model oracles (layout width)) (φ : ℝ)
    (environment : oracles.Interpretation) :
    ((circuit flip φ).binaryMatrix environment) =
      (flip.binaryMatrix environment) *
        ((rotZStdOp φ).tensor (1 : UnitaryOperator (Qubits width)) * (flip.binaryMatrix
          environment)) := by
  rw [circuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, Gate.singleQubitAt_first_binaryMatrix]

/-- The resource pool includes both concrete flip implementations and the actual rotation. -/
lemma circuit_events
    (flip : UnitaryCircuit AlgorithmGate.model oracles (layout width)) (φ : ℝ) :
    (circuit flip φ).eventCost =
      flip.eventCost + ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit) + flip.eventCost := rfl

/-- No projector invocation is free in the sequential dependency depth. -/
lemma circuit_depth
    (flip : UnitaryCircuit AlgorithmGate.model oracles (layout width)) (φ : ℝ) :
    (circuit flip φ).evaluatedEventDepth (fun _ => 1) =
      2 * flip.evaluatedEventDepth (fun _ => 1) + 1 := by
  change (flip.evaluatedEventDepth (fun _ => 1) + 1) +
    flip.evaluatedEventDepth (fun _ => 1) = _
  omega

private lemma x_rotation_x (φ : ℝ) :
    (Gate.XOp : HilbertOperator (Qubits 1)) *
        (rotZStdOp φ : HilbertOperator (Qubits 1)) *
        (Gate.XOp : HilbertOperator (Qubits 1)) =
      (rotZStdOp (-φ) : HilbertOperator (Qubits 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Gate.XOp, UnitaryOperator.ofPerm, rotZStdOp, rotZOp, Matrix.mul_apply] <;>
    congr 1 <;> ring

/-- Correct projector implementations give the source's two complementary phase branches. -/
lemma circuit_projector_matrix
    (flip : UnitaryCircuit AlgorithmGate.model oracles (layout width))
    (P : OrthogonalProjector width)
    (environment : oracles.Interpretation)
    (hflip : (flip.binaryMatrix environment) = OrthogonalProjector.controlledNotOp P) (φ : ℝ) :
    (((circuit flip φ).binaryMatrix environment) : HilbertOperator (Qubits (1 + width))) =
      HilbertOperator.tensor (rotZStdOp (-φ) : HilbertOperator (Qubits 1)) P.op +
        HilbertOperator.tensor (rotZStdOp φ : HilbertOperator (Qubits 1))
          (OrthogonalProjector.complement P) := by
  rw [circuit_matrix, hflip]
  change
    (HilbertOperator.tensor (Gate.XOp : HilbertOperator (Qubits 1)) P.op +
      HilbertOperator.tensor (1 : HilbertOperator (Qubits 1))
        (OrthogonalProjector.complement P)) *
      (HilbertOperator.tensor (rotZStdOp φ : HilbertOperator (Qubits 1))
        (1 : HilbertOperator (Qubits width)) *
        (HilbertOperator.tensor (Gate.XOp : HilbertOperator (Qubits 1)) P.op +
          HilbertOperator.tensor (1 : HilbertOperator (Qubits 1))
            (OrthogonalProjector.complement P))) = _
  rw [← Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  repeat rw [HilbertOperator.tensor_mul_tensor]
  rw [x_rotation_x]
  simp only [Matrix.one_mul, Matrix.mul_one]
  rw [P.idempotent, OrthogonalProjector.complement_mul P,
    OrthogonalProjector.mul_complement P, OrthogonalProjector.complement_sq P]
  simp [HilbertOperator.tensor_zero]

end

end QuantumAlg.QSP.MultiQubit.QSVT.ProjectorPhase
