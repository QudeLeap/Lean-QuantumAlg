/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.ProjectorPhase
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Source

/-!
# Controlled rotations from a restored projector flip

Two half-angle rotations and two executions of a supplied projector flip
implement a rotation only on that projector's range. The complete complement
is exactly the identity, including its phase and any restored work register.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.ProjectorPhase
noncomputable section

variable {oracles : OracleModel} {width : Nat}

/-- Native half rotation followed by the opposite-angle flip sandwich. -/
def controlledRotation (flip : UnitaryCircuit AlgorithmGate.model oracles (layout width))
    (angle : ℝ) : UnitaryCircuit AlgorithmGate.model oracles (layout width) :=
  (Gate.singleQubitAt (layout width) oracles (rotZStdOp (angle / 2))
    (0 : Fin (1 + width)) rfl).seq (circuit flip (-(angle / 2)))

private lemma standard_rotation_mul (a b : ℝ) :
    (rotZStdOp a : HilbertOperator (Qubits 1)) *
      (rotZStdOp b : HilbertOperator (Qubits 1)) =
        (rotZStdOp (a + b) : HilbertOperator (Qubits 1)) := by
  simp only [rotZStdOp]
  rw [rotZ_op_mul, show -(a / 2) + -(b / 2) = -((a + b) / 2) by ring]

/-- The actual circuit rotates the projector range and preserves its orthogonal complement. -/
lemma controlledRotation_matrix
    (flip : UnitaryCircuit AlgorithmGate.model oracles (layout width))
    (P : OrthogonalProjector width)
    (environment : oracles.Interpretation)
    (correct : (flip.binaryMatrix environment)
      = OrthogonalProjector.controlledNotOp P) (angle : ℝ) :
    (((controlledRotation flip angle).binaryMatrix environment) : HilbertOperator (Qubits (1 +
      width))) =
      HilbertOperator.tensor (rotZStdOp angle : HilbertOperator (Qubits 1)) P.op +
      HilbertOperator.tensor (1 : HilbertOperator (Qubits 1))
        (OrthogonalProjector.complement P) := by
  rw [controlledRotation, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq]
  change _ * _ = _
  rw [circuit_projector_matrix flip P environment correct, Gate.singleQubitAt_first_binaryMatrix]
  change (_ + _) * HilbertOperator.tensor _ 1 = _
  rw [Matrix.add_mul, HilbertOperator.tensor_mul_tensor, HilbertOperator.tensor_mul_tensor]
  simp only [Matrix.mul_one, neg_neg]
  repeat rw [standard_rotation_mul]
  rw [show angle / 2 + angle / 2 = angle by ring,
    show -(angle / 2) + angle / 2 = 0 by ring, rotZStdOp_zero]
  rfl

/-- Both flip executions and both native rotations are charged to the same execution. -/
lemma controlledRotation_events
    (flip : UnitaryCircuit AlgorithmGate.model oracles (layout width)) (angle : ℝ) :
    (controlledRotation flip angle).eventCost =
      2 • flip.eventCost + 2 • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit) := by
  rw [controlledRotation, UnitaryCircuit.seq_eventCost, circuit_events,
    Gate.singleQubitAt_eventCost, two_nsmul, two_nsmul]
  ac_rfl

/-- Full sequential depth includes both restored flips and both half rotations. -/
lemma controlledRotation_depth
    (flip : UnitaryCircuit AlgorithmGate.model oracles (layout width)) (angle : ℝ) :
    (controlledRotation flip angle).evaluatedEventDepth (fun _ => 1) =
      2 * flip.evaluatedEventDepth (fun _ => 1) + 2 := by
  rw [controlledRotation, UnitaryCircuit.evaluatedEventDepth_seq, circuit_depth]
  change 1 + (2 * flip.evaluatedEventDepth (fun _ => 1) + 1) = _
  omega

end
end QuantumAlg.QSP.MultiQubit.QSVT.ProjectorPhase
