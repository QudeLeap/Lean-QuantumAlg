/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.ControlWork.Resources
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Phase

/-!
# Four simultaneous native phases with restored control work

Two selectors choose only rotation angles. All four branches share the same
restored-control flips, without controlled source queries or additional work.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.ControlWork.Four
noncomputable section

abbrev layout (k n : Nat) := SharedFour.layout k (1 + n)

private def lift {k n : Nat} {oracles : OracleModel}
    (word : UnitaryCircuit AlgorithmGate.model oracles (ControlWork.layout k n)) :
    UnitaryCircuit AlgorithmGate.model oracles (layout k n) :=
  UnitaryCircuit.onBinarySuffix 1 (UnitaryCircuit.onBinarySuffix 1 word)

private def rotation (k n : Nat) (oracles : OracleModel) (a b c d : ℝ) :
    UnitaryCircuit AlgorithmGate.model oracles (layout k n) :=
  Gate.Rotation.Multiplex.Four.onPrefix oracles (k + (1 + n)) a b c d

private theorem rotation_matrix (k n : Nat) (oracles : OracleModel) (a b c d : ℝ) :
    ((rotation k n oracles a b c d).binaryMatrix :
      HilbertOperator (Qubits (1 + (1 + (1 + (k + (1 + n))))))) =
      Native.branchMatrix
        (Native.branchMatrix (HilbertOperator.tensor (rotZStdOp a) 1)
          (HilbertOperator.tensor (rotZStdOp b) 1))
        (Native.branchMatrix (HilbertOperator.tensor (rotZStdOp c) 1)
          (HilbertOperator.tensor (rotZStdOp d) 1)) :=
  Gate.Rotation.Multiplex.Four.fourRotation_prefix_binaryMatrix oracles (k + (1 + n)) a b c d

/-- Four first-control rotations share both restored native flip executions. -/
def firstRotation (k n : Nat) (oracles : OracleModel) (a b c d : ℝ) :
    UnitaryCircuit AlgorithmGate.model oracles (layout k n) :=
  let flip := lift (KnownZero.flip k (1 + n) (by omega) oracles)
  (((rotation k n oracles (a / 2) (b / 2) (c / 2) (d / 2)).seq flip).seq
    (rotation k n oracles (-(a / 2)) (-(b / 2)) (-(c / 2)) (-(d / 2)))).seq flip

/-- Four intersection rotations reuse the final original control and restore it. -/
def intersectionRotation (k n : Nat) (oracles : OracleModel) (a b c d : ℝ) :
    UnitaryCircuit AlgorithmGate.model oracles (layout k n) :=
  let flip := lift (ControlWork.lastFlip k n oracles)
  (((firstRotation k n oracles (a / 2) (b / 2) (c / 2) (d / 2)).seq flip).seq
    (firstRotation k n oracles (-(a / 2)) (-(b / 2)) (-(c / 2)) (-(d / 2)))).seq flip

/-- Five four-angle rotations and shared flips implement all four full source phases. -/
def phase (k n : Nat) (oracles : OracleModel) (a b c d : ℝ) :
    UnitaryCircuit AlgorithmGate.model oracles (layout k n) :=
  (rotation k n oracles (2 * a) (2 * b) (2 * c) (2 * d)).seq
    (intersectionRotation k n oracles (-4 * a) (-4 * b) (-4 * c) (-4 * d))

private theorem lift_matrix {k n : Nat} {oracles : OracleModel}
    (word : UnitaryCircuit AlgorithmGate.model oracles (ControlWork.layout k n)) :
    ((lift word).binaryMatrix : HilbertOperator (Qubits (1 + (1 + (1 + (k + (1 + n))))))) =
      Native.branchMatrix (Native.branchMatrix word.binaryMatrix word.binaryMatrix)
        (Native.branchMatrix word.binaryMatrix word.binaryMatrix) := by
  simp only [lift, UnitaryCircuit.unitaryCircuit_onBinarySuffix_binaryMatrix,
    UnitaryOperator.coe_tensor]
  rw [Native.branchMatrix_same, Native.branchMatrix_same]
  rfl

/-- The shared first-control schedule has exactly the four original branch operators. -/
theorem controlWork_fourFirstRotation_matrix (k n : Nat) (oracles : OracleModel)
    (a b c d : ℝ) :
    ((firstRotation k n oracles a b c d).binaryMatrix :
      HilbertOperator (Qubits (1 + (1 + (1 + (k + (1 + n))))))) =
      Native.branchMatrix
        (Native.branchMatrix (ControlWork.firstRotation k n oracles a).binaryMatrix
          (ControlWork.firstRotation k n oracles b).binaryMatrix)
        (Native.branchMatrix (ControlWork.firstRotation k n oracles c).binaryMatrix
          (ControlWork.firstRotation k n oracles d).binaryMatrix) := by
  simp only [firstRotation, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    Submonoid.coe_mul, lift_matrix, rotation_matrix]
  repeat rw [Native.branchMatrix_mul]
  simp only [ControlWork.firstRotation, ProjectorPhase.controlledRotation, ProjectorPhase.circuit,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, Gate.singleQubitAt_first_binaryMatrix,
    Submonoid.coe_mul, UnitaryOperator.coe_tensor]
  simp only [Matrix.mul_assoc]
  rfl

/-- Every branch includes the same two final-control flips and its own angles. -/
theorem controlWork_fourIntersection_matrix (k n : Nat) (oracles : OracleModel)
    (a b c d : ℝ) :
    ((intersectionRotation k n oracles a b c d).binaryMatrix :
      HilbertOperator (Qubits (1 + (1 + (1 + (k + (1 + n))))))) =
      Native.branchMatrix
        (Native.branchMatrix (ControlWork.intersectionRotation k n oracles a).binaryMatrix
          (ControlWork.intersectionRotation k n oracles b).binaryMatrix)
        (Native.branchMatrix (ControlWork.intersectionRotation k n oracles c).binaryMatrix
          (ControlWork.intersectionRotation k n oracles d).binaryMatrix) := by
  simp only [intersectionRotation, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    Submonoid.coe_mul, lift_matrix, controlWork_fourFirstRotation_matrix]
  repeat rw [Native.branchMatrix_mul]
  simp only [ControlWork.intersectionRotation, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    Submonoid.coe_mul]

/-- The complete shared native word realizes all four full control-work phase operators. -/
theorem controlWork_fourPhase_matrix (k n : Nat) (oracles : OracleModel)
    (a b c d : ℝ) :
    ((phase k n oracles a b c d).binaryMatrix :
      HilbertOperator (Qubits (1 + (1 + (1 + (k + (1 + n))))))) =
      Native.branchMatrix
        (Native.branchMatrix (ControlWork.phase k n oracles a).binaryMatrix
          (ControlWork.phase k n oracles b).binaryMatrix)
        (Native.branchMatrix (ControlWork.phase k n oracles c).binaryMatrix
          (ControlWork.phase k n oracles d).binaryMatrix) := by
  simp only [phase, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, Submonoid.coe_mul,
    controlWork_fourIntersection_matrix, rotation_matrix]
  repeat rw [Native.branchMatrix_mul]
  simp only [ControlWork.phase, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    Gate.singleQubitAt_first_binaryMatrix, Submonoid.coe_mul, UnitaryOperator.coe_tensor]
  rfl

/-- The shared schedule charges five ten-step rotations and all restored work. -/
theorem controlWork_fourPhase_depth (k n : Nat) (oracles : OracleModel)
    (a b c d : ℝ) :
    (phase k n oracles a b c d).evaluatedEventDepth (fun _ => 1) =
      4 * (2 * k + EncodedBit.Word.OneDirtyLayout.gateCount k) + 56 := by
  simp only [phase, intersectionRotation, firstRotation, rotation, lift,
    UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_unit_depth,
    Gate.Rotation.Multiplex.Four.fourRotation_prefix_depth, KnownZero.flip_depth,
    ControlWork.controlWork_lastFlip_depth]
  omega

end
end QuantumAlg.QSP.MultiQubit.QSVT.ControlWork.Four
