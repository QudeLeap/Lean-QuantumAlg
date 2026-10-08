/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Construction
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Queries.Matrix
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Reflection.Laws
import all QuantumAlg.Algorithms.QPE.ControlledAction
import all QuantumAlg.Algorithms.QPE.Analysis
import all QuantumAlg.Components.Oracle.AmplitudeAmplification
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Powers
import all QuantumAlg.Primitives.AmplitudeAmplification.Construction

/-!
# Full source-step operator of the actual elementary sequence

Both preparations remain ordinary queries. On control zero their U-dagger
and U actions cancel on the entire source space; on control one the exact
source product U S0 U-dagger R-good is applied. The elementary reflection
restores all phase and work values before this unrestricted equality is used.
-/

namespace QuantumAlg.AmplitudeEstimation.Elementary

noncomputable section

private theorem step_applyVec_tensor {n t : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (stage : Fin t)
    (phase : Fin (2 ^ phaseWidth t n)) (target : HilbertVector (Qubits n)) :
    (step U good stage).binaryMatrix.applyVec
        (HilbertVector.tensor
          (NormalizedVector.ket (R := Qubits (phaseWidth t n)) phase).vec target) =
      HilbertVector.tensor (NormalizedVector.ket (R := Qubits (phaseWidth t n)) phase).vec
        (if phase.val.testBit (extendedStage n stage).val then
          (U * (ZeroReflection.zeroReflectionOperator n *
            (U.dagger * OrthogonalProjector.rankOnePhaseReflectionOp good))).applyVec target
        else target) := by
  rw [step, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryOperator.mul_applyVec, UnitaryOperator.mul_applyVec,
    UnitaryOperator.mul_applyVec]
  rw [preparation_matrix, inversePreparation_matrix, reflection_matrix,
    controlledGoodReflection_matrix, qpeControlledBitOp_applyVec_ket_tensor,
    UnitaryOperator.tensor_applyVec_tensor, UnitaryOperator.one_applyVec,
    qpeControlledBitOp_applyVec_ket_tensor, UnitaryOperator.tensor_applyVec_tensor,
    UnitaryOperator.one_applyVec]
  cases active : phase.val.testBit (extendedStage n stage).val
  · simp [AmplitudeAmplification.unitary_applyVec_dagger_applyVec]
  · simp [UnitaryOperator.mul_applyVec]

/-- The actual source sequence equals control of the complete source product on every state. -/
theorem step_matrix {n t : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (stage : Fin t) :
    (step U good stage).binaryMatrix = qpeControlledBitOp (phaseWidth t n)
      (U * (ZeroReflection.zeroReflectionOperator n *
        (U.dagger * OrthogonalProjector.rankOnePhaseReflectionOp good)))
      (extendedStage n stage) := by
  apply Subtype.ext
  ext row column
  obtain ⟨⟨phase, source⟩, rfl⟩ :=
    (prodEquiv (m := phaseWidth t n) (n := n)).surjective column
  have tensorKet :
      HilbertVector.tensor (NormalizedVector.ket (R := Qubits (phaseWidth t n)) phase).vec
          (NormalizedVector.ket (R := Qubits n) source).vec =
        (NormalizedVector.ket (R := Qubits (totalQubits t n)) (prodEquiv (phase, source))).vec :=
    congrArg NormalizedVector.vec (NormalizedVector.tensor_ket phase source)
  have action := (step_applyVec_tensor U good stage phase
    (NormalizedVector.ket (R := Qubits n) source).vec).trans
      (qpeControlledBitOp_applyVec_ket_tensor (phaseWidth t n)
        (U * (ZeroReflection.zeroReflectionOperator n *
          (U.dagger * OrthogonalProjector.rankOnePhaseReflectionOp good)))
        (extendedStage n stage) phase (NormalizedVector.ket (R := Qubits n) source).vec).symm
  rw [tensorKet] at action
  simpa only [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket] using
    congrArg (fun state : HilbertVector (Qubits (totalQubits t n)) => state row) action

/-- Actual stage repetitions multiply the selected exponent by the original binary power. -/
theorem powerStage_matrix {n t : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (stage : Fin t) :
    (powerStage U good stage).binaryMatrix = qpeExponentOp (phaseWidth t n)
      (U * (ZeroReflection.zeroReflectionOperator n *
        (U.dagger * OrthogonalProjector.rankOnePhaseReflectionOp good)))
      (fun phase => 2 ^ stage.val * (phase.val.testBit (extendedStage n stage).val).toNat) := by
  rw [powerStage, UnitaryCircuit.unitaryCircuit_binaryMatrix_iterate]
  rw [step_matrix, qpeControlledBitOp, qpeExponentOp_pow]

end

end QuantumAlg.AmplitudeEstimation.Elementary
