/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.ControlWork.Resources
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.ControlWork.Permutation
import all QuantumAlg.Components.Gates.Rotation.Multiplex.Binary

/-!
# Diagonal phases of the restored first-control rotation

The phase is selected by the first k original control coordinates. The final
control and every signal coordinate remain outside that condition.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.ControlWork
noncomputable section

/-- The binary label of only the first k original control wires. -/
def controlLabel (k n : Nat) (basis : Fin (1 + (k + (1 + n))) → Fin 2) : Fin (2 ^ k) :=
  BinaryBasis.bigEndianEquiv k
    (fun index => basis (Fin.natAdd 1 (Fin.castAdd (1 + n) index)))

private theorem controlLabel_decoded (k n : Nat) (phase : Fin 2)
    (controls : Fin (2 ^ k)) (suffix : Fin (2 ^ (1 + n))) :
    controlLabel k n ((QuantumSignature.qubitsIndexEquiv (1 + (k + (1 + n)))).symm
      (prodEquiv (phase, prodEquiv (controls, suffix)))) = controls := by
  have coordinates :
      (fun index : Fin k =>
        (QuantumSignature.qubitsIndexEquiv (1 + (k + (1 + n)))).symm
          (prodEquiv (phase, prodEquiv (controls, suffix)))
          (Fin.natAdd 1 (Fin.castAdd (1 + n) index))) =
        (BinaryBasis.bigEndianEquiv k).symm controls := by
    funext index
    exact (BinaryBasis.bigEndianEquiv_prod_right (leftWidth := 1) (rightWidth := k + (1 + n))
      phase (prodEquiv (controls, suffix))
      (Fin.castAdd (1 + n) index)).trans
        (BinaryBasis.bigEndianEquiv_prod_left (leftWidth := k) (rightWidth := 1 + n)
          controls suffix index)
  exact (congrArg (BinaryBasis.bigEndianEquiv k) coordinates).trans
    ((BinaryBasis.bigEndianEquiv k).apply_symm_apply controls)

private theorem phase_decoded (k n : Nat) (phase : Fin 2)
    (controls : Fin (2 ^ k)) (suffix : Fin (2 ^ (1 + n))) :
    (QuantumSignature.qubitsIndexEquiv (1 + (k + (1 + n)))).symm
      (prodEquiv (phase, prodEquiv (controls, suffix)))
      (0 : Fin (1 + (k + (1 + n)))) = phase := by
  have first := BinaryBasis.bigEndianEquiv_prod_left (leftWidth := 1) (rightWidth := k + (1 + n))
    phase
    (prodEquiv (controls, suffix)) (0 : Fin 1)
  have one : (BinaryBasis.bigEndianEquiv 1).symm phase 0 = phase := by
    fin_cases phase <;> rfl
  exact first.trans one

/-- Basis-dependent scalar of the first-control rotation. -/
def firstWeight (k n : Nat) (angle : ℝ)
    (basis : (layout k n).Basis) : ℂ :=
  Gate.Rotation.Multiplex.weight (if controlLabel k n (bits k n basis) = 0 then angle else 0)
    (bits k n basis 0)

/-- The complete first-control operator is diagonal on the original physical coordinates. -/
theorem controlWork_firstRotation_diagonal (k n : Nat) (oracles : OracleModel) (angle : ℝ) :
    ((firstRotation k n oracles angle).matrix : HilbertOperator (layout k n).register) =
      Matrix.diagonal (firstWeight k n angle) := by
  ext row column
  obtain ⟨rowLabel, rfl⟩ :=
    (QuantumSignature.qubitsIndexEquiv (1 + (k + (1 + n)))).symm.surjective row
  obtain ⟨columnLabel, rfl⟩ :=
    (QuantumSignature.qubitsIndexEquiv (1 + (k + (1 + n)))).symm.surjective column
  obtain ⟨⟨rowPhase, rowRest⟩, rfl⟩ := prodEquiv.surjective rowLabel
  obtain ⟨⟨rowControls, rowSuffix⟩, rfl⟩ := prodEquiv.surjective rowRest
  obtain ⟨⟨phase, rest⟩, rfl⟩ := prodEquiv.surjective columnLabel
  obtain ⟨⟨controls, suffix⟩, rfl⟩ := prodEquiv.surjective rest
  have entry := congrFun (congrFun (controlWork_firstRotation_matrix k n oracles angle)
    (prodEquiv (rowPhase, prodEquiv (rowControls, rowSuffix))))
      (prodEquiv (phase, prodEquiv (controls, suffix)))
  change (firstRotation k n oracles angle).matrix _ _ = _ at entry
  rw [entry]
  change _ = @ite ℂ
    ((QuantumSignature.qubitsIndexEquiv (1 + (k + (1 + n)))).symm
      (prodEquiv (rowPhase, prodEquiv (rowControls, rowSuffix))) =
      (QuantumSignature.qubitsIndexEquiv (1 + (k + (1 + n)))).symm
        (prodEquiv (phase, prodEquiv (controls, suffix))))
    ((QuantumSignature.qubits (1 + (k + (1 + n)))).register.decEq _ _)
    (firstWeight k n angle _) 0
  unfold firstWeight bits
  rw [controlLabel_decoded, phase_decoded]
  by_cases zero : controls = 0 <;>
    by_cases sameControls : rowControls = controls <;>
    by_cases sameSuffix : rowSuffix = suffix <;>
    fin_cases rowPhase <;> fin_cases phase <;>
    simp [OrthogonalProjector.zeroAncilla, OrthogonalProjector.tensor,
      OrthogonalProjector.zero, OrthogonalProjector.basis, OrthogonalProjector.basisOp,
      OrthogonalProjector.identity, OrthogonalProjector.complement, HilbertOperator.tensor_apply,
      rotZStdOp, rotZOp, Gate.Rotation.Multiplex.weight, Matrix.one_apply,
      zero, sameControls, sameSuffix]
  all_goals simp_all

end
end QuantumAlg.QSP.MultiQubit.QSVT.ControlWork
