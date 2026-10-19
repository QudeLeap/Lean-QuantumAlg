/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.ControlWork.Intersection

/-!
# Complete phase semantics with a restored original control

The actual native word applies the negative source angle exactly when all
original controls are zero, and the positive source angle otherwise. The
construction and its matrix statement allow an empty signal register.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.ControlWork
noncomputable section

private lemma first_rotation_diagonal (k n : Nat) (oracles : OracleModel) (angle : ℝ)
    (environment : oracles.Interpretation) :
    (((Gate.singleQubitAt (layout k n) oracles (rotZStdOp angle)
      (0 : Fin (1 + (k + (1 + n)))) rfl).matrix environment) : HilbertOperator (layout k
        n).register) =
        Matrix.diagonal (fun basis => Gate.Rotation.Multiplex.weight angle
          (bits k n basis 0)) := by
  let application := Gate.singleQubitApplication (layout k n) (rotZStdOp angle)
    (0 : Fin (1 + (k + (1 + n)))) rfl
  have selected (basis : (layout k n).Basis) :
      QuantumSignature.qubitsIndexEquiv 1 (application.basisEquiv basis).1 =
        bits k n basis 0 := by
    have coordinates : (application.basisEquiv basis).1 =
        fun _ => bits k n basis 0 := by
      funext index
      fin_cases index
      apply Fin.ext
      rfl
    rw [coordinates]
    generalize bits k n basis 0 = bit
    fin_cases bit <;> rfl
  refine (application.application_operator_diagonal
    (fun basis => Gate.Rotation.Multiplex.weight angle (QuantumSignature.qubitsIndexEquiv 1 basis))
    (Gate.Rotation.Multiplex.token_diagonal angle)).trans ?_
  apply congrArg Matrix.diagonal
  funext basis
  rw [selected]

/-- The complete sign choice of the known-zero projector phase. -/
def phaseWeight (k n : Nat) (angle : ℝ)
    (basis : (layout k n).Basis) : ℂ :=
  Gate.Rotation.Multiplex.weight
    (if controlLabel k n (bits k n basis) = 0 ∧ bits k n basis (lastControl k n) = 0
      then -2 * angle else 2 * angle) (bits k n basis 0)

/-- Full original-coordinate matrix of the executed phase word, without a signal-width premise. -/
lemma controlWork_phase_matrix (k n : Nat) (oracles : OracleModel) (angle : ℝ)
    (environment : oracles.Interpretation) :
    (((phase k n oracles angle).matrix environment) : HilbertOperator (layout k n).register) =
      Matrix.diagonal (phaseWeight k n angle) := by
  rw [phase, UnitaryCircuit.seq_matrix]
  change _ * _ = _
  rw [controlWork_intersectionRotation_matrix, first_rotation_diagonal,
    Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext basis
  simp only [intersectionWeight, phaseWeight]
  by_cases selected : controlLabel k n (bits k n basis) = 0 ∧
      bits k n basis (lastControl k n) = 0 <;>
    simp only [selected, ite_false] <;>
    generalize bits k n basis 0 = bit
  all_goals
    fin_cases bit <;> simp [Gate.Rotation.Multiplex.weight, ← Complex.exp_add] <;>
      congr 1 <;> ring_nf

end
end QuantumAlg.QSP.MultiQubit.QSVT.ControlWork
