/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.ControlWork.Permutation
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.ControlWork.Diagonal

/-!
# Exact intersection-controlled rotation on the original wires

The final-control conjugation changes the sign of the first-control rotation
on precisely the required branch. Its two masks leave all controls intact.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.ControlWork
noncomputable section

private lemma last_involutive (k n : Nat) : Function.Involutive (lastPermutation k n) := by
  intro basis
  apply bits_injective k n
  rw [lastPermutation_bits, lastPermutation_bits]
  have distinct := lastControl_ne_phase k n
  funext index
  by_cases phase : index = (0 : Fin (1 + (k + (1 + n))))
  · subst index
    by_cases zero : bits k n basis (lastControl k n) = 0
    · simp only [Function.update_self, Function.update_of_ne distinct, zero, ite_true]
      generalize bits k n basis 0 = value
      fin_cases value <;> rfl
    · simp [distinct, zero]
  · simp [Function.update_apply, phase]

private lemma controlLabel_last (k n : Nat)
    (basis : (layout k n).Basis) :
    controlLabel k n (bits k n (lastPermutation k n basis)) =
      controlLabel k n (bits k n basis) := by
  unfold controlLabel
  apply congrArg (BinaryBasis.bigEndianEquiv k)
  funext index
  rw [lastPermutation_bits]
  apply Function.update_of_ne
  intro same
  have values := congrArg Fin.val same
  change 1 + index.val = 0 at values
  omega

/-- Exact scalar chosen by all original controls together. -/
def intersectionWeight (k n : Nat) (angle : ℝ)
    (basis : (layout k n).Basis) : ℂ :=
  Gate.Rotation.Multiplex.weight
    (if controlLabel k n (bits k n basis) = 0 ∧ bits k n basis (lastControl k n) = 0
      then angle else 0) (bits k n basis 0)

private lemma half_weights (k n : Nat) (angle : ℝ)
    (basis : (layout k n).Basis) :
    firstWeight k n (-(angle / 2)) (lastPermutation k n basis) *
      firstWeight k n (angle / 2) basis = intersectionWeight k n angle basis := by
  have phase := congrFun (lastPermutation_bits k n basis)
    (0 : Fin (1 + (k + (1 + n))))
  rw [Function.update_self] at phase
  simp only [firstWeight, controlLabel_last, phase, intersectionWeight]
  by_cases first : controlLabel k n (bits k n basis) = 0 <;>
    by_cases last : bits k n basis (lastControl k n) = 0 <;>
    simp only [first, last, ite_true, ite_false] <;>
    generalize bits k n basis 0 = target
  all_goals
    fin_cases target <;> simp [Gate.Rotation.Multiplex.weight, Fin.add, ← Complex.exp_add] <;>
      congr 1 <;> ring_nf <;> simp

/-- The full actual intersection word is diagonal with exactly the all-controls-zero phase. -/
lemma controlWork_intersectionRotation_matrix (k n : Nat) (oracles : OracleModel) (angle : ℝ)
    (environment : oracles.Interpretation) :
    (((intersectionRotation k n oracles angle).matrix environment) : HilbertOperator (layout k
      n).register) =
      Matrix.diagonal (intersectionWeight k n angle) := by
  simp only [intersectionRotation, UnitaryCircuit.seq_matrix, Submonoid.coe_mul,
    controlWork_lastFlip_matrix, controlWork_firstRotation_diagonal]
  rw [← mul_assoc, ← mul_assoc,
    Gate.Rotation.Multiplex.conjugate_diagonal (layout k n).register
      (lastPermutation k n) (last_involutive k n), Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext basis
  exact half_weights k n angle basis

end
end QuantumAlg.QSP.MultiQubit.QSVT.ControlWork
