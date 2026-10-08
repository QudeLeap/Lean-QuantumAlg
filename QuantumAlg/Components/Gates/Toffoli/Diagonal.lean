/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Gates.Toffoli.Permutation
import all QuantumAlg.Components.Gates.ControlledPhase.Placement

/-!
# Native phases and weighted permutations in the Toffoli expansion

The diagonal entries are the original one-qubit phase factors. Weighted
permutation multiplication retains their exact complex phases on every input.
-/

namespace QuantumAlg.Gate.Toffoli
noncomputable section

private def weight (angle : ℝ) (bit : Fin 2) : ℂ :=
  if bit = 0 then 1 else Complex.exp ((angle : ℂ) * Complex.I)

private theorem phase_diagonal (oracles : OracleModel) (target : Fin 3) (angle : ℝ) :
    ((phase oracles target angle).matrix : HilbertOperator layout.register) =
      Matrix.diagonal (fun basis => weight angle (bits basis target)) := by
  let application := singleQubitApplication layout (phaseGateOp angle) target rfl
  have selected (basis : layout.register.Index) :
      QuantumSignature.qubitsIndexEquiv 1 (application.basisEquiv basis).1 = basis target := by
    have coordinates : (application.basisEquiv basis).1 = fun _ => basis target := by
      funext index
      fin_cases index
      apply Fin.ext
      rfl
    rw [coordinates]
    generalize basis target = bit
    fin_cases bit <;> rfl
  refine (application.application_operator_diagonal
    (fun basis => if QuantumSignature.qubitsIndexEquiv 1 basis = 0 then 1 else
      Complex.exp ((angle : ℂ) * Complex.I)) (ControlledPhase.phase_token_diagonal angle)).trans ?_
  apply congrArg Matrix.diagonal
  funext basis
  rw [selected]
  rfl

private def weighted (values : layout.register.Index → ℂ)
    (p : Equiv.Perm layout.register.Index) :
    HilbertOperator layout.register := fun row column => if p row = column then values row else 0

private theorem weighted_mul (values next : layout.register.Index → ℂ)
    (p q : Equiv.Perm layout.register.Index) :
    weighted values p * weighted next q =
      weighted (fun basis => values basis * next (p basis)) (p.trans q) := by
  ext row column
  rw [Matrix.mul_apply]
  simp only [weighted]
  rw [Finset.sum_eq_single (p row)]
  · simp [Equiv.trans_apply]
    rfl
  · intro other _ different
    simp [Ne.symm different]
  · simp

private theorem weighted_eq_diagonal (values : layout.register.Index → ℂ)
    (p : Equiv.Perm layout.register.Index) (fixed : ∀ basis, p basis = basis) :
    weighted values p = Matrix.diagonal values := by
  have same : p = Equiv.refl _ := Equiv.ext fixed
  subst p
  rfl

private theorem phase_weighted (oracles : OracleModel) (target : Fin 3) (angle : ℝ) :
    ((phase oracles target angle).matrix : HilbertOperator layout.register) =
      weighted (fun basis => weight angle (bits basis target)) (Equiv.refl _) := by
  rw [phase_diagonal]
  ext row column
  simp [weighted, Matrix.diagonal_apply]
  rfl

private theorem cnot_weighted (oracles : OracleModel) (control target : Fin 3)
    (distinct : control ≠ target) :
    ((cnot oracles control target distinct).matrix : HilbertOperator layout.register) =
      weighted (fun _ => 1) (permutation control target distinct) := by
  rw [cnot_matrix]
  ext row column
  simp [weighted, UnitaryOperator.ofPerm_entry]

end
end QuantumAlg.Gate.Toffoli
