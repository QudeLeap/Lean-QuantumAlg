/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Gates.Rotation.Multiplex.Four
import all QuantumAlg.Core.Base.Gate.Placement.Permutation
import all QuantumAlg.Components.GateModel.Algorithm.Permutation

/-!
# Full matrix semantics of the four-angle native selector

The outer CNOT toggles only the phase wire. Its conjugation changes the sign
of the difference rotation, retaining both original selector values.
-/

namespace QuantumAlg.Gate.Rotation.Multiplex.Four
noncomputable section

private def application := Gate.cnotApplication layout 0 2 (by decide) rfl rfl

private def permutation : Equiv.Perm layout.Basis :=
  application.liftPermutation AlgorithmGate.cnotPermutation

private theorem permutation_coordinates (basis : layout.Basis) :
    permutation basis = ![basis 0, basis 1, Fin.add (n := 2) (basis 0) (basis 2)] := by
  apply (application.liftPermutation_eq_iff AlgorithmGate.cnotPermutation _ _).mpr
  constructor
  · have selected : (application.basisEquiv basis).1 = ![basis 0, basis 2] := by
      funext index
      fin_cases index <;> rfl
    have output : (application.basisEquiv
        ![basis 0, basis 1, Fin.add (n := 2) (basis 0) (basis 2)]).1 =
        ![basis 0, Fin.add (n := 2) (basis 0) (basis 2)] := by
      funext index
      fin_cases index <;> rfl
    exact ((congrArg AlgorithmGate.cnotPermutation selected).trans
      (AlgorithmGate.cnotPermutation_pair (basis 0) (basis 2))).trans output.symm
  · funext index
    have middle : index.val = (1 : Fin 3) := by
      fin_cases index
      rfl
    change basis index.val = ![basis 0, basis 1, Fin.add (n := 2) (basis 0) (basis 2)] index.val
    rw [middle]
    rfl

private theorem permutation_involutive : Function.Involutive permutation := by
  intro basis
  rw [permutation_coordinates, permutation_coordinates]
  funext index
  fin_cases index
  · rfl
  · rfl
  · change Fin.add (n := 2) (basis 0) (Fin.add (n := 2) (basis 0) (basis 2)) = basis 2
    generalize basis 0 = control
    generalize basis 2 = target
    fin_cases control <;> fin_cases target <;> rfl

private theorem outer_matrix (oracles : OracleModel) :
    (outerCnot oracles).matrix = UnitaryOperator.ofPerm permutation :=
  application.operator_ofPerm AlgorithmGate.cnotPermutation AlgorithmGate.cnot_operator_ofPerm

/-- Every basis entry has precisely the phase selected by the two unchanged original controls. -/
theorem fourRotation_matrix (oracles : OracleModel) (a00 a01 a10 a11 : ℝ) :
    ((circuit oracles a00 a01 a10 a11).matrix : HilbertOperator layout.register) =
      Matrix.diagonal (fun basis => weight
        (if basis 0 = 0 then (if basis 1 = 0 then a00 else a01)
          else (if basis 1 = 0 then a10 else a11)) (basis 2)) := by
  simp only [circuit, UnitaryCircuit.seq_matrix, Submonoid.coe_mul,
    outer_matrix, Multiplex.circuitAt_matrix]
  rw [← mul_assoc, ← mul_assoc,
    conjugate_diagonal layout.register permutation permutation_involutive,
    Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext basis
  have inner := congrFun (permutation_coordinates basis) (1 : Fin 3)
  have target := congrFun (permutation_coordinates basis) (2 : Fin 3)
  change permutation basis 1 = basis 1 at inner
  change permutation basis 2 = Fin.add (n := 2) (basis 0) (basis 2) at target
  rw [inner, target]
  by_cases selected : basis 1 = 0
  · simp only [selected, ite_true]
    exact weight_product a00 a10 (basis 0) (basis 2)
  · simp only [selected, ite_false]
    exact weight_product a01 a11 (basis 0) (basis 2)

end
end QuantumAlg.Gate.Rotation.Multiplex.Four
