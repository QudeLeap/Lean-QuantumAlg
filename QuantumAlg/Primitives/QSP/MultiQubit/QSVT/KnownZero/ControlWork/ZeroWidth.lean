/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.ControlWork.Coordinates

/-!
# Original projector phase at zero signal width

The last original control supplies restored work. The complete binary matrix
retains the original k+1 controls and the single phase ancilla.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.ControlWork
noncomputable section

private theorem emptySuffix (width : Nat) (label : Fin (2 ^ width)) :
    prodEquiv (m := width) (n := 0) (label, 0) = label := by
  apply Fin.ext
  simp [prodEquiv, finProdFinEquiv]

private theorem zeroAncilla_empty (width : Nat) :
    (OrthogonalProjector.zeroAncilla width 0).op = (OrthogonalProjector.zero width).op := by
  ext row column
  change HilbertOperator.tensor (OrthogonalProjector.zero width).op
    (1 : HilbertOperator (Qubits 0)) row column = _
  conv_lhs => rw [← emptySuffix width row, ← emptySuffix width column,
    HilbertOperator.tensor_apply]
  have oneEntry (a b : Fin 1) : (1 : HilbertOperator (Qubits 0)) a b = 1 := by
    fin_cases a; fin_cases b; rfl
  rw [oneEntry, mul_one]
  simp only [Equiv.symm_apply_apply]

/-- At zero signal width the full native matrix is precisely the original projector phase. -/
theorem controlWork_zeroWidth_phase_matrix (k : Nat) (oracles : OracleModel) (angle : ℝ) :
    ((phase k 0 oracles angle).binaryMatrix : HilbertOperator (Qubits (1 + ((k + 1) + 0)))) =
      HilbertOperator.tensor (rotZStdOp (-2 * angle) : HilbertOperator (Qubits 1))
        (OrthogonalProjector.zeroAncilla (k + 1) 0).op +
      HilbertOperator.tensor (rotZStdOp (2 * angle) : HilbertOperator (Qubits 1))
        (OrthogonalProjector.complement (OrthogonalProjector.zeroAncilla (k + 1) 0)) := by
  have diagonal : ((phase k 0 oracles angle).binaryMatrix :
      HilbertOperator (Qubits (1 + (k + 1)))) =
      Matrix.diagonal (fun label => phaseWeight k 0 angle
        ((QuantumSignature.qubitsIndexEquiv (1 + (k + 1))).symm label)) := by
    rw [UnitaryCircuit.binaryMatrix, UnitaryOperator.coe_reindex, controlWork_phase_matrix]
    exact Matrix.submatrix_diagonal
      (fun basis : (layout k 0).Basis => phaseWeight k 0 angle basis)
      (QuantumSignature.qubitsIndexEquiv (1 + (k + 1))).symm
      (QuantumSignature.qubitsIndexEquiv (1 + (k + 1))).symm.injective
  rw [diagonal]
  ext row column
  obtain ⟨⟨rowPhase, rowWord⟩, rfl⟩ := (prodEquiv (m := 1) (n := k + 1)).surjective row
  obtain ⟨⟨rowControls, rowLast⟩, rfl⟩ := (prodEquiv (m := k) (n := 1)).surjective rowWord
  obtain ⟨⟨phaseBit, word⟩, rfl⟩ := (prodEquiv (m := 1) (n := k + 1)).surjective column
  obtain ⟨⟨controls, last⟩, rfl⟩ := (prodEquiv (m := k) (n := 1)).surjective word
  have weight := controlWork_phaseWeight_decoded k 0 angle rowPhase rowControls rowLast 0
  rw [emptySuffix] at weight
  rw [Matrix.diagonal_apply, weight]
  simp only [OrthogonalProjector.complement, zeroAncilla_empty]
  simp only [Matrix.add_apply, HilbertOperator.tensor_apply (m := 1) (n := k + 1),
    Equiv.symm_apply_apply, Matrix.sub_apply, Matrix.one_apply,
    OrthogonalProjector.zero, OrthogonalProjector.basis, OrthogonalProjector.basisOp,
    Matrix.of_apply, Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  simp only [controlWork_zero_control_label]
  by_cases first : rowControls = 0 <;>
    by_cases same : rowControls = controls <;>
    fin_cases rowPhase <;> fin_cases phaseBit <;> fin_cases rowLast <;> fin_cases last <;>
    simp [rotZStdOp, rotZOp, Gate.Rotation.Multiplex.weight, first, same]
  all_goals simp_all [eq_comm]

end
end QuantumAlg.QSP.MultiQubit.QSVT.ControlWork
