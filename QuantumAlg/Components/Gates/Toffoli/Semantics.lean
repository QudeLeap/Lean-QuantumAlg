/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Gates.Toffoli.Binary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Base.UnitaryCircuit.Realization

/-!
# Exact Toffoli from the executed fifteen-gate word

The two boundary Hadamards convert the all-one phase into the original target
flip. Equality includes global phase and every input, with no ancillary wire.
-/

namespace QuantumAlg.Gate.Toffoli
noncomputable section

private def bothControls : HilbertOperator (Qubits 2) :=
  Matrix.diagonal (fun label => if label = (3 : Fin 4) then 1 else 0)

private lemma phase_tensor :
    (Matrix.diagonal (fun label => if label = (7 : (Qubits 3).Index) then (-1 : ℂ) else 1) :
      HilbertOperator (Qubits 3)) =
      HilbertOperator.tensor bothControls (Gate.ZOp : HilbertOperator (Qubits 1)) +
      HilbertOperator.tensor (1 - bothControls) (1 : HilbertOperator (Qubits 1)) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp +decide [Qubits, HilbertOperator.tensor, bothControls, Gate.ZOp,
      prodEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]

private lemma flip_tensor :
    ((UnitaryOperator.ofPerm (R := Qubits 3) (Equiv.swap (6 : (Qubits 3).Index) 7)) :
      HilbertOperator (Qubits 3)) =
      HilbertOperator.tensor bothControls (Gate.XOp : HilbertOperator (Qubits 1)) +
      HilbertOperator.tensor (1 - bothControls) (1 : HilbertOperator (Qubits 1)) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp +decide [Qubits, HilbertOperator.tensor, bothControls, Gate.XOp,
      UnitaryOperator.ofPerm_entry,
      prodEquiv, finProdFinEquiv, Fin.divNat,
      Fin.modNat, Fin.ext_iff]

private lemma hadamard_square :
    (Gate.HOp : HilbertOperator (Qubits 1)) * (Gate.HOp : HilbertOperator (Qubits 1)) = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [Gate.HOp, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
      NormalizedVector.invSqrt2_mul_self]

private lemma hadamard_z_hadamard :
    (Gate.HOp : HilbertOperator (Qubits 1)) * (Gate.ZOp : HilbertOperator (Qubits 1)) *
      (Gate.HOp : HilbertOperator (Qubits 1)) = (Gate.XOp : HilbertOperator (Qubits 1)) := by
  have commute : (Gate.HOp : HilbertOperator (Qubits 1)) *
      (Gate.ZOp : HilbertOperator (Qubits 1)) =
      (Gate.XOp : HilbertOperator (Qubits 1)) * (Gate.HOp : HilbertOperator (Qubits 1)) := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Gate.HOp, Gate.ZOp, Gate.XOp, Matrix.mul_apply,
        smul_eq_mul, UnitaryOperator.ofPerm_entry]
  rw [commute, Matrix.mul_assoc, hadamard_square, Matrix.mul_one]

/-- The complete binary operator is the original Toffoli transposition, with exact phase. -/
lemma toffoliExpansion_binaryMatrix (oracles : OracleModel)
    (environment : oracles.Interpretation) :
    ((circuit oracles).binaryMatrix environment) =
      UnitaryOperator.ofPerm (R := Qubits 3) (Equiv.swap (6 : (Qubits 3).Index) 7) := by
  rw [circuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, toffoliExpansion_hadamard_binary]
  apply Subtype.ext
  change HilbertOperator.tensor 1 (Gate.HOp : HilbertOperator (Qubits 1)) *
    ((((phaseWord oracles (Real.pi / 4)).binaryMatrix environment) : HilbertOperator (Qubits 3)) *
      HilbertOperator.tensor 1 (Gate.HOp : HilbertOperator (Qubits 1))) = _
  rw [toffoliExpansion_phaseWord_binary, ← Matrix.mul_assoc, phase_tensor,
    Matrix.mul_add, Matrix.add_mul]
  repeat rw [HilbertOperator.tensor_mul_tensor]
  simp only [Matrix.one_mul, Matrix.mul_one]
  rw [hadamard_z_hadamard, hadamard_square]
  exact flip_tensor.symm

/-- The executed native expansion realizes the model-owned Toffoli token itself. -/
lemma toffoliExpansion_matrix (oracles : OracleModel) (environment : oracles.Interpretation) :
    ((circuit oracles).matrix environment) = AlgorithmGate.model.operator .toffoli := by
  calc
    ((circuit oracles).matrix environment) = UnitaryOperator.reindex
        (QuantumSignature.qubitsIndexEquiv 3).symm ((circuit oracles).binaryMatrix environment) :=
      (UnitaryOperator.unitaryOperator_reindex_cancel
        (QuantumSignature.qubitsIndexEquiv 3) ((circuit oracles).matrix environment)).symm
    _ = UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 3).symm
        (UnitaryOperator.ofPerm (R := Qubits 3)
          (Equiv.swap (6 : (Qubits 3).Index) 7)) := by
      rw [toffoliExpansion_binaryMatrix]
    _ = AlgorithmGate.model.operator .toffoli := by
      rw [UnitaryOperator.reindex_ofPerm, AlgorithmGate.toffoli_operator_ofPerm]
      rfl

/-- Exact realization on the original three physical systems, with the complete native word. -/
def realization (oracles : OracleModel) :
    UnitaryCircuit.ExactRealization AlgorithmGate.model oracles layout
      (fun _ => AlgorithmGate.model.operator .toffoli) where
  circuit := circuit oracles
  matrix_eq := toffoliExpansion_matrix oracles

end
end QuantumAlg.Gate.Toffoli
