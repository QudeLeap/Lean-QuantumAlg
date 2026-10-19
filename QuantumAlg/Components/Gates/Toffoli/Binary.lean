/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Gates.Toffoli.PhaseWord
import all QuantumAlg.Components.Gates.SingleQubit.Last.Binary

/-!
# Binary coordinates of the exact Toffoli phase expansion

The three original bits retain their big-endian labels. At a quarter turn,
only label seven acquires a negative phase; all other labels are unchanged.
-/

namespace QuantumAlg.Gate.Toffoli
noncomputable section

/-- The native middle word is exactly controlled-controlled Z in the original binary order. -/
lemma toffoliExpansion_phaseWord_binary (oracles : OracleModel)
    (environment : oracles.Interpretation) :
    (((phaseWord oracles (Real.pi / 4)).binaryMatrix environment) : HilbertOperator (Qubits 3)) =
      Matrix.diagonal (fun label => if label = (7 : (Qubits 3).Index) then (-1 : ℂ) else 1) := by
  rw [UnitaryCircuit.binaryMatrix, UnitaryOperator.coe_reindex,
    toffoliExpansion_phaseWord_matrix]
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_diagonal _ _ (QuantumSignature.qubitsIndexEquiv 3).symm.injective]
  apply congrArg Matrix.diagonal
  funext label
  simp only [Function.comp_apply,
    show 4 * (Real.pi / 4) = Real.pi by ring, Complex.exp_pi_mul_I]
  fin_cases label <;> rfl

/-- Both boundary Hadamards act on the original target, with its two controls untouched. -/
lemma toffoliExpansion_hadamard_binary (oracles : OracleModel)
    (environment : oracles.Interpretation) :
    ((Gate.singleQubitAt layout oracles Gate.HOp (2 : Fin 3) rfl).binaryMatrix environment) =
      (1 : UnitaryOperator (Qubits 2)).tensor Gate.HOp :=
  Gate.singleQubitAt_last_binaryMatrix oracles 2 Gate.HOp environment

end
end QuantumAlg.Gate.Toffoli
