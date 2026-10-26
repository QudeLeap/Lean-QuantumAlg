/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.FTQC.Parity
import all QuantumAlg.Primitives.FTQC.CliffordLayers

/-! # Exact parity phase of the original seven-T circuit without dense products -/

namespace QuantumAlg.FTQC

open CliffordT Gate UnitaryCircuit

noncomputable section

/-- All six original CNOTs cancel while the seven original phases give the all-one sign. -/
lemma parity7T_diagonal (oracles : OracleModel) (environment : oracles.Interpretation) :
    ((parity7T oracles).binaryMatrix environment : HilbertOperator (Qubits 3)) =
      Parity.cczMatrix := by
  simp only [parity7T, blocks_matrix, List.foldl_cons, List.foldl_nil,
    layer3_matrix, cx_matrix]
  simp only [tDaggerWord, evalOp, Letter.op, one_mul,
    Matrix.UnitaryGroup.mul_apply, Matrix.UnitaryGroup.one_apply,
    UnitaryOperator.coe_tensor, Toffoli7TProof.sOp_diagonal,
    Toffoli7TProof.tOp_diagonal, ← Matrix.diagonal_one,
    Matrix.diagonal_mul_diagonal]
  repeat rw [tensor_diagonal]
  simp only [Parity.diagonal_weighted, Parity.cnot_weighted]
  repeat rw [WeightedPermutation.mul]
  refine (WeightedPermutation.eq_diagonal_of_fixed _ _ ?_).trans ?_
  · intro label
    fin_cases label <;> decide +kernel
  · apply congrArg Matrix.diagonal
    funext label
    fin_cases label <;>
      (norm_num [Equiv.trans_apply, Parity.cnot01_apply, Parity.cnot02_apply,
        Parity.cnot10_apply, Parity.cnot20_apply, Parity.cnot12_apply,
        prodEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat, Parity.cczMatrix,
        Toffoli7TProof.sqrtTwo_sq, Complex.I_sq, Fin.ext_iff];
        simp <;> try ring_nf)
    all_goals
      norm_num [Toffoli7TProof.sqrtTwo_sq, Toffoli7TProof.sqrtTwo_four,
        Complex.I_pow_eq_pow_mod, Complex.I_sq, Complex.I_pow_three, Fin.ext_iff]
    all_goals norm_num [Complex.I_sq, Complex.I_pow_three]
    all_goals try ring

/-- The unchanged native word has the original full Toffoli matrix with exact phase. -/
lemma toffoli7T_matrix_sparse (oracles : OracleModel) (environment : oracles.Interpretation) :
    (toffoli7TCircuit oracles).binaryMatrix environment = toffoliOp := by
  simp only [toffoli7TCircuit, blocks_matrix, List.foldl_cons, List.foldl_nil, layer3_matrix]
  apply Subtype.ext
  simp only [Matrix.UnitaryGroup.mul_val, Matrix.UnitaryGroup.one_val, UnitaryOperator.coe_tensor,
    evalOp, Letter.op, one_mul, Matrix.mul_one, HilbertOperator.one_tensor_one,
    parity7T_diagonal]
  exact Parity.hadamard_conjugate_ccz oracles environment

end

end QuantumAlg.FTQC
