/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.FTQC.Parity
import all QuantumAlg.Primitives.FTQC.ToffoliTDepth3.Base
import all QuantumAlg.Primitives.FTQC.CliffordLayers

/-! # Exact phase of the original three-stage seven-T parity network -/

namespace QuantumAlg.FTQC

open CliffordT Gate UnitaryCircuit

noncomputable section

/-- Actual parity computation and its inverse restore the original three binary coordinates. -/
lemma parityTDepth3_diagonal (oracles : OracleModel) (environment : oracles.Interpretation) :
    ((parityTDepth3 oracles).binaryMatrix environment : HilbertOperator (Qubits 3)) =
      Parity.cczMatrix := by
  simp only [parityTDepth3, parityBasis, List.reverse_cons, List.reverse_nil,
    List.cons_append, List.nil_append,
    blocks_matrix, List.foldl_cons, List.foldl_nil, layer3_matrix, cx_matrix]
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

/-- Exact common Hadamard conjugation retains the full original Toffoli matrix and phase. -/
lemma toffoliTDepth3Core_matrix_sparse (oracles : OracleModel)
    (environment : oracles.Interpretation) :
    (toffoliTDepth3Core oracles).binaryMatrix environment = toffoliOp := by
  simp only [toffoliTDepth3Core, blocks_matrix, List.foldl_cons, List.foldl_nil, layer3_matrix]
  apply Subtype.ext
  simp only [Matrix.UnitaryGroup.mul_val, Matrix.UnitaryGroup.one_val, UnitaryOperator.coe_tensor,
    evalOp, Letter.op, one_mul, Matrix.mul_one, HilbertOperator.one_tensor_one,
    parityTDepth3_diagonal]
  exact Parity.hadamard_conjugate_ccz oracles environment

end

end QuantumAlg.FTQC
