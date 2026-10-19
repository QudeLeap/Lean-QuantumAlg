/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Hadamard.Layer.Matrix
public import QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Components.Gates.Hadamard.Layer.Matrix
import all QuantumAlg.Components.Gates.Hadamard.Layer.Layout
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Kets
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Primitives.WalshHadamard.Mathematics
import all QuantumAlg.Util.FinPow.BinaryBasis
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity

/-!
# Native Walsh-Hadamard implementation

The full matrix of the actual parallel Hadamard word agrees with the original
Walsh character formula [dW19, qcnotes.tex:1005-1006]. Reindexing here only
expresses that computed matrix in binary labels; it introduces no instruction.
-/

namespace QuantumAlg.WalshHadamard.Native

noncomputable section

open scoped BigOperators
open NormalizedVector

/-- The operator computed by the actual native layer, expressed in binary labels. -/
public def binaryOperator (oracles : OracleModel) (width : Nat)
    (environment : oracles.Interpretation) :
    UnitaryOperator (Qubits width) :=
  UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv width)
    ((Gate.HadamardLayer.circuit oracles width).matrix environment)

private lemma hadamard_entry (row column : Fin 2) :
    Gate.HOp row column = invSqrt2 *
      (if finTwoEquiv row && finTwoEquiv column then (-1 : ℂ) else 1) := by
  fin_cases row <;> fin_cases column <;> simp [Gate.HOp, finTwoEquiv]

private lemma normalization_product (width : Nat) :
    (∏ _ : Fin width, invSqrt2) = invSqrtCard width := by
  induction width with
  | zero => simp [invSqrtCard]
  | succ width ih => rw [Fin.prod_univ_castSucc, ih, invSqrtCard_succ]

private lemma sign_product (width : Nat) (row column : Fin (2 ^ width)) :
    (∏ index : Fin width, if bit row index && bit column index then (-1 : ℂ) else 1) =
      walshSign row column := by
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const]
  unfold walshSign dotParity
  split
  · rename_i odd
    exact (of_decide_eq_true odd).neg_one_pow
  · rename_i notOdd
    have parity : ¬ Odd (Finset.univ.filter (fun index : Fin width =>
        (bit row index && bit column index) = true)).card := by simpa using notOdd
    exact (Nat.not_odd_iff_even.mp parity).neg_one_pow

/-- The actual native word realizes the original Walsh character matrix exactly. -/
lemma native_binary_matrix (oracles : OracleModel) (width : Nat)
    (environment : oracles.Interpretation) :
    binaryOperator oracles width environment = hadamardLayerOperator width := by
  ext row column
  change ((Gate.HadamardLayer.circuit oracles width).matrix environment)
      ((QuantumSignature.qubitsIndexEquiv width).symm row)
      ((QuantumSignature.qubitsIndexEquiv width).symm column) = _
  rw [Gate.HadamardLayer.hadamardLayer_circuit_matrix_entry]
  change (∏ index : Fin width, Gate.HOp
    (finTwoEquiv.symm (row.val.testBit index.rev.val))
    (finTwoEquiv.symm (column.val.testBit index.rev.val))) = _
  simp only [hadamard_entry, Equiv.apply_symm_apply]
  rw [Finset.prod_mul_distrib, normalization_product, hadamardLayerOperator_apply]
  congr 1
  calc
    (∏ index : Fin width, if row.val.testBit index.rev.val &&
        column.val.testBit index.rev.val then (-1 : ℂ) else 1) =
      ∏ index : Fin width, if bit row index && bit column index then (-1 : ℂ) else 1 :=
        Equiv.prod_comp (Fin.revPerm (n := width))
          (fun index : Fin width =>
            if bit row index && bit column index then (-1 : ℂ) else 1)
    _ = walshSign row column := sign_product width row column

end

end QuantumAlg.WalshHadamard.Native
