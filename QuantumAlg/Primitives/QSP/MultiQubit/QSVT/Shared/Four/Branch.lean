/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Execution

/-!
# Constant and positive-degree branch boundaries

A supplied initial constant of one leaves the branch operator unchanged.
A zero-length source word with any bounded real initial constant realizes
that constant on the full signal space without a source query. Native
initialization events remain charged in both cases.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
noncomputable section

private lemma constant_one_operator (oracles : OracleModel) (width : Nat)
    (environment : oracles.Interpretation) :
    ((Shared.constantInitial oracles width 1).binaryMatrix environment) = 1 := by
  rw [Shared.constantInitial, Gate.singleQubitAt_first_binaryMatrix, Real.arccos_one]
  have zeroRotation : rotZOp 0 = 1 := by
    apply Subtype.ext
    ext row column
    fin_cases row <;> fin_cases column <;> simp [rotZOp]
  rw [zeroRotation]
  apply Subtype.ext
  exact HilbertOperator.one_tensor_one

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n))) (positive : 0 < n)

/-- Identity initialization preserves the full source word, including global phase. -/
lemma initializedBranch_one (phases : List ℝ) :
    initializedBranch U positive phases 1 =
      ((KnownZero.circuit (m := m) (n := n) positive true phases).binaryMatrix
        (UnitarySource.interpretation U true true false)) := by
  rw [initializedBranch, constant_one_operator, mul_one]

/-- The zero-length branch realizes its supplied constant on the original system block. -/
lemma initializedBranch_constant_block (constant : ℝ) (lower : -1 ≤ constant)
    (upper : constant ≤ 1) :
    projectedBlock m n (phasePlusBlock (initializedBranch U positive [] constant)) =
      (constant : ℂ) • (1 : HilbertOperator (Qubits n)) := by
  simp only [initializedBranch, KnownZero.circuit,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_identity, one_mul]
  rw [Shared.constantInitial_correct _ _ _ lower upper]
  ext row column
  simp [projectedBlock, Matrix.smul_apply, Matrix.one_apply]

end
end QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
