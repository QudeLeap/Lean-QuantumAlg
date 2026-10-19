/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Util.Complex

/-!
# Exact one-qubit phase operators

These two mathematical operators preserve the original phase on each basis
branch. They are independent of the execution model, native gate alphabet,
placement and circuit cost. Native realizations use these same operators.
-/

namespace QuantumAlg

noncomputable section

/-- Metadata-free phase operator `diag(1, e^{iθ})`. -/
public def phaseGateOp (θ : ℝ) : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (!![1, 0; 0, Complex.exp ((θ : ℝ) * Complex.I)] :
      HilbertOperator (Qubits 1)) (by
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.star_apply, conj_exp_I,
          exp_I_mul_exp_neg_I])

/-- Metadata-free zero-branch phase operator `diag(e^{iθ}, 1)`. -/
public def phaseGateOnZeroOp (θ : ℝ) : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (!![Complex.exp ((θ : ℝ) * Complex.I), 0; 0, 1] :
      HilbertOperator (Qubits 1)) (by
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.star_apply, conj_exp_I,
          exp_I_mul_exp_neg_I])

/-- The original one-branch phase operator is diagonal with its exact complex phase. -/
public lemma phaseGateOp_diagonal (angle : Real) :
    (phaseGateOp angle : HilbertOperator (Qubits 1)) =
      Matrix.diagonal (fun bit => if bit = 0 then 1 else
        Complex.exp ((angle : Complex) * Complex.I)) := by
  ext row column
  fin_cases row <;> fin_cases column <;> rfl

/-- The original zero-branch phase operator carries its exact phase on the zero branch. -/
public lemma phaseGateOnZeroOp_diagonal (angle : Real) :
    (phaseGateOnZeroOp angle : HilbertOperator (Qubits 1)) =
      Matrix.diagonal (fun bit => if bit = 0 then
        Complex.exp ((angle : Complex) * Complex.I) else 1) := by
  ext row column
  fin_cases row <;> fin_cases column <;> rfl

end

end QuantumAlg
