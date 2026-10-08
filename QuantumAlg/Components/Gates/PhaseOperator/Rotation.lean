/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.PhaseOperator
public import QuantumAlg.Components.Gates.Rotation.Operator
import all QuantumAlg.Components.Gates.PhaseOperator
import all QuantumAlg.Components.Gates.Rotation.Operator
import all QuantumAlg.Core.Base.Gate.Unitary

/-!
# Exact phase factors relating one-branch phases and standard rotations

The scalar factors are retained explicitly; these identities cannot justify
silently dropping a phase before coherent control or certificate composition.
-/

namespace QuantumAlg

noncomputable section

/-- `diag(1,e^{iθ}) = e^{iθ/2} · R_Z(θ)`. -/
public theorem phaseGateOp_signal (θ : ℝ) :
    (phaseGateOp θ : HilbertOperator (Qubits 1)) =
      Complex.exp ((θ / 2 : ℝ) * Complex.I) •
        (rotZStdOp θ : HilbertOperator (Qubits 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [phaseGateOp, rotZStdOp, rotZOp, UnitaryOperator.coe_ofMatrix,
      Nat.reducePow, Fin.zero_eta, Fin.mk_one, Fin.isValue, Complex.ofReal_div,
      Complex.ofReal_ofNat, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.smul_apply, smul_eq_mul, mul_zero]
  · rw [show (1 : ℂ) = Complex.exp 0 from (Complex.exp_zero).symm, ← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring_nf
  · rw [← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring_nf

/-- `diag(e^{-iθ},1) = e^{-iθ/2} · R_Z(θ)`. -/
public theorem phaseGateOnZeroOp_signal (θ : ℝ) :
    (phaseGateOnZeroOp (-θ) : HilbertOperator (Qubits 1)) =
      Complex.exp (-(θ / 2 : ℝ) * Complex.I) •
        (rotZStdOp θ : HilbertOperator (Qubits 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [phaseGateOnZeroOp, rotZStdOp, rotZOp,
      UnitaryOperator.coe_ofMatrix, Nat.reducePow,
      Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Complex.ofReal_div, Complex.ofReal_ofNat, neg_mul, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.smul_apply, smul_eq_mul,
      mul_zero]
  · rw [← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring_nf
  · rw [show (1 : ℂ) = Complex.exp 0 from (Complex.exp_zero).symm, ← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring_nf

end

end QuantumAlg
