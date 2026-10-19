/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Unitary
public import QuantumAlg.Components.Kets
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Components.Kets
import all QuantumAlg.Util.Complex

/-!
# Exact rotation operators

These mathematical operators grant no native instruction or oracle access.
-/

namespace QuantumAlg

noncomputable section

/-- Metadata-free processing rotation `e^{i phi Z}`. -/
public def rotZOp (φ : ℝ) : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (!![Complex.exp (φ * Complex.I), 0; 0,
      Complex.exp (-(φ * Complex.I))] : HilbertOperator (Qubits 1)) (by
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.star_apply, conj_exp_I,
          conj_exp_neg_I, exp_I_mul_exp_neg_I, exp_neg_I_mul_exp_I])

/-- Metadata-free standard `R_Y(theta)`. -/
@[expose] public def rotYOp (θ : ℝ) : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (!![(Real.cos (θ / 2) : ℂ), -(Real.sin (θ / 2) : ℂ);
      (Real.sin (θ / 2) : ℂ),
      (Real.cos (θ / 2) : ℂ)] : HilbertOperator (Qubits 1)) (by
      have hcs' : (Real.sin (θ / 2) : ℂ) ^ 2
          + (Real.cos (θ / 2) : ℂ) ^ 2 = 1 := by
        have h := Real.sin_sq_add_cos_sq (θ / 2)
        exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) h
      rw [Matrix.mem_unitaryGroup_iff]
      generalize Real.cos (θ / 2) = c at hcs' ⊢
      generalize Real.sin (θ / 2) = s at hcs' ⊢
      ext i j
      fin_cases i <;> fin_cases j <;>
        · simp [Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
          try ring_nf
          try linear_combination hcs')

/-- A Y rotation sends the zero basis vector to its two real-amplitude
branches. -/
public lemma rotYOp_applyVec_ket0 (θ : ℝ) :
    (rotYOp θ).applyVec
        (NormalizedVector.ket0 : HilbertVector (Qubits 1)) =
      (Real.cos (θ / 2) : ℂ) •
          (NormalizedVector.ket0 : HilbertVector (Qubits 1)) +
        (Real.sin (θ / 2) : ℂ) •
          (NormalizedVector.ket1 : HilbertVector (Qubits 1)) := by
  apply WithLp.ofLp_injective
  funext index
  fin_cases index <;>
    simp [UnitaryOperator.applyVec, rotYOp, NormalizedVector.ket0,
      NormalizedVector.ket1, NormalizedVector.ket_apply,
      PiLp.smul_apply, PiLp.add_apply]

/-- A Y rotation sends the one basis vector to the signed branch
decomposition used by finite-range preparation. -/
public lemma rotYOp_applyVec_ket1 (θ : ℝ) :
    (rotYOp θ).applyVec
        (NormalizedVector.ket1 : HilbertVector (Qubits 1)) =
      (-(Real.sin (θ / 2)) : ℂ) •
          (NormalizedVector.ket0 : HilbertVector (Qubits 1)) +
        (Real.cos (θ / 2) : ℂ) •
          (NormalizedVector.ket1 : HilbertVector (Qubits 1)) := by
  apply WithLp.ofLp_injective
  funext index
  fin_cases index <;>
    simp [UnitaryOperator.applyVec, rotYOp, NormalizedVector.ket0,
      NormalizedVector.ket1, NormalizedVector.ket_apply,
      PiLp.smul_apply, PiLp.add_apply]

/-- Metadata-free standard `R_Z(phi) = e^{-i phi Z/2}`. -/
public def rotZStdOp (φ : ℝ) : UnitaryOperator (Qubits 1) := rotZOp (-(φ / 2))

@[simp]
lemma rotZStdOp_zero : rotZStdOp 0 = 1 := by
  apply Subtype.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [rotZStdOp, rotZOp]


end

end QuantumAlg
