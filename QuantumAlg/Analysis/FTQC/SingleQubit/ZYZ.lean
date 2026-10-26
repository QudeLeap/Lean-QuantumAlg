/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Util.Matrix.UnitaryAngles
public import QuantumAlg.Analysis.FTQC.CliffordT.Identities
import all QuantumAlg.Components.Kets
import all QuantumAlg.Components.Gates
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Gates.Rotation.Operator
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Analysis.FTQC.CliffordT.Word
import Mathlib.Tactic

/-!
# Phase-exact single-qubit Euler decomposition

The standard convention is RY(theta) = [[cos(theta/2), -sin(theta/2)],
[sin(theta/2), cos(theta/2)]]. The scalar phase is retained as in
Nielsen and Chuang, Theorem 4.1 (citation-only).
No determinant-one hypothesis is imposed on the input.
-/

@[expose] public section

namespace QuantumAlg.CliffordT

open Gate

open NormalizedVector

noncomputable section

/-- Every single-qubit unitary has a Z-Y-Z decomposition with its scalar phase. -/
public theorem zyz_decomposition (U : UnitaryOperator (Qubits 1)) :
    ∃ α β γ δ : ℝ,
      (U : HilbertOperator (Qubits 1)) = Complex.exp (α * Complex.I) •
        ((rotZStdOp β * rotYOp γ * rotZStdOp δ :
          UnitaryOperator (Qubits 1)) : HilbertOperator (Qubits 1)) := by
  obtain ⟨t, p, q, r, hu⟩ := MatrixAngles.unitary_two_angles U
  refine ⟨r / 2, q - p, 2 * t, r - p - q, ?_⟩
  rw [hu]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZStdOp, rotZOp, rotYOp, MatrixAngles.phase,
      mul_comm, mul_left_comm, mul_assoc] <;>
    ring_nf <;> simp only [← Complex.exp_add] <;> ring_nf <;> simp

/-- S H, expressed in first-letter-first execution order. -/
def yConjugator : List Letter := [.h, .s]

/-- The inverse Clifford word H S-dagger. -/
def yConjugatorInverse : List Letter := [.s, .s, .s, .h]

lemma yConjugatorInverse_evalOp :
    evalOp yConjugatorInverse = star (evalOp yConjugator) := by
  have hh : star HOp = HOp := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [HOp, Matrix.star_apply]
  simp [yConjugatorInverse, yConjugator, evalOp, Letter.op, star_mul,
    star_SOp, hh, pow_succ, mul_assoc]

/-- Clifford conjugation maps the standard Z rotation to the standard Y rotation. -/
lemma rotYOp_eq_clifford_conj (γ : ℝ) :
    rotYOp γ = evalOp yConjugator * rotZStdOp γ *
      star (evalOp yConjugator) := by
  apply Subtype.ext
  have hm : Complex.exp (((-(γ / 2) : ℝ) : ℂ) * Complex.I) =
      (Real.cos (γ / 2) : ℂ) - (Real.sin (γ / 2) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, neg_mul, sub_eq_add_neg]
  have hp : Complex.exp (-(((-(γ / 2) : ℝ) : ℂ) * Complex.I)) =
      (Real.cos (γ / 2) : ℂ) + (Real.sin (γ / 2) : ℂ) * Complex.I := by
    rw [show -(((-(γ / 2) : ℝ) : ℂ) * Complex.I) =
      ((γ / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hz : (rotZStdOp γ : HilbertOperator (Qubits 1)) =
      !![(Real.cos (γ / 2) : ℂ) - (Real.sin (γ / 2) : ℂ) * Complex.I, 0;
        0, (Real.cos (γ / 2) : ℂ) + (Real.sin (γ / 2) : ℂ) * Complex.I] := by
    change !![Complex.exp (((-(γ / 2) : ℝ) : ℂ) * Complex.I), 0;
      0, Complex.exp (-(((-(γ / 2) : ℝ) : ℂ) * Complex.I))] = _
    rw [hm, hp]
  have hstar : (starRingEnd ℂ) invSqrt2 = invSqrt2 := star_invSqrt2
  change (rotYOp γ : HilbertOperator (Qubits 1)) =
    (evalOp yConjugator : HilbertOperator (Qubits 1)) *
      (rotZStdOp γ : HilbertOperator (Qubits 1)) *
        star (evalOp yConjugator : HilbertOperator (Qubits 1))
  rw [hz]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [yConjugator, evalOp, Letter.op, rotYOp,
      HOp, SOp, Matrix.mul_apply, Matrix.star_apply, hstar] <;>
    ring_nf <;> norm_num [invSqrt2_sq, Complex.I_sq] <;> ring

/-- Three standard Z rotations and explicit Clifford words suffice, retaining phase. -/
lemma singleQubit_via_rotZ (U : UnitaryOperator (Qubits 1)) :
    ∃ (c₁ c₂ c₃ : List Letter) (β γ δ φ : ℝ),
      (U : HilbertOperator (Qubits 1)) = Complex.exp (φ * Complex.I) •
        ((evalOp c₁ * rotZStdOp β * evalOp c₂ * rotZStdOp γ *
          evalOp c₃ * rotZStdOp δ : UnitaryOperator (Qubits 1)) :
            HilbertOperator (Qubits 1)) := by
  obtain ⟨α, β, γ, δ, h⟩ := zyz_decomposition U
  refine ⟨[], yConjugator, yConjugatorInverse, β, γ, δ, α, ?_⟩
  simpa [rotYOp_eq_clifford_conj, yConjugatorInverse_evalOp, mul_assoc] using h

end

end QuantumAlg.CliffordT
