/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Bounds
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Exact
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Evaluation

/-!
# Kernel-computable rotation certificate checking

The checker compares exact word matrices against the standard Z rotation,
including its global phase. All executable operations use exact rational or
ring arithmetic. The square-root and operator-norm reasoning occurs only in
the soundness proof. The target and synthesis output form are those of
[RS16, gridsynth.tex:146-162]; this module derives a sufficient, computable
acceptance test rather than a completeness result for synthesis.
-/

@[expose] public section

namespace QuantumAlg.CliffordT

open Gate
open scoped Matrix.Norms.L2Operator

namespace Checker

/-- Squared Frobenius bound, sharpened to zero for an exact small-index match. -/
def errorSq (A : Mat2) (j : ℕ) : ℚ :=
  if j ≤ 2 ∧ A = exactTarget j then 0 else matrixErrorSq A j

lemma errorSq_sound (A : Mat2) (j : ℕ) :
    ‖toComplexMat A - targetMatrix j‖ ≤ Real.sqrt (errorSq A j) := by
  unfold errorSq
  split_ifs with h
  · rw [h.2, exactTarget_sound j h.1, sub_self, norm_zero]
    simp
  · exact matrixErrorSq_sound A j

end Checker

/-- Accept precisely nonnegative tolerances whose square dominates the rational
error bound. An exact match at indices at most two has bound zero. -/
def check (w : List Letter) (j : ℕ) (eps : ℚ) : Bool :=
  decide (0 ≤ eps ∧ Checker.errorSq (evalRingPacked w) j ≤ eps ^ 2)

/-- Acceptance implies operator-norm closeness to the standard rotation,
with no freedom to discard a scalar phase. -/
public theorem check_sound (w : List Letter) (j : ℕ) (eps : ℚ) (h : check w j eps = true) :
    HilbertOperator.opNorm ((evalOp w : HilbertOperator (Qubits 1)) -
      (rotZStdOp (2 * Real.pi / 2 ^ j) : HilbertOperator (Qubits 1))) ≤ (eps : ℝ) := by
  have hc : 0 ≤ eps ∧ Checker.errorSq (evalRingPacked w) j ≤ eps ^ 2 := of_decide_eq_true h
  rw [evalRingPacked_eq_evalRing] at hc
  have he : (0 : ℝ) ≤ (eps : ℝ) := by exact_mod_cast hc.1
  have hs : (Checker.errorSq (evalRing w) j : ℝ) ≤ (eps : ℝ) ^ 2 := by
    exact_mod_cast hc.2
  rw [evalOp_eq_toComplexMat, ← Checker.targetMatrix_eq_rotZStdOp]
  exact (Checker.errorSq_sound (evalRing w) j).trans (Real.sqrt_le_iff.mpr ⟨he, hs⟩)

namespace RotationCertificate

/-- Turn a kernel-checked Boolean result into the existing semantic certificate. -/
def ofCheck {w : List Letter} {j : ℕ} {eps : ℚ} (h : check w j eps = true) :
    RotationCertificate (2 * Real.pi / 2 ^ j) (eps : ℝ) :=
  ⟨w, check_sound w j eps h⟩

@[simp]
lemma ofCheck_word {w : List Letter} {j : ℕ} {eps : ℚ} (h : check w j eps = true) :
    (ofCheck h).word = w := rfl

end RotationCertificate

end QuantumAlg.CliffordT
