/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Target
public import QuantumAlg.Util.CliffordT.Matrix

/-!
# Exact small-index rotation targets

The standard rotations at indices zero, one, and two have entries in the
Clifford+T coefficient ring. Exact comparison avoids interval rounding at zero
tolerance. Higher indices use the rational interval checker.
-/

@[expose] public section

namespace QuantumAlg.CliffordT.Checker

/-- Ring-valued diagonal target, used only when the index is at most two. -/
def exactTarget (j : ℕ) : Mat2 :=
  let c : DOmega := if j = 0 then -1 else if j = 1 then 0 else DOmega.invSqrtTwo
  let s : DOmega := if j = 0 then 0 else if j = 1 then 1 else DOmega.invSqrtTwo
  fun i k => if i = k then c + DOmega.imaginary * (if i = 0 then -s else s) else 0

lemma exactTarget_sound (j : ℕ) (hj : j ≤ 2) :
    toComplexMat (exactTarget j) = targetMatrix j := by
  have h1 : halfAngle 1 = Real.pi / 2 := by norm_num [halfAngle]; ring
  have h2 : halfAngle 2 = Real.pi / 4 := by norm_num [halfAngle]; ring
  ext i k
  change DOmega.toComplex (exactTarget j i k) = targetMatrix j i k
  interval_cases j
  · fin_cases i <;> fin_cases k <;> simp [exactTarget, targetMatrix, halfAngle]
  · fin_cases i <;> fin_cases k <;> simp [exactTarget, targetMatrix, h1,
      DOmega.toComplex_imaginary, -Complex.ofReal_cos, -Complex.ofReal_sin]
  · fin_cases i <;> fin_cases k <;> simp [exactTarget, targetMatrix, h2,
      DOmega.toComplex_imaginary, DOmega.toComplex_invSqrtTwo,
      -Complex.ofReal_cos, -Complex.ofReal_sin, Real.cos_pi_div_four,
      Real.sin_pi_div_four, Real.sqrt_div_self, Complex.ofReal_inv]

end QuantumAlg.CliffordT.Checker
