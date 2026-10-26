/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

/-!
# Angular coordinates for a two-dimensional unitary matrix

The first column and determinant determine the second column without division
by an entry. Consequently the coordinates also cover zero matrix entries.
-/

@[expose] public section

namespace QuantumAlg.MatrixAngles

noncomputable section

/-- Unit complex phase with a real angle. -/
def phase (t : ℝ) : ℂ := Complex.exp (t * Complex.I)

lemma phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  simp [phase, add_mul, Complex.exp_add]

lemma phase_neg (t : ℝ) : phase (-t) = star (phase t) := by
  simp [phase, ← Complex.exp_conj]

/-- First-column polar coordinates, with a determinant angle. -/
lemma unitary_two_angles (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ t p q r : ℝ,
      (U : Matrix (Fin 2) (Fin 2) ℂ) =
        !![(Real.cos t : ℂ) * phase p, -(Real.sin t : ℂ) * phase (r - q);
          (Real.sin t : ℂ) * phase q, (Real.cos t : ℂ) * phase (r - p)] := by
  let a := U 0 0
  let b := U 0 1
  let c := U 1 0
  let d := U 1 1
  let D := (U : Matrix (Fin 2) (Fin 2) ℂ).det
  have hcol := Matrix.mem_unitaryGroup_iff'.mp U.property
  have hnorm : star a * a + star c * c = 1 := by
    simpa [Matrix.mul_apply, Matrix.star_apply, a, c] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hcol
  have horth : star a * b + star c * d = 0 := by
    simpa [Matrix.mul_apply, Matrix.star_apply, a, b, c, d] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hcol
  have hdet : D = a * d - b * c := by simp [D, Matrix.det_fin_two, a, b, c, d]
  have hb : b = -D * star c := by
    rw [hdet]
    linear_combination a * horth - b * hnorm
  have hd : d = D * star a := by
    rw [hdet]
    linear_combination c * horth - d * hnorm
  have hnormReal : ‖a‖ ^ 2 + ‖c‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply, Complex.normSq_apply]
    have hr := congrArg Complex.re hnorm
    simpa [Complex.mul_re] using hr
  have ha : ‖a‖ ≤ 1 := by nlinarith [norm_nonneg a, sq_nonneg ‖c‖]
  let t := Real.arccos ‖a‖
  have hcos : Real.cos t = ‖a‖ :=
    Real.cos_arccos (x := ‖a‖) (by linarith [norm_nonneg a]) ha
  have hsin : Real.sin t = ‖c‖ := by
    rw [Real.sin_arccos, show 1 - ‖a‖ ^ 2 = ‖c‖ ^ 2 by linarith]
    exact Real.sqrt_sq (norm_nonneg c)
  have hDunit : D ∈ unitary ℂ := Matrix.det_of_mem_unitary U.property
  have hDnorm : ‖D‖ = 1 := by
    have hm := congrArg norm hDunit.1
    have hp := norm_nonneg D
    simp only [norm_mul, norm_star, norm_one] at hm
    nlinarith
  obtain ⟨r, hr⟩ := (Complex.norm_eq_one_iff D).mp hDnorm
  have hp : (Real.cos t : ℂ) * phase (Complex.arg a) = a := by
    rw [hcos]
    exact Complex.norm_mul_exp_arg_mul_I a
  have hq : (Real.sin t : ℂ) * phase (Complex.arg c) = c := by
    rw [hsin]
    exact Complex.norm_mul_exp_arg_mul_I c
  refine ⟨t, Complex.arg a, Complex.arg c, r, ?_⟩
  have hphase : phase r = D := hr
  ext i j
  fin_cases i <;> fin_cases j
  · exact hp.symm
  · change b = _
    calc
      b = -D * star c := hb
      _ = -D * star ((Real.sin t : ℂ) * phase (Complex.arg c)) :=
        congrArg (fun z => -D * star z) hq.symm
      _ = -(Real.sin t : ℂ) * phase (r - Complex.arg c) := by
        rw [sub_eq_add_neg, phase_add, phase_neg, hphase]
        simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
        ring
  · exact hq.symm
  · change d = _
    calc
      d = D * star a := hd
      _ = D * star ((Real.cos t : ℂ) * phase (Complex.arg a)) :=
        congrArg (fun z => D * star z) hp.symm
      _ = (Real.cos t : ℂ) * phase (r - Complex.arg a) := by
        rw [sub_eq_add_neg, phase_add, phase_neg, hphase]
        simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
        ring

end

end QuantumAlg.MatrixAngles
