/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.Matrix.Weyl

/-!
# Finite-dimensional Fourier transform

The normalized discrete Fourier matrix and its unitarity, used in the
encoder formula [CML+24, main.tex:738].
-/

@[expose] public section

namespace QuantumAlg.MatrixWeyl

noncomputable section


variable {d : ℕ}

/-- The `d`-dimensional quantum Fourier transform: `(j, k) ↦ ω^{jk}/√d`. -/
private def fourierFormula (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun j k => invSqrtD d * clockRoot d ^ (j.val * k.val)

@[simp]
private lemma fourierFormula_entry (d : ℕ) (j k : Fin d) :
    fourierFormula d j k = invSqrtD d * clockRoot d ^ (j.val * k.val) := by
  simp [fourierFormula]

/-- The `d`-dimensional quantum Fourier transform is unitary. -/
private lemma fourierFormula_mem_unitaryGroup (hd : d ≠ 0) :
    fourierFormula d ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  have hterm : ∀ l : Fin d,
      star (fourierFormula d) j l * fourierFormula d l k =
        (↑(d : ℝ))⁻¹ * clockRoot d ^ ((l.val : ℤ) * ((k.val : ℤ) - (j.val : ℤ))) := by
    intro l
    simp only [Matrix.star_apply, fourierFormula_entry, star_mul', star_pow, star_clockRoot hd,
      star_invSqrtD]
    rw [mul_mul_mul_comm, invSqrtD_mul_self]
    congr 1
    rw [inv_pow, ← zpow_natCast (clockRoot d) (l.val * j.val),
      ← zpow_natCast (clockRoot d) (l.val * k.val), ← zpow_neg,
      ← zpow_add₀ (clockRoot_ne_zero d)]
    congr 1
    push_cast
    ring
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [hterm]
  rw [← Finset.mul_sum]
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos rfl]
    have h0 : ∀ l : Fin d,
        clockRoot d ^ ((l.val : ℤ) * ((j.val : ℤ) - (j.val : ℤ))) = (1 : ℂ) :=
      fun l => by rw [sub_self, mul_zero, zpow_zero]
    simp only [h0, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    push_cast
    exact inv_mul_cancel₀ (by exact_mod_cast hd)
  · rw [if_neg hjk]
    have hdvd : ¬ ((d : ℕ) : ℤ) ∣ ((k.val : ℤ) - (j.val : ℤ)) := by
      intro hdvd
      have h0 : (k.val : ℤ) - (j.val : ℤ) = 0 :=
        Int.eq_zero_of_abs_lt_dvd hdvd (Int.abs_sub_lt_of_lt_lt j.isLt k.isLt)
      exact hjk (Fin.val_injective
        (by exact_mod_cast sub_eq_zero.mp h0 : k.val = j.val)).symm
    rw [sum_clockRoot_zpow_eq_zero hd hdvd, mul_zero]

/-- The normalized finite Fourier transform, carrying its unitary invariant. -/
def quditFT (d : ℕ) : Matrix.unitaryGroup (Fin d) ℂ :=
  ⟨Matrix.of (fun j k => invSqrtD d * clockRoot d ^ (j.val * k.val)), by
    by_cases hd : d = 0
    · subst d
      rw [Matrix.mem_unitaryGroup_iff]
      ext i
      exact Fin.elim0 i
    · exact fourierFormula_mem_unitaryGroup hd⟩

/-- Entry formula for the certified finite Fourier transform. -/
@[simp] lemma quditFT_entry (d : ℕ) (j k : Fin d) :
    (quditFT d : Matrix (Fin d) (Fin d) ℂ) j k =
      invSqrtD d * clockRoot d ^ (j.val * k.val) := by
  rfl

end

end QuantumAlg.MatrixWeyl
