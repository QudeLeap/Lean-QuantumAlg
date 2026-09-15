/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Analysis.UnitaryReversal.Amplification

/-!
# Rounding and angle choices for exact amplification

A floor-based iteration count and a final scalar parameter for the matrix
identity motivated by [CML+24, main.tex:680]. This differs from the
source's ceiling-minus-one count when the unrounded value is an integer.
These scalar identities carry no execution or resource interpretation.
-/

@[expose] public section

namespace QuantumAlg.UnitaryReversal

noncomputable section

open MatrixWeyl

variable {d : ℕ}

/-- Floor-based iteration parameter; the source uses a ceiling-minus-one parameter. -/
def quraFloorRounds (hd : 1 ≤ d) : ℕ :=
  let θ := quraAngle hd
  (Int.floor (Real.pi / (2 * θ))).toNat

/-- `quraFloorRounds = ⌊π/(2·Δ_d)⌋` as a real number (the floor is nonnegative). -/
lemma quraFloorRounds_eq_floor (hd : 1 ≤ d) :
    (quraFloorRounds hd : ℝ) = Int.floor (Real.pi / (2 * quraAngle hd)) := by
  unfold quraFloorRounds
  let θ : ℝ := quraAngle hd
  have hθ_pos : 0 < θ := by
    dsimp [θ, quraAngle]
    rw [Real.arcsin_pos]
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    positivity
  have hθ_le : θ ≤ Real.pi / 2 := by
    dsimp [θ, quraAngle]
    have hle : (1 / (d : ℝ)) ≤ 1 := by
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      exact (div_le_one hd0).2 (by exact_mod_cast (by omega : 1 ≤ d))
    have hm := Real.arcsin_le_arcsin hle
    have harcsin_one : Real.arcsin 1 = Real.pi / 2 := by
      rw [← Real.sin_pi_div_two]
      exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    simpa [harcsin_one] using hm
  have hx : 1 ≤ Real.pi / (2 * θ) := by
    have h2θ : 2 * θ ≤ Real.pi := by nlinarith [hθ_le]
    have h2θ_pos : 0 < 2 * θ := by nlinarith [hθ_pos]
    exact one_le_div h2θ_pos |>.mpr (by nlinarith)
  have hf : 0 ≤ Int.floor (Real.pi / (2 * θ)) := by
    have hfloor : (1 : ℤ) ≤ Int.floor (Real.pi / (2 * θ)) := by
      exact (Int.le_floor).mpr (by exact_mod_cast hx : ((1 : ℤ) : ℝ) ≤ Real.pi / (2 * θ))
    omega
  have hnat : ((Int.floor (Real.pi / (2 * θ))).toNat : ℤ) = Int.floor (Real.pi / (2 * θ)) :=
    Int.toNat_of_nonneg hf
  exact_mod_cast hnat

/-- `quraFloorRounds ≥ 3` for `d ≥ 2` (since `π/(2Δ_d) ≥ 3`). -/
lemma quraFloorRounds_ge_three (hd : 2 ≤ d) : 3 ≤ quraFloorRounds (by omega : 1 ≤ d) := by
  have hd1 : 1 ≤ d := by omega
  have hx : 3 ≤ Real.pi / (2 * quraAngle hd1) := by
    have hθ_le : quraAngle hd1 ≤ Real.pi / 6 := by
      have hle : (1 / (d : ℝ)) ≤ (1 / 2 : ℝ) := by
        exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hd : (2 : ℝ) ≤ d)
      have hm := Real.arcsin_le_arcsin hle
      have harcsin_half : Real.arcsin (2 : ℝ)⁻¹ = Real.pi / 6 := by
        rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
        rw [← Real.sin_pi_div_six]
        exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      simpa [quraAngle, harcsin_half] using hm
    have hθ_pos : 0 < quraAngle hd1 := by
      rw [quraAngle, Real.arcsin_pos]
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      positivity
    have h2θ : 2 * quraAngle hd1 ≤ Real.pi / 3 := by nlinarith [hθ_le]
    have h2θ_pos : 0 < 2 * quraAngle hd1 := by nlinarith [hθ_pos]
    calc
      3 = Real.pi / (Real.pi / 3) := by field_simp [Real.pi_pos.ne']
      _ ≤ Real.pi / (2 * quraAngle hd1) := by
        exact div_le_div_of_nonneg_left Real.pi_pos.le h2θ_pos h2θ
  have hfloor : (3 : ℤ) ≤ Int.floor (Real.pi / (2 * quraAngle hd1)) := by
    exact (Int.le_floor).mpr (by exact_mod_cast hx : ((3 : ℤ) : ℝ) ≤ Real.pi / (2 * quraAngle hd1))
  have hm : 3 ≤ ((Int.floor (Real.pi / (2 * quraAngle hd1))).toNat : ℤ) := by
    have hnonneg : 0 ≤ Int.floor (Real.pi / (2 * quraAngle hd1)) := by omega
    rw [Int.toNat_of_nonneg hnonneg]
    omega
  exact_mod_cast hm

/-- `m·Δ_d ≤ π/2`: the amplified angle never overshoots. -/
lemma quraFloorRounds_angle_le_half (hd : 2 ≤ d) :
    (quraFloorRounds (by omega : 1 ≤ d) : ℝ) * quraAngle (by omega : 1 ≤ d) ≤ Real.pi / 2 := by
  have hd1 : 1 ≤ d := by omega
  have hx : Int.floor (Real.pi / (2 * quraAngle hd1)) ≤ Real.pi / (2 * quraAngle hd1) := by
    exact Int.floor_le _
  have hθ_pos : 0 < quraAngle hd1 := by
    rw [quraAngle, Real.arcsin_pos]
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    positivity
  have hmul : (quraFloorRounds hd1 : ℝ) * quraAngle hd1 ≤
      Int.floor (Real.pi / (2 * quraAngle hd1)) * quraAngle hd1 := by
    rw [quraFloorRounds_eq_floor hd1]
  calc
    (quraFloorRounds hd1 : ℝ) * quraAngle hd1
        ≤ Int.floor (Real.pi / (2 * quraAngle hd1)) * quraAngle hd1 := hmul
    _ ≤ Real.pi / (2 * quraAngle hd1) * quraAngle hd1 := by
        exact mul_le_mul_of_nonneg_right hx hθ_pos.le
    _ = Real.pi / 2 := by
        field_simp [hθ_pos.ne']

/-- `m·Δ_d > π/2 − Δ_d`: the amplified angle passes the complement of `Δ_d`. -/
lemma quraFloorRounds_angle_gt (hd : 2 ≤ d) :
    Real.pi / 2 - quraAngle (by omega : 1 ≤ d) <
      (quraFloorRounds (by omega : 1 ≤ d) : ℝ) * quraAngle (by omega : 1 ≤ d) := by
  have hd1 : 1 ≤ d := by omega
  have hθ_pos : 0 < quraAngle hd1 := by
    rw [quraAngle, Real.arcsin_pos]
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    positivity
  have hx : Real.pi / (2 * quraAngle hd1) - 1 < Int.floor (Real.pi / (2 * quraAngle hd1)) := by
    have hf : Real.pi / (2 * quraAngle hd1) < Int.floor (Real.pi / (2 * quraAngle hd1)) + 1 :=
      Int.lt_floor_add_one _
    linarith
  have hmul : (Real.pi / (2 * quraAngle hd1) - 1) * quraAngle hd1 <
      Int.floor (Real.pi / (2 * quraAngle hd1)) * quraAngle hd1 := by
    exact mul_lt_mul_of_pos_right hx hθ_pos
  have hq : (quraFloorRounds hd1 : ℝ) * quraAngle hd1 =
      Int.floor (Real.pi / (2 * quraAngle hd1)) * quraAngle hd1 := by
    rw [quraFloorRounds_eq_floor hd1]
  calc
    Real.pi / 2 - quraAngle hd1
        = (Real.pi / (2 * quraAngle hd1) - 1) * quraAngle hd1 := by
          field_simp [hθ_pos.ne']
    _ < Int.floor (Real.pi / (2 * quraAngle hd1)) * quraAngle hd1 := hmul
    _ = (quraFloorRounds hd1 : ℝ) * quraAngle hd1 := by rw [hq]

/-- `0 < sin(m·Δ_d)` for the floor round count. -/
lemma quraFloorRounds_sin_pos (hd : 2 ≤ d) :
    0 < Real.sin ((quraFloorRounds (by omega : 1 ≤ d) : ℝ) * quraAngle (by omega : 1 ≤ d)) := by
  have hd1 : 1 ≤ d := by omega
  have hθ_le : quraAngle hd1 ≤ Real.pi / 6 := by
    have hle : (1 / (d : ℝ)) ≤ (1 / 2 : ℝ) := by
      exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hd : (2 : ℝ) ≤ d)
    have hm := Real.arcsin_le_arcsin hle
    have harcsin_half : Real.arcsin (2 : ℝ)⁻¹ = Real.pi / 6 := by
      rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
      rw [← Real.sin_pi_div_six]
      exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    simpa [quraAngle, harcsin_half] using hm
  have hmθ_pos : 0 < (quraFloorRounds hd1 : ℝ) * quraAngle hd1 := by
    have hgt := quraFloorRounds_angle_gt hd
    have hlo : 0 < Real.pi / 2 - quraAngle hd1 := by
      have hθ_pos : 0 < quraAngle hd1 := by
        rw [quraAngle, Real.arcsin_pos]
        have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
        positivity
      linarith [hθ_pos, hθ_le]
    linarith
  have hmθ_lt_pi : (quraFloorRounds hd1 : ℝ) * quraAngle hd1 < Real.pi := by
    linarith [quraFloorRounds_angle_le_half hd]
  exact Real.sin_pos_of_pos_of_lt_pi hmθ_pos hmθ_lt_pi

/-- `0 < Δ_d = arcsin(1/d)` for `d ≥ 2`. -/
lemma quraAngle_pos_of_two_le (hd : 2 ≤ d) :
    0 < quraAngle (by omega : 1 ≤ d) := by
  rw [quraAngle, Real.arcsin_pos]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  positivity

/-- `Δ_d = arcsin(1/d) ≤ π/6` for `d ≥ 2`. -/
lemma quraAngle_le_pi_div_six (hd : 2 ≤ d) :
    quraAngle (by omega : 1 ≤ d) ≤ Real.pi / 6 := by
  have hle : (1 / (d : ℝ)) ≤ (1 / 2 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hd : (2 : ℝ) ≤ d)
  have hm := Real.arcsin_le_arcsin hle
  have harcsin_half : Real.arcsin (2 : ℝ)⁻¹ = Real.pi / 6 := by
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
    rw [← Real.sin_pi_div_six]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  simpa [quraAngle, harcsin_half] using hm

/-- The paper's `Δ_d` lies in `(0, π/6]`, so `cos Δ_d > 0`. -/
lemma quraCosAngle_pos (hd : 2 ≤ d) :
    0 < Real.cos (quraAngle (by omega : 1 ≤ d)) := by
  exact Real.cos_pos_of_mem_Ioo
    ⟨by linarith [quraAngle_pos_of_two_le hd, Real.pi_pos],
      by linarith [quraAngle_le_pi_div_six hd, Real.pi_pos]⟩

/-- `0 ≤ α` for `α = cos Δ_d / sin(m·Δ_d)` with the floor round count. -/
lemma quraFloorAlpha_nonneg (hd : 2 ≤ d) :
    0 ≤ Real.cos (quraAngle (by omega : 1 ≤ d)) /
      Real.sin ((quraFloorRounds (by omega : 1 ≤ d) : ℝ) * quraAngle (by omega : 1 ≤ d)) := by
  have hcos : 0 ≤ Real.cos (quraAngle (by omega : 1 ≤ d)) := (quraCosAngle_pos hd).le
  have hsin : 0 ≤
      Real.sin ((quraFloorRounds (by omega : 1 ≤ d) : ℝ) * quraAngle (by omega : 1 ≤ d)) :=
    (quraFloorRounds_sin_pos hd).le
  exact div_nonneg hcos hsin

/-- `α < 1` for `α = cos Δ_d / sin(m·Δ_d)` with the floor round count. -/
lemma quraFloorAlpha_lt_one (hd : 2 ≤ d) :
    Real.cos (quraAngle (by omega : 1 ≤ d)) /
      Real.sin ((quraFloorRounds (by omega : 1 ≤ d) : ℝ) * quraAngle (by omega : 1 ≤ d)) < 1 := by
  have hd1 : 1 ≤ d := by omega
  have hsin : 0 < Real.sin ((quraFloorRounds hd1 : ℝ) * quraAngle hd1) := quraFloorRounds_sin_pos hd
  rw [div_lt_one hsin]
  rw [← Real.sin_pi_div_two_sub]
  exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (by linarith [quraAngle_pos_of_two_le hd, quraAngle_le_pi_div_six hd])
    (quraFloorRounds_angle_le_half hd)
    (quraFloorRounds_angle_gt hd)

/-- `arcsin(α·sin(m·Δ_d)) = π/2 − Δ_d` for the floor-parameter `α`. -/
lemma quraFloor_arcsin_alpha_sin (hd : 2 ≤ d) :
    Real.arcsin (Real.cos (quraAngle (by omega : 1 ≤ d)) /
        Real.sin ((quraFloorRounds (by omega : 1 ≤ d) : ℝ) * quraAngle (by omega : 1 ≤ d)) *
        Real.sin ((quraFloorRounds (by omega : 1 ≤ d) : ℝ) * quraAngle (by omega : 1 ≤ d))) =
      Real.pi / 2 - quraAngle (by omega : 1 ≤ d) := by
  have hd1 : 1 ≤ d := by omega
  have hsin_ne : Real.sin ((quraFloorRounds hd1 : ℝ) * quraAngle hd1) ≠ 0 :=
    (quraFloorRounds_sin_pos hd).ne'
  have hαsin : Real.cos (quraAngle hd1) / Real.sin ((quraFloorRounds hd1 : ℝ) * quraAngle hd1) *
      Real.sin ((quraFloorRounds hd1 : ℝ) * quraAngle hd1) = Real.cos (quraAngle hd1) := by
    field_simp [hsin_ne]
  rw [hαsin]
  rw [← Real.sin_pi_div_two_sub]
  exact Real.arcsin_sin
    (by linarith [quraAngle_pos_of_two_le hd, quraAngle_le_pi_div_six hd])
    (by linarith [quraAngle_pos_of_two_le hd])

end

end QuantumAlg.UnitaryReversal
