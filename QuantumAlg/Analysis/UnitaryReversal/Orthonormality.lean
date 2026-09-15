/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Analysis.UnitaryReversal.Amplification

/-!
# Orthonormality of the amplification subspaces

Adjoint products of the two distinguished matrix-valued subspaces from
[CML+24, main.tex:880].
-/

@[expose] public section

namespace QuantumAlg.UnitaryReversal

noncomputable section

open MatrixWeyl

variable {d : ℕ}

/-! ## Matrix-state orthonormality -/

/-- `Ψ₀†·Ψ₀ = 1`: the encoded target matrix state is an isometry. -/
lemma quraPsi0_adjoint_self (d : ℕ) [NeZero d] (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    (quraPsi0 d U).conjTranspose * quraPsi0 d U = 1 := by
  have hUU : U * U.conjTranspose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hU
  ext s t
  rw [Matrix.mul_apply]
  change (∑ a : Fin d × (Fin d × Fin d),
      star ((if a.1.val = 0 ∧ a.2.1.val = 0 then (1 : ℂ) else 0) * U.conjTranspose a.2.2 s) *
        ((if a.1.val = 0 ∧ a.2.1.val = 0 then (1 : ℂ) else 0) * U.conjTranspose a.2.2 t)) =
    (if s = t then 1 else 0)
  rw [show (∑ a : Fin d × (Fin d × Fin d),
        star ((if a.1.val = 0 ∧ a.2.1.val = 0 then (1 : ℂ) else 0) * U.conjTranspose a.2.2 s) *
          ((if a.1.val = 0 ∧ a.2.1.val = 0 then (1 : ℂ) else 0) * U.conjTranspose a.2.2 t)) =
      (∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d,
        star ((if j.val = 0 ∧ k.val = 0 then (1 : ℂ) else 0) * U.conjTranspose l s) *
          ((if j.val = 0 ∧ k.val = 0 then (1 : ℂ) else 0) * U.conjTranspose l t)) by
    calc
      (∑ a : Fin d × (Fin d × Fin d),
          star ((if a.1.val = 0 ∧ a.2.1.val = 0 then (1 : ℂ) else 0) * U.conjTranspose a.2.2 s) *
            ((if a.1.val = 0 ∧ a.2.1.val = 0 then (1 : ℂ) else 0) * U.conjTranspose a.2.2 t))
          = ∑ j : Fin d, ∑ y : Fin d × Fin d,
              star ((if (j, y).1.val = 0 ∧ (j, y).2.1.val = 0 then (1 : ℂ) else 0) *
                  U.conjTranspose (j, y).2.2 s) *
                ((if (j, y).1.val = 0 ∧ (j, y).2.1.val = 0 then (1 : ℂ) else 0) *
                  U.conjTranspose (j, y).2.2 t) := by
            exact Fintype.sum_prod_type (f := fun a : Fin d × (Fin d × Fin d) =>
              star ((if a.1.val = 0 ∧ a.2.1.val = 0 then (1 : ℂ) else 0) * U.conjTranspose a.2.2 s)
              *
                ((if a.1.val = 0 ∧ a.2.1.val = 0 then (1 : ℂ) else 0) * U.conjTranspose a.2.2 t))
      _ = ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d,
              star ((if j.val = 0 ∧ k.val = 0 then (1 : ℂ) else 0) * U.conjTranspose l s) *
                ((if j.val = 0 ∧ k.val = 0 then (1 : ℂ) else 0) * U.conjTranspose l t) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact Fintype.sum_prod_type (f := fun y : Fin d × Fin d =>
              star ((if (j, y).1.val = 0 ∧ (j, y).2.1.val = 0 then (1 : ℂ) else 0) *
                  U.conjTranspose (j, y).2.2 s) *
                ((if (j, y).1.val = 0 ∧ (j, y).2.1.val = 0 then (1 : ℂ) else 0) *
                  U.conjTranspose (j, y).2.2 t))]
  rw [Finset.sum_eq_single (0 : Fin d)]
  · rw [Finset.sum_eq_single (0 : Fin d)]
    · have hstep : (∑ l : Fin d,
          star ((if (0 : Fin d).val = 0 ∧ (0 : Fin d).val = 0 then (1 : ℂ) else 0) *
          U.conjTranspose l s) *
            ((if (0 : Fin d).val = 0 ∧ (0 : Fin d).val = 0 then (1 : ℂ) else 0) * U.conjTranspose l
            t)) =
          (∑ l : Fin d, U s l * star (U t l)) := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [show (if (0 : Fin d).val = 0 ∧ (0 : Fin d).val = 0 then (1 : ℂ) else 0) = 1 by rfl]
        rw [one_mul, Matrix.conjTranspose_apply, star_star, one_mul, Matrix.conjTranspose_apply]
      have hUUst : (∑ l : Fin d, U s l * star (U t l)) = (if s = t then 1 else 0) := by
        have h := congrFun (congrFun hUU s) t
        change (∑ l : Fin d, U s l * U.conjTranspose l t) = (1 : Matrix (Fin d) (Fin d) ℂ) s t at h
        simpa [Matrix.one_apply] using h
      rw [hstep]
      exact hUUst
    · intro k hk hk0
      have hk' : k.val ≠ 0 := by
        intro h
        apply hk0
        exact Fin.ext h
      simp [hk']
    · intro h
      exact False.elim (h (Finset.mem_univ (0 : Fin d)))
  · intro j hj hj0
    have hj' : j.val ≠ 0 := by
      intro h
      apply hj0
      exact Fin.ext h
    simp [hj']
  · intro h
    exact False.elim (h (Finset.mem_univ (0 : Fin d)))

-- Declaration-scoped exception: simp normalizes filter cardinalities before omega.
set_option linter.flexible false in
/-- `|00⊥⟩` is normalized: `Σ |v(a)|² = 1`. -/
lemma quraKet00Perp_normSq [NeZero d] (hd : 2 ≤ d) :
    (∑ a : Fin d × Fin d, star (quraKet00Perp d a) * quraKet00Perp d a) = 1 := by
  let c : ℂ := ((Real.sqrt ((d : ℝ) ^ 2 - 1) : ℝ) : ℂ)⁻¹
  have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 - 1 := by
    nlinarith [show (1 : ℝ) ≤ (d : ℝ) from by exact_mod_cast (by omega : 1 ≤ d)]
  have hsqrt_ne : ((Real.sqrt ((d : ℝ) ^ 2 - 1) : ℝ) : ℂ) ≠ 0 := by
    have hpos : 0 < Real.sqrt ((d : ℝ) ^ 2 - 1) := by
      exact Real.sqrt_pos.2 (by
        nlinarith [show (2 : ℝ) ≤ (d : ℝ) from by exact_mod_cast hd])
    exact_mod_cast (ne_of_gt hpos)
  have hsqrt_mul : ((Real.sqrt ((d : ℝ) ^ 2 - 1) : ℝ) : ℂ) *
      ((Real.sqrt ((d : ℝ) ^ 2 - 1) : ℝ) : ℂ) = (((d : ℝ) ^ 2 - 1 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    rw [Real.mul_self_sqrt hd2]
  have hmain : (∑ a : Fin d × Fin d, star (quraKet00Perp d a) * quraKet00Perp d a) =
      (∑ a : Fin d × Fin d, (if a.1 = 0 ∧ a.2 = 0 then 0 else star c * c)) := by
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : a.1 = 0 ∧ a.2 = 0
    · simp [quraKet00Perp, h]
    · simp [quraKet00Perp, c, h]
  rw [hmain]
  rw [Finset.sum_ite]
  have hcard : ((Finset.univ : Finset (Fin d × Fin d)).filter
      (fun a => ¬(a.1 = 0 ∧ a.2 = 0))).card = d ^ 2 - 1 := by
    have hc : ((Finset.univ : Finset (Fin d × Fin d)).filter
        (fun a => a.1 = 0 ∧ a.2 = 0)).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨(0, (0 : Fin d)), ?_⟩
      ext a
      simp [Finset.mem_filter]
      constructor
      · intro h
        apply Prod.ext
        · exact Fin.ext (by simpa using h.1)
        · exact Fin.ext (by simpa using h.2)
      · intro hEq
        simp [hEq]
    have hc2 : ((Finset.univ : Finset (Fin d × Fin d)).filter
          (fun a => a.1 = 0 ∧ a.2 = 0)).card +
        ((Finset.univ : Finset (Fin d × Fin d)).filter
          (fun a => ¬(a.1 = 0 ∧ a.2 = 0))).card =
        Fintype.card (Fin d × Fin d) := by
      simpa using (Finset.card_filter_add_card_filter_not
        (fun a : Fin d × Fin d => a.1 = 0 ∧ a.2 = 0)
        (s := (Finset.univ : Finset (Fin d × Fin d))))
    rw [hc] at hc2
    simp [Fintype.card_prod, Fintype.card_fin, pow_two] at hc2 ⊢
    omega
  have hstar : star c * c = (1 : ℂ) / (((Real.sqrt ((d : ℝ) ^ 2 - 1) : ℝ) : ℂ) *
      ((Real.sqrt ((d : ℝ) ^ 2 - 1) : ℝ) : ℂ)) := by
    dsimp [c]
    have hs : (starRingEnd ℂ) (((Real.sqrt ((d : ℝ) ^ 2 - 1) : ℝ) : ℂ)⁻¹) =
        ((Real.sqrt ((d : ℝ) ^ 2 - 1) : ℝ) : ℂ)⁻¹ := by
      simp [Complex.conj_ofReal]
    rw [hs]
    field_simp [hsqrt_ne]
  rw [Finset.sum_const, Finset.sum_const]
  simp only [nsmul_eq_mul]
  rw [hcard]
  rw [hstar]
  rw [hsqrt_mul]
  have hcast : (((d : ℕ) ^ 2 - 1 : ℕ) : ℂ) = (((d : ℝ) ^ 2 - 1 : ℝ) : ℂ) := by
    have hle : 1 ≤ (d : ℕ) ^ 2 := by nlinarith [hd]
    rw [Nat.cast_sub hle]
    simp [Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_natCast, Nat.cast_pow]
  rw [hcast]
  have hd2ne : (((d : ℝ) ^ 2 - 1 : ℝ) : ℂ) ≠ 0 := by
    have hgt : 0 < (d : ℝ) ^ 2 - 1 := by
      nlinarith [show (2 : ℝ) ≤ (d : ℝ) from by exact_mod_cast hd]
    exact_mod_cast (ne_of_gt hgt)
  field_simp [hd2ne]
  simp

-- Declaration-scoped exception: simp removes identity factors before exact hvec.
set_option linter.flexible false in
/-- `Ψ⊥†·Ψ⊥ = 1`: the perpendicular matrix state is an isometry. -/
lemma quraPsiPerp_adjoint_self (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    (quraPsiPerp d U).conjTranspose * quraPsiPerp d U = 1 := by
  have hD : quraDecoder U * (quraDecoder U).conjTranspose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff.mp ((decoderOperator ⟨U, hU⟩).property)
  have hvec : (quraVecState d (quraKet00Perp d)).conjTranspose * quraVecState d (quraKet00Perp d) =
  1 := by
    ext s t
    rw [Matrix.mul_apply]
    change (∑ a : Fin d × (Fin d × Fin d),
        star (quraKet00Perp d (a.1, a.2.1) * (if a.2.2 = s then 1 else 0)) *
          (quraKet00Perp d (a.1, a.2.1) * (if a.2.2 = t then 1 else 0))) =
      (if s = t then 1 else 0)
    rw [show (∑ a : Fin d × (Fin d × Fin d),
          star (quraKet00Perp d (a.1, a.2.1) * (if a.2.2 = s then 1 else 0)) *
            (quraKet00Perp d (a.1, a.2.1) * (if a.2.2 = t then 1 else 0))) =
        (∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d,
          star (quraKet00Perp d (j, k) * (if l = s then 1 else 0)) *
            (quraKet00Perp d (j, k) * (if l = t then 1 else 0))) by
      calc
        (∑ a : Fin d × (Fin d × Fin d),
            star (quraKet00Perp d (a.1, a.2.1) * (if a.2.2 = s then 1 else 0)) *
              (quraKet00Perp d (a.1, a.2.1) * (if a.2.2 = t then 1 else 0)))
            = ∑ j : Fin d, ∑ y : Fin d × Fin d,
                star (quraKet00Perp d ((j, y).1, (j, y).2.1) * (if (j, y).2.2 = s then 1 else 0)) *
                  (quraKet00Perp d ((j, y).1, (j, y).2.1) * (if (j, y).2.2 = t then 1 else 0)) := by
              exact Fintype.sum_prod_type (f := fun a : Fin d × (Fin d × Fin d) =>
                star (quraKet00Perp d (a.1, a.2.1) * (if a.2.2 = s then 1 else 0)) *
                  (quraKet00Perp d (a.1, a.2.1) * (if a.2.2 = t then 1 else 0)))
        _ = ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d,
                star (quraKet00Perp d (j, k) * (if l = s then 1 else 0)) *
                  (quraKet00Perp d (j, k) * (if l = t then 1 else 0)) := by
              apply Finset.sum_congr rfl
              intro j hj
              exact Fintype.sum_prod_type (f := fun y : Fin d × Fin d =>
                star (quraKet00Perp d ((j, y).1, (j, y).2.1) * (if (j, y).2.2 = s then 1 else 0)) *
                  (quraKet00Perp d ((j, y).1, (j, y).2.1) * (if (j, y).2.2 = t then 1 else 0)))]
    have hinner : ∀ j k : Fin d,
        (∑ l : Fin d,
            star (quraKet00Perp d (j, k) * (if l = s then 1 else 0)) *
              (quraKet00Perp d (j, k) * (if l = t then 1 else 0))) =
          (if s = t then 1 else 0) * star (quraKet00Perp d (j, k)) * quraKet00Perp d (j, k) := by
      intro j k
      by_cases hst : s = t
      · subst t
        rw [Finset.sum_eq_single s]
        · simp
        · intro l hl hl0
          simp [hl0]
        · intro h
          exact False.elim (h (Finset.mem_univ s))
      · rw [if_neg hst, zero_mul, zero_mul]
        apply Finset.sum_eq_zero
        intro l hl
        by_cases hls : l = s
        · subst l
          simp [hst]
        · simp [hls]
    rw [show (∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d,
          star (quraKet00Perp d (j, k) * (if l = s then 1 else 0)) *
            (quraKet00Perp d (j, k) * (if l = t then 1 else 0))) =
        (∑ j : Fin d, ∑ k : Fin d,
          (if s = t then 1 else 0) * star (quraKet00Perp d (j, k)) * quraKet00Perp d (j, k)) by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      exact hinner j k]
    by_cases hst : s = t
    · subst t
      simp
      simpa [Fintype.sum_prod_type] using quraKet00Perp_normSq hd
    · simp [hst]
  rw [quraPsiPerp]
  rw [Matrix.conjTranspose_mul]
  rw [Matrix.conjTranspose_conjTranspose]
  rw [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (quraDecoder U)]
  rw [hD]
  simp
  exact hvec

/-- `Ψ₀†·Ψ⊥ = 0`: the two matrix states are orthogonal. -/
lemma quraPsi0_adjoint_psiPerp (d : ℕ) [NeZero d] (U : Matrix (Fin d) (Fin d) ℂ)
    (_hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    (quraPsi0 d U).conjTranspose * quraPsiPerp d U = 0 := by
  ext s t
  rw [Matrix.mul_apply]
  change (∑ a : Fin d × (Fin d × Fin d),
      star ((if a.1.val = 0 ∧ a.2.1.val = 0 then (1 : ℂ) else 0) * U.conjTranspose a.2.2 s) *
        quraPsiPerp d U (a.1, (a.2.1, a.2.2)) t) = 0
  rw [show (∑ a : Fin d × (Fin d × Fin d),
        star ((if a.1.val = 0 ∧ a.2.1.val = 0 then (1 : ℂ) else 0) * U.conjTranspose a.2.2 s) *
          quraPsiPerp d U (a.1, (a.2.1, a.2.2)) t) =
      (∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d,
        star ((if j.val = 0 ∧ k.val = 0 then (1 : ℂ) else 0) * U.conjTranspose l s) *
          quraPsiPerp d U (j, (k, l)) t) by
    calc
      (∑ a : Fin d × (Fin d × Fin d),
          star ((if a.1.val = 0 ∧ a.2.1.val = 0 then (1 : ℂ) else 0) * U.conjTranspose a.2.2 s) *
            quraPsiPerp d U (a.1, (a.2.1, a.2.2)) t)
          = ∑ j : Fin d, ∑ y : Fin d × Fin d,
              star ((if (j, y).1.val = 0 ∧ (j, y).2.1.val = 0 then (1 : ℂ) else 0) *
                  U.conjTranspose (j, y).2.2 s) *
                quraPsiPerp d U ((j, y).1, ((j, y).2.1, (j, y).2.2)) t := by
            exact Fintype.sum_prod_type (f := fun a : Fin d × (Fin d × Fin d) =>
              star ((if a.1.val = 0 ∧ a.2.1.val = 0 then (1 : ℂ) else 0) * U.conjTranspose a.2.2 s)
              *
                quraPsiPerp d U (a.1, (a.2.1, a.2.2)) t)
      _ = ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d,
              star ((if j.val = 0 ∧ k.val = 0 then (1 : ℂ) else 0) * U.conjTranspose l s) *
                quraPsiPerp d U (j, (k, l)) t := by
            apply Finset.sum_congr rfl
            intro j hj
            exact Fintype.sum_prod_type (f := fun y : Fin d × Fin d =>
              star ((if (j, y).1.val = 0 ∧ (j, y).2.1.val = 0 then (1 : ℂ) else 0) *
                  U.conjTranspose (j, y).2.2 s) *
                quraPsiPerp d U ((j, y).1, ((j, y).2.1, (j, y).2.2)) t)]
  rw [Finset.sum_eq_single (0 : Fin d)]
  · rw [Finset.sum_eq_single (0 : Fin d)]
    · apply Finset.sum_eq_zero
      intro l hl
      rw [quraPsiPerp_00_zero d U t l]
      simp
    · intro k hk hk0
      have hk' : k.val ≠ 0 := by
        intro h
        apply hk0
        exact Fin.ext h
      simp [hk']
    · intro h
      exact False.elim (h (Finset.mem_univ (0 : Fin d)))
  · intro j hj hj0
    have hj' : j.val ≠ 0 := by
      intro h
      apply hj0
      exact Fin.ext h
    simp [hj']
  · intro h
    exact False.elim (h (Finset.mem_univ (0 : Fin d)))

/-- `Ψ⊥†·Ψ₀ = 0`: the two matrix states are orthogonal (conjugate direction). -/
lemma quraPsiPerp_adjoint_psi0 (d : ℕ) [NeZero d] (U : Matrix (Fin d) (Fin d) ℂ)
    (_hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    (quraPsiPerp d U).conjTranspose * quraPsi0 d U = 0 := by
  ext s t
  rw [Matrix.mul_apply]
  change (∑ a : Fin d × (Fin d × Fin d),
      star (quraPsiPerp d U (a.1, (a.2.1, a.2.2)) s) *
        ((if a.1.val = 0 ∧ a.2.1.val = 0 then (1 : ℂ) else 0) * U.conjTranspose a.2.2 t)) = 0
  rw [show (∑ a : Fin d × (Fin d × Fin d),
        star (quraPsiPerp d U (a.1, (a.2.1, a.2.2)) s) *
          ((if a.1.val = 0 ∧ a.2.1.val = 0 then (1 : ℂ) else 0) * U.conjTranspose a.2.2 t)) =
      (∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d,
        star (quraPsiPerp d U (j, (k, l)) s) *
          ((if j.val = 0 ∧ k.val = 0 then (1 : ℂ) else 0) * U.conjTranspose l t)) by
    calc
      (∑ a : Fin d × (Fin d × Fin d),
          star (quraPsiPerp d U (a.1, (a.2.1, a.2.2)) s) *
            ((if a.1.val = 0 ∧ a.2.1.val = 0 then (1 : ℂ) else 0) * U.conjTranspose a.2.2 t))
          = ∑ j : Fin d, ∑ y : Fin d × Fin d,
              star (quraPsiPerp d U ((j, y).1, ((j, y).2.1, (j, y).2.2)) s) *
                ((if (j, y).1.val = 0 ∧ (j, y).2.1.val = 0 then (1 : ℂ) else 0) *
                  U.conjTranspose (j, y).2.2 t) := by
            exact Fintype.sum_prod_type (f := fun a : Fin d × (Fin d × Fin d) =>
              star (quraPsiPerp d U (a.1, (a.2.1, a.2.2)) s) *
                ((if a.1.val = 0 ∧ a.2.1.val = 0 then (1 : ℂ) else 0) * U.conjTranspose a.2.2 t))
      _ = ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d,
              star (quraPsiPerp d U (j, (k, l)) s) *
                ((if j.val = 0 ∧ k.val = 0 then (1 : ℂ) else 0) * U.conjTranspose l t) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact Fintype.sum_prod_type (f := fun y : Fin d × Fin d =>
              star (quraPsiPerp d U ((j, y).1, ((j, y).2.1, (j, y).2.2)) s) *
                ((if (j, y).1.val = 0 ∧ (j, y).2.1.val = 0 then (1 : ℂ) else 0) *
                  U.conjTranspose (j, y).2.2 t))]
  rw [Finset.sum_eq_single (0 : Fin d)]
  · rw [Finset.sum_eq_single (0 : Fin d)]
    · apply Finset.sum_eq_zero
      intro l hl
      rw [quraPsiPerp_00_zero d U s l]
      simp
    · intro k hk hk0
      have hk' : k.val ≠ 0 := by
        intro h
        apply hk0
        exact Fin.ext h
      simp [hk']
    · intro h
      exact False.elim (h (Finset.mem_univ (0 : Fin d)))
  · intro j hj hj0
    have hj' : j.val ≠ 0 := by
      intro h
      apply hj0
      exact Fin.ext h
    simp [hj']
  · intro h
    exact False.elim (h (Finset.mem_univ (0 : Fin d)))

end

end QuantumAlg.UnitaryReversal
