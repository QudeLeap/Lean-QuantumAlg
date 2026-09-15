/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.State.Normalized

public import QuantumAlg.Analysis.UnitaryReversal.EncoderUnitary

/-!
# Duality-based amplification as a matrix recurrence

The two-dimensional invariant-subspace recurrence and its iteration
[CML+24, main.tex:985], [CML+24, main.tex:999].
The recurrence does not count oracle calls or provide an executable circuit.
-/

@[expose] public section

namespace QuantumAlg.UnitaryReversal

noncomputable section

open MatrixWeyl

-- Preserve symbolic basis coefficients until a proof requests their entry formula.
attribute [-simp] NormalizedVector.ket_apply

variable {d : ℕ}

local notation "k₀" => (NormalizedVector.ket (R := Qubits 1) 0)


local notation "Z[" d "]" => (clockMatrix d : Matrix (Fin d) (Fin d) ℂ)
local notation "X[" d "]" => (shiftMatrix d : Matrix (Fin d) (Fin d) ℂ)
local notation "FT[" d "]" => (quditFT d : Matrix (Fin d) (Fin d) ℂ)



/-- The QURA rotation angle `θ_d = arcsin(1/d)`. -/
@[nolint unusedArguments]
def quraAngle (_hd : 1 ≤ d) : ℝ := Real.arcsin (1 / (d : ℝ))

/-- The main-construction round count `k = max(0, ⌊π/(2·θ_d)⌋ − 1)`. -/
lemma decoder_mul_plus_entry (U : Matrix (Fin d) (Fin d) ℂ)
    (a : Fin d × (Fin d × Fin d)) (s : Fin d) :
    (quraDecoder U * qudPlusState d) a s =
      (invSqrtD d * invSqrtD d) *
        (((X[d])⁻¹ ^ a.1.val * (Z[d])⁻¹ ^ a.2.1.val * U *
          (X[d])⁻¹ ^ a.1.val * Z[d] ^ a.2.1.val) a.2.2 s) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (a.1, a.2.1, s)]
  · rw [qudPlusState_apply]
    have hD : quraDecoder U a (a.1, a.2.1, s) =
        ((X[d])⁻¹ ^ a.1.val * (Z[d])⁻¹ ^ a.2.1.val * U *
          (X[d])⁻¹ ^ a.1.val * Z[d] ^ a.2.1.val) a.2.2 s := by
      simp [quraDecoder]
    rw [hD]
    simp
    ring
  · intro c hc hne
    by_cases h3 : c.2.2 = s
    · have hx : ¬(c.1 = a.1 ∧ c.2.1 = a.2.1) := by
        intro h
        apply hne
        cases c with
        | mk c1 c2 =>
          cases c2 with
          | mk c21 c22 =>
            have h' : c1 = a.1 ∧ c21 = a.2.1 := h
            have h3' : c22 = s := by simpa using h3
            simp [h'.1, h'.2, h3']
      have hx' : ¬(a.1 = c.1 ∧ a.2.1 = c.2.1) := by
        intro h
        apply hx
        exact ⟨h.1.symm, h.2.symm⟩
      simp [quraDecoder, hx', h3]
    · simp [qudPlusState_apply, h3]
  · intro h
    exact False.elim (h (Finset.mem_univ (a.1, a.2.1, s)))

/-- `(FT⊗FT⊗I)·Λ₀ = |++⟩⊗I`. -/
lemma qudTensorFT_mul_lambda0 [NeZero d] :
    qudTensor3 (FT[d]) (FT[d]) 1 * quraLambda0 d = qudPlusState d := by
  ext a s
  simp only [Matrix.mul_apply, quraLambda0, qudPlusState_apply, qudTensor3_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (0, (0, s))]
  · -- main term
    simp [quditFT_entry]
  · intro b hb hne
    by_cases h1 : b.1.val = 0 ∧ b.2.1.val = 0
    · by_cases h3 : b.2.2 = s
      · exfalso
        apply hne
        apply Prod.ext
        · exact Fin.ext h1.1
        · apply Prod.ext
          · exact Fin.ext h1.2
          · exact h3
      · have hL : quraLambda0 d b s = 0 := by
          simp only [quraLambda0]
          dsimp
          simp [h3]
        change (FT[d] a.1 b.1 * FT[d] a.2.1 b.2.1 * (if a.2.2 = b.2.2 then 1 else 0)) *
          quraLambda0 d b s = 0
        rw [hL]
        simp
    · have hL : quraLambda0 d b s = 0 := by
        simp only [quraLambda0]
        dsimp
        rw [if_neg h1]
        simp
      change (FT[d] a.1 b.1 * FT[d] a.2.1 b.2.1 * (if a.2.2 = b.2.2 then 1 else 0)) *
        quraLambda0 d b s = 0
      rw [hL]
      simp
  · intro h
    exact False.elim (h (Finset.mem_univ (0, (0, s))))

/-- The select-adjoint applied to `|++⟩⊗I`, entrywise. -/
lemma select_conjTranspose_mul_plus_entry (U : Matrix (Fin d) (Fin d) ℂ)
    (a : Fin d × (Fin d × Fin d)) (s : Fin d) :
    ((quraSelect (U.map (starRingEnd ℂ))).conjTranspose * qudPlusState d) a s =
      (invSqrtD d * invSqrtD d) *
        ((Z[d] ^ a.1.val * X[d] ^ a.2.1.val * (U.map (starRingEnd ℂ)) *
          (Z[d])⁻¹ ^ a.1.val * X[d] ^ a.2.1.val).conjTranspose a.2.2 s) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (a.1, a.2.1, s)]
  · rw [qudPlusState_apply]
    have hS : (quraSelect (U.map (starRingEnd ℂ))).conjTranspose a (a.1, a.2.1, s) =
        ((Z[d] ^ a.1.val * X[d] ^ a.2.1.val * (U.map (starRingEnd ℂ)) *
          (Z[d])⁻¹ ^ a.1.val * X[d] ^ a.2.1.val).conjTranspose) a.2.2 s := by
      rw [Matrix.conjTranspose_apply]
      simp [quraSelect]
    rw [hS]
    simp
    ring
  · intro c hc hne
    by_cases h3 : c.2.2 = s
    · have hx : ¬(c.1 = a.1 ∧ c.2.1 = a.2.1) := by
        intro h
        apply hne
        cases c with
        | mk c1 c2 =>
          cases c2 with
          | mk c21 c22 =>
            have h' : c1 = a.1 ∧ c21 = a.2.1 := h
            have h3' : c22 = s := by simpa using h3
            simp [h'.1, h'.2, h3']
      have hx' : ¬(a.1 = c.1 ∧ a.2.1 = c.2.1) := by
        intro h
        apply hx
        exact ⟨h.1.symm, h.2.symm⟩
      rw [Matrix.conjTranspose_apply]
      simp [quraSelect, hx]
    · simp [qudPlusState_apply, h3]
  · intro h
    exact False.elim (h (Finset.mem_univ (a.1, a.2.1, s)))

/-- `E(U)†·Λ₀ = T†·(S†·(|++⟩⊗I))` with `T† = FT⊗FT⊗I`. -/
lemma encoder_conjTranspose_lambda0 [NeZero d] (U : Matrix (Fin d) (Fin d) ℂ) :
    (quraEncoder U).conjTranspose * quraLambda0 d =
      qudTensor3 (FT[d]) (FT[d]) 1 *
        ((quraSelect (U.map (starRingEnd ℂ))).conjTranspose * qudPlusState d) := by
  unfold quraEncoder
  rw [Matrix.conjTranspose_mul]
  rw [Matrix.conjTranspose_mul]
  rw [quraTensorT_conjTranspose]
  rw [Matrix.mul_assoc]
  rw [Matrix.mul_assoc]
  rw [qudTensorFT_mul_lambda0]

/-- The encoder-adjoint applied to `Λ₀`, entrywise. -/
lemma encoder_conjTranspose_lambda0_entry [NeZero d] (U : Matrix (Fin d) (Fin d) ℂ)
    (a : Fin d × (Fin d × Fin d)) (s : Fin d) :
    ((quraEncoder U).conjTranspose * quraLambda0 d) a s =
      (invSqrtD d * invSqrtD d) * (invSqrtD d * invSqrtD d) *
        (∑ j : Fin d, ∑ k : Fin d,
          (clockRoot d ^ (a.1.val * j.val)) * (clockRoot d ^ (a.2.1.val * k.val)) *
            ((Z[d] ^ j.val * X[d] ^ k.val * (U.map (starRingEnd ℂ)) *
              (Z[d])⁻¹ ^ j.val * X[d] ^ k.val).conjTranspose) a.2.2 s) := by
  rw [encoder_conjTranspose_lambda0]
  rw [Matrix.mul_apply]
  calc
    (∑ j : Fin d × (Fin d × Fin d), qudTensor3 (FT[d]) (FT[d]) 1 a j *
        ((quraSelect (U.map (starRingEnd ℂ))).conjTranspose * qudPlusState d) j s)
        = ∑ j : Fin d × (Fin d × Fin d), qudTensor3 (FT[d]) (FT[d]) 1 a j *
            ((invSqrtD d * invSqrtD d) *
              ((Z[d] ^ j.1.val * X[d] ^ j.2.1.val * (U.map (starRingEnd ℂ)) *
                (Z[d])⁻¹ ^ j.1.val * X[d] ^ j.2.1.val).conjTranspose) j.2.2 s) :=
                by
          apply Finset.sum_congr rfl
          intro j hj
          rw [select_conjTranspose_mul_plus_entry U j s]
    _ = (∑ j : Fin d × (Fin d × Fin d), (FT[d]) a.1 j.1 * (FT[d]) a.2.1 j.2.1 *
            (if a.2.2 = j.2.2 then 1 else 0) *
            ((invSqrtD d * invSqrtD d) *
              ((Z[d] ^ j.1.val * X[d] ^ j.2.1.val * (U.map (starRingEnd ℂ)) *
                (Z[d])⁻¹ ^ j.1.val * X[d] ^ j.2.1.val).conjTranspose) j.2.2 s))
                := by
          apply Finset.sum_congr rfl
          intro j hj
          simp only [qudTensor3_apply, Matrix.one_apply]
    _ = (∑ j1 : Fin d, ∑ j2 : Fin d, (FT[d]) a.1 j1 * (FT[d]) a.2.1 j2 *
            ((invSqrtD d * invSqrtD d) *
              ((Z[d] ^ j1.val * X[d] ^ j2.val * (U.map (starRingEnd ℂ)) *
                (Z[d])⁻¹ ^ j1.val * X[d] ^ j2.val).conjTranspose) a.2.2 s)) := by
          simp only [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro j1 hj1
          apply Finset.sum_congr rfl
          intro j2 hj2
          rw [Finset.sum_eq_single a.2.2]
          · rw [if_pos rfl]
            simp
          · intro t ht hne
            rw [if_neg (fun hh => hne hh.symm)]
            simp
          · intro h
            exact False.elim (h (Finset.mem_univ a.2.2))
    _ = (invSqrtD d * invSqrtD d) * (invSqrtD d * invSqrtD d) *
          (∑ j : Fin d, ∑ k : Fin d,
            (clockRoot d ^ (a.1.val * j.val)) * (clockRoot d ^ (a.2.1.val * k.val)) *
              ((Z[d] ^ j.val * X[d] ^ k.val * (U.map (starRingEnd ℂ)) *
                (Z[d])⁻¹ ^ j.val * X[d] ^ k.val).conjTranspose) a.2.2 s) := by
          -- j = (j1, (k, a.2.2)) — split and expand FT entries
          simp only [quditFT_entry]
          -- pull the invSqrtD factors out
          rw [show (∑ j : Fin d, ∑ k : Fin d,
              invSqrtD d * clockRoot d ^ (a.1.val * j.val) *
                (invSqrtD d * clockRoot d ^ (a.2.1.val * k.val)) *
                  (invSqrtD d * invSqrtD d *
                    ((Z[d] ^ j.val * X[d] ^ k.val * (U.map (starRingEnd ℂ)) *
                      (Z[d])⁻¹ ^ j.val * X[d] ^ k.val).conjTranspose) a.2.2 s) =
              (invSqrtD d * invSqrtD d) * (invSqrtD d * invSqrtD d) *
                (∑ j : Fin d, ∑ k : Fin d,
                  (clockRoot d ^ (a.1.val * j.val)) * (clockRoot d ^ (a.2.1.val * k.val)) *
                    ((Z[d] ^ j.val * X[d] ^ k.val * (U.map (starRingEnd ℂ)) *
                      (Z[d])⁻¹ ^ j.val * X[d] ^ k.val).conjTranspose) a.2.2 s)) by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring]

-- Declaration-scoped exception: simp normalizes conjugation in h0 before exact h0.
set_option linter.flexible false in
/-- The conjugate of `dual_sum_entry`: `Σ_{j,k} ω^{rj+tk}·block† m s = d·block' m s`. -/
lemma dual_sum_entry_star [NeZero d] (hd : d ≠ 0) (U : Matrix (Fin d) (Fin d) ℂ)
    (r t m s : Fin d) :
    (∑ j : Fin d, ∑ k : Fin d,
      (clockRoot d ^ (r.val * j.val)) * (clockRoot d ^ (t.val * k.val)) *
        ((Z[d] ^ j.val * X[d] ^ k.val * (U.map (starRingEnd ℂ)) *
          (Z[d])⁻¹ ^ j.val * X[d] ^ k.val).conjTranspose) m s) =
      (d : ℂ) * ((X[d])⁻¹ ^ r.val * (Z[d])⁻¹ ^ t.val * U *
        (X[d])⁻¹ ^ r.val * Z[d] ^ t.val) m s := by
  have h0 := congrArg star (dual_sum_entry hd U r t s m)
  simp [star_pow, star_inv₀, star_clockRoot hd, Matrix.conjTranspose_apply] at h0
  exact h0

/-- `D(U)·(|++⟩⊗I) = E(U)†·Λ₀` (paper `cor:O1`, second duality). -/
lemma quraDecoder_mul_plus [NeZero d] (hd : d ≠ 0) (U : Matrix (Fin d) (Fin d) ℂ) :
    quraDecoder U * qudPlusState d = (quraEncoder U).conjTranspose * quraLambda0 d := by
  ext a s
  rw [decoder_mul_plus_entry U a s]
  rw [encoder_conjTranspose_lambda0_entry U a s]
  have hdual := dual_sum_entry_star hd U a.1 a.2.1 a.2.2 s
  rw [hdual]
  have hfac : (invSqrtD d * invSqrtD d) * (invSqrtD d * invSqrtD d) * (d : ℂ) =
      invSqrtD d * invSqrtD d := by
    rw [invSqrtD_mul_self]
    field_simp [show (d : ℂ) ≠ 0 from by exact_mod_cast hd]
    norm_num
  calc
    (invSqrtD d * invSqrtD d) *
          ((X[d])⁻¹ ^ a.1.val * (Z[d])⁻¹ ^ a.2.1.val * U *
            (X[d])⁻¹ ^ a.1.val * Z[d] ^ a.2.1.val) a.2.2 s
        = (invSqrtD d * invSqrtD d) * (invSqrtD d * invSqrtD d) * (d : ℂ) *
            ((X[d])⁻¹ ^ a.1.val * (Z[d])⁻¹ ^ a.2.1.val * U *
              (X[d])⁻¹ ^ a.1.val * Z[d] ^ a.2.1.val) a.2.2 s := by
          conv_lhs => rw [← hfac]
    _ = (invSqrtD d * invSqrtD d) * (invSqrtD d * invSqrtD d) *
          ((d : ℂ) * ((X[d])⁻¹ ^ a.1.val * (Z[d])⁻¹ ^ a.2.1.val * U *
            (X[d])⁻¹ ^ a.1.val * Z[d] ^ a.2.1.val) a.2.2 s) := by
          ring

lemma E_LambdaPerp_decompose [NeZero d] (hd : 2 ≤ d) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quraEncoder U * quraLambdaPerp d U =
      quraCosDelta d • quraPsi0 d U - (1 / (d : ℂ)) • quraPsiPerp d U := by
  have hUU : U * U.conjTranspose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hU
  have hEE : quraEncoder U * (quraEncoder U).conjTranspose = 1 := by
    have hE := (encoderOperator ⟨U, hU⟩).property
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hE
  have hEE' : (quraEncoder U).conjTranspose * quraEncoder U = 1 := by
    have hE := (encoderOperator ⟨U, hU⟩).property
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hE
  let s : ℂ := ((Real.sqrt ((d : ℝ) ^ 2 - 1) : ℝ) : ℂ)⁻¹
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h4 : 4 ≤ (d : ℝ) ^ 2 := by nlinarith [hdR]
  have hpos : 0 < (d : ℝ) ^ 2 - 1 := by
    have hgt : 1 < (d : ℝ) ^ 2 := by nlinarith [h4]
    linarith
  have hsqrt0 : ((Real.sqrt ((d : ℝ) ^ 2 - 1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hpos))
  have hsqrt2 : ((Real.sqrt ((d : ℝ) ^ 2 - 1) : ℝ) : ℂ) ^ 2 = (d : ℂ) ^ 2 - 1 := by
    rw [← Complex.ofReal_pow]
    rw [Real.sq_sqrt]
    · rw [Complex.ofReal_sub, Complex.ofReal_pow]
      norm_num
    · nlinarith [show (2 : ℝ) ≤ (d : ℝ) from by exact_mod_cast hd]
  have hsc1 : s * ((d : ℂ) - 1 / (d : ℂ)) = quraCosDelta d := by
    dsimp [s, quraCosDelta]
    field_simp [hd0, hsqrt0]
    rw [hsqrt2]
  have hsc2 : s * quraCosDelta d = 1 / (d : ℂ) := by
    dsimp [s, quraCosDelta]
    field_simp [hd0, hsqrt0]
  have hV : quraVecState d (quraKet00Perp d) =
      s • ((d : ℂ) • quraVecState d (quraKetPlusPlus d) - quraVecState d (quraKet00 d)) := by
    ext a t
    change quraKet00Perp d (a.1, a.2.1) * (if a.2.2 = t then 1 else 0) =
      s * ((d : ℂ) * (quraKetPlusPlus d (a.1, a.2.1) * (if a.2.2 = t then 1 else 0)) -
        (quraKet00 d (a.1, a.2.1) * (if a.2.2 = t then 1 else 0)))
    have hp := quraKet00Perp_decompose hd (a.1, a.2.1)
    rw [show ((Real.sqrt ((d : ℝ) ^ 2 - 1) : ℝ) : ℂ)⁻¹ = s by rfl] at hp
    rw [hp]
    ring
  have hPlusDec : qudPlusState d =
      (1 / (d : ℂ)) • quraLambda0 d + quraCosDelta d • quraVecState d (quraKet00Perp d) := by
    rw [show qudPlusState d = quraVecState d (quraKetPlusPlus d) by
      ext a t
      simp [qudPlusState_apply, quraVecState_apply, quraKetPlusPlus]]
    rw [quraPlusPlus_decompose hd]
    rw [quraVecState_add, quraVecState_smul, quraVecState_smul]
    rfl
  have hscalar : s • ((d : ℂ) • quraLambda0 d - qudPlusState d) =
      quraCosDelta d • quraLambda0 d - (1 / (d : ℂ)) • quraVecState d (quraKet00Perp d) := by
    rw [hPlusDec]
    rw [smul_sub, smul_add, smul_smul, smul_smul, smul_smul]
    rw [show (s * (d : ℂ)) • quraLambda0 d -
          ((s * (1 / (d : ℂ))) • quraLambda0 d + (s * quraCosDelta d) • quraVecState d
          (quraKet00Perp d)) =
        (s * (d : ℂ) - s * (1 / (d : ℂ))) • quraLambda0 d -
          (s * quraCosDelta d) • quraVecState d (quraKet00Perp d) by
      rw [sub_smul]
      simp [sub_eq_add_neg, add_assoc, add_comm]]
    rw [show s * (d : ℂ) - s * (1 / (d : ℂ)) = s * ((d : ℂ) - 1 / (d : ℂ)) by ring]
    rw [hsc1, hsc2]
  have hLU : quraLambda0 d * U.conjTranspose = quraTarget d U := by
    ext a s
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single a.2.2]
    · have hL : quraLambda0 d a a.2.2 = (if a.1.val = 0 ∧ a.2.1.val = 0 then 1 else 0) := by
        simp [quraLambda0]
      rw [hL]
      change (if a.1.val = 0 ∧ a.2.1.val = 0 then 1 else 0) * U.conjTranspose a.2.2 s =
        (if a.1.val = 0 ∧ a.2.1.val = 0 then 1 else 0) * U.conjTranspose a.2.2 s
      rfl
    · intro t ht hne
      have hL : quraLambda0 d a t = 0 := by
        simp only [quraLambda0]
        dsimp
        have hnot : ¬ a.2.2 = t := fun hh => hne hh.symm
        simp [hnot]
      rw [hL]
      simp
    · intro h
      exact False.elim (h (Finset.mem_univ a.2.2))
  have hPU : quraKet00PerpU d U = quraVecState d (quraKet00Perp d) * U.conjTranspose := by
    ext a s
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single a.2.2]
    · simp [quraVecState_apply, quraKet00PerpU]
    · intro t ht hne
      have hV : quraVecState d (quraKet00Perp d) a t = 0 := by
        simp [quraVecState_apply]
        have hnot : ¬ a.2.2 = t := fun hh => hne hh.symm
        simp [hnot]
      rw [hV]
      simp
    · intro h
      exact False.elim (h (Finset.mem_univ a.2.2))
  have hsub : (d : ℂ) • quraTarget d U - (quraDecoder U).conjTranspose * qudPlusState d =
      (quraDecoder U).conjTranspose * ((d : ℂ) • quraLambda0 d - qudPlusState d) := by
    rw [← D_dag_lambda0]
    rw [← Matrix.mul_smul]
    rw [← Matrix.mul_sub]
  calc
    quraEncoder U * quraLambdaPerp d U
        = quraEncoder U * (quraDecoder U * quraKet00PerpU d U) := by rfl
    _ = quraEncoder U * (quraDecoder U * (quraVecState d (quraKet00Perp d) * U.conjTranspose)) := by
          rw [hPU]
    _ = quraEncoder U * ((quraDecoder U * quraVecState d (quraKet00Perp d)) * U.conjTranspose) := by
          congr 1
          rw [Matrix.mul_assoc]
    _ = quraEncoder U * ((s • ((d : ℂ) • (quraDecoder U * qudPlusState d) - quraDecoder U *
    quraLambda0 d)) * U.conjTranspose) := by
          rw [hV]
          rw [Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_smul]
          rfl
    _ = quraEncoder U * ((s • ((d : ℂ) • ((quraEncoder U).conjTranspose * quraLambda0 d) -
    quraLambda0 d * U)) * U.conjTranspose) := by
          rw [quraDecoder_mul_plus (by omega : d ≠ 0) U]
          rw [quraDecoder_mulVec_ket00]
    _ = quraEncoder U * (s • (((d : ℂ) • ((quraEncoder U).conjTranspose * quraLambda0 d)) *
    U.conjTranspose -
          (quraLambda0 d * U) * U.conjTranspose)) := by
          rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_smul]
    _ = quraEncoder U * (s • (((d : ℂ) • ((quraEncoder U).conjTranspose * quraLambda0 d)) *
    U.conjTranspose -
          quraLambda0 d)) := by
          rw [Matrix.mul_assoc, hUU]
          simp
    _ = quraEncoder U * (s • ((d : ℂ) • (((quraEncoder U).conjTranspose * quraLambda0 d) *
    U.conjTranspose) -
          quraLambda0 d)) := by
          congr 1
          congr 1
          rw [Matrix.smul_mul]
    _ = quraEncoder U * (s • ((d : ℂ) • ((quraEncoder U).conjTranspose * (quraLambda0 d *
    U.conjTranspose)) -
          quraLambda0 d)) := by
          rw [← Matrix.mul_assoc]
    _ = quraEncoder U * (s • ((d : ℂ) • ((quraEncoder U).conjTranspose * quraTarget d U) -
          quraLambda0 d)) := by
          rw [hLU]
    _ = quraEncoder U * (s • ((quraEncoder U).conjTranspose *
          ((d : ℂ) • quraTarget d U - quraEncoder U * quraLambda0 d))) := by
          congr 1
          congr 1
          have hΛ : quraLambda0 d = (quraEncoder U).conjTranspose * (quraEncoder U * quraLambda0 d)
          := by
            rw [← Matrix.mul_assoc]
            rw [hEE']
            simp
          calc
            (d : ℂ) • ((quraEncoder U).conjTranspose * quraTarget d U) - quraLambda0 d
                = (d : ℂ) • ((quraEncoder U).conjTranspose * quraTarget d U) -
                    (quraEncoder U).conjTranspose * (quraEncoder U * quraLambda0 d) := by
                  conv_lhs => rw [hΛ]
            _ = (quraEncoder U).conjTranspose * ((d : ℂ) • quraTarget d U) -
                    (quraEncoder U).conjTranspose * (quraEncoder U * quraLambda0 d) := by
                  rw [← Matrix.mul_smul]
            _ = (quraEncoder U).conjTranspose *
                    ((d : ℂ) • quraTarget d U - quraEncoder U * quraLambda0 d) := by
                  rw [← Matrix.mul_sub]
    _ = quraEncoder U * (s • ((quraEncoder U).conjTranspose *
          ((d : ℂ) • quraTarget d U - (quraDecoder U).conjTranspose * qudPlusState d))) := by
          rw [qura_duality (by omega : d ≠ 0) U]
    _ = quraEncoder U * (s • ((quraEncoder U).conjTranspose * (quraDecoder U).conjTranspose *
          ((d : ℂ) • quraLambda0 d - qudPlusState d))) := by
          rw [hsub]
          rw [← Matrix.mul_assoc]
    _ = (quraDecoder U).conjTranspose * (s • ((d : ℂ) • quraLambda0 d - qudPlusState d)) := by
          rw [Matrix.mul_smul]
          conv_lhs =>
            rw [show quraEncoder U * ((quraEncoder U).conjTranspose * (quraDecoder U).conjTranspose
            *
                  ((d : ℂ) • quraLambda0 d - qudPlusState d)) =
                (quraDecoder U).conjTranspose * ((d : ℂ) • quraLambda0 d - qudPlusState d) by
              rw [← Matrix.mul_assoc]
              rw [← Matrix.mul_assoc]
              rw [hEE]
              simp]
          rw [← Matrix.mul_smul]
    _ = (quraDecoder U).conjTranspose * (quraCosDelta d • quraLambda0 d -
          (1 / (d : ℂ)) • quraVecState d (quraKet00Perp d)) := by
          rw [hscalar]
    _ = quraCosDelta d • ((quraDecoder U).conjTranspose * quraLambda0 d) -
          (1 / (d : ℂ)) • ((quraDecoder U).conjTranspose * quraVecState d (quraKet00Perp d)) := by
          rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul]
    _ = quraCosDelta d • quraPsi0 d U - (1 / (d : ℂ)) • quraPsiPerp d U := by
          rw [D_dag_lambda0]
          rw [show quraPsi0 d U = quraTarget d U by rfl]
          rw [quraPsiPerp]

/-- `I₂ ⊗ E(U)` on the ancilla qubit and the three-qudit register. -/
def quraI2E (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin 2 × (Fin d × (Fin d × Fin d))) ℂ :=
  Matrix.of fun a b =>
    (if a.1 = b.1 then 1 else 0) *
      quraEncoder U (a.2.1, (a.2.2.1, a.2.2.2)) (b.2.1, (b.2.2.1, b.2.2.2))

/-- `(I₂⊗E(U))·(|0⟩⊗M) = |0⟩⊗(E(U)·M)`. -/
lemma quraI2E_mul_ket0 (U : Matrix (Fin d) (Fin d) ℂ)
    (M : Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ) :
    quraI2E d U * (Matrix.of fun a s => k₀ a.1 * M (a.2.1, (a.2.2.1, a.2.2.2)) s) =
      Matrix.of fun a s => k₀ a.1 * (quraEncoder U * M) (a.2.1, (a.2.2.1, a.2.2.2)) s := by
  ext a s
  simp [quraI2E, Matrix.mul_apply, Fintype.sum_prod_type, mul_comm, NormalizedVector.ket_apply]

/-- The duality-based amplitude amplifier `A(U) = (I₂⊗E(U))·D̃(U)`. -/
def quraAmplifier (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin 2 × (Fin d × (Fin d × Fin d))) ℂ :=
  quraI2E d U * quraTildeD d U

/-- `A(U)·(|0⟩⊗Ψ₀) = cosΔ·(|0⟩⊗Ψ₀) − (1/d)·(|0⟩⊗Ψ⊥)` (paper `lem:oracle_d`). -/
lemma quraAmplifier_mul_ket0_psi0 [NeZero d] (hd : 2 ≤ d)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quraAmplifier d U * (Matrix.of fun a s =>
        k₀ a.1 * quraPsi0 d U (a.2.1, (a.2.2.1, a.2.2.2)) s) =
      Matrix.of fun a s =>
        k₀ a.1 * (quraCosDelta d • quraPsi0 d U (a.2.1, (a.2.2.1, a.2.2.2)) s -
          (1 / (d : ℂ)) • quraPsiPerp d U (a.2.1, (a.2.2.1, a.2.2.2)) s) := by
  rw [quraAmplifier]
  simp only [Matrix.mul_assoc]
  rw [quraTildeD_mul_ket0_psi0]
  rw [quraI2E_mul_ket0]
  rw [E_LambdaPerp_decompose hd U hU]
  rfl

/-- `A(U)·(|0⟩⊗Ψ⊥) = (1/d)·(|0⟩⊗Ψ₀) + cosΔ·(|0⟩⊗Ψ⊥)` (paper `lem:oracle_d`). -/
lemma quraAmplifier_mul_ket0_psiPerp [NeZero d] (hd : 2 ≤ d)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quraAmplifier d U * (Matrix.of fun a s =>
        k₀ a.1 * quraPsiPerp d U (a.2.1, (a.2.2.1, a.2.2.2)) s) =
      Matrix.of fun a s =>
        k₀ a.1 * ((1 / (d : ℂ)) • quraPsi0 d U (a.2.1, (a.2.2.1, a.2.2.2)) s +
          quraCosDelta d • quraPsiPerp d U (a.2.1, (a.2.2.1, a.2.2.2)) s) := by
  rw [quraAmplifier]
  simp only [Matrix.mul_assoc]
  rw [quraTildeD_mul_ket0_psiPerp d hd U hU]
  rw [quraI2E_mul_ket0]
  rw [E_Lambda0_decompose hd U]
  rfl

/-! ## Arc-length rotation (Eq. A.8) -/

/-- The QURA rotation angle `θ_d = arcsin(1/d)`, as a complex number. -/
@[nolint unusedArguments]
def quraTheta (_hd : 1 ≤ d) : ℂ := (Real.arcsin (1 / (d : ℝ)) : ℂ)

/-- `sin θ_d = 1/d` (Lemma S3 coefficient). -/
lemma quraTheta_sin (hd : 1 ≤ d) : Complex.sin (quraTheta hd) = 1 / (d : ℂ) := by
  rw [quraTheta]
  rw [← Complex.ofReal_sin]
  rw [Real.sin_arcsin]
  · norm_num
  · have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hnonneg : 0 ≤ (1 : ℝ) / d := by positivity
    linarith
  · have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    field_simp [hd0]
    exact_mod_cast hd

/-- `cos θ_d = cos Δ_d` (the complex cosine is the QURA cosine). -/
lemma quraTheta_cos (hd : 1 ≤ d) : Complex.cos (quraTheta hd) = quraCosDelta d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 - 1 := by
    nlinarith [show (1 : ℝ) ≤ (d : ℝ) from by exact_mod_cast hd]
  rw [quraTheta]
  rw [← Complex.ofReal_cos]
  rw [Real.cos_arcsin]
  rw [show 1 - (1 / (d : ℝ)) ^ 2 = ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 2 by
    field_simp [hd0]]
  rw [Real.sqrt_div hd2]
  rw [Real.sqrt_sq (by positivity : 0 ≤ (d : ℝ))]
  rw [Complex.ofReal_div]
  rfl

/-- `sin ((k+1)·θ_d) = sin (k·θ_d)·cos θ_d + cos (k·θ_d)·sin θ_d`. -/
lemma quraTheta_sin_add_one (hd : 1 ≤ d) (k : ℕ) :
    Complex.sin (((k + 1 : ℕ) : ℂ) * quraTheta hd) =
      Complex.sin (((k : ℕ) : ℂ) * quraTheta hd) * Complex.cos (quraTheta hd) +
        Complex.cos (((k : ℕ) : ℂ) * quraTheta hd) * Complex.sin (quraTheta hd) := by
  rw [show ((k + 1 : ℕ) : ℂ) * quraTheta hd = ((k : ℕ) : ℂ) * quraTheta hd + quraTheta hd by
    rw [show ((k + 1 : ℕ) : ℂ) = ((k : ℕ) : ℂ) + 1 by simp [Nat.cast_add]]
    ring]
  rw [Complex.sin_add]

/-- `cos ((k+1)·θ_d) = cos (k·θ_d)·cos θ_d - sin (k·θ_d)·sin θ_d`. -/
lemma quraTheta_cos_add_one (hd : 1 ≤ d) (k : ℕ) :
    Complex.cos (((k + 1 : ℕ) : ℂ) * quraTheta hd) =
      Complex.cos (((k : ℕ) : ℂ) * quraTheta hd) * Complex.cos (quraTheta hd) -
        Complex.sin (((k : ℕ) : ℂ) * quraTheta hd) * Complex.sin (quraTheta hd) := by
  rw [show ((k + 1 : ℕ) : ℂ) * quraTheta hd = ((k : ℕ) : ℂ) * quraTheta hd + quraTheta hd by
    rw [show ((k + 1 : ℕ) : ℂ) = ((k : ℕ) : ℂ) + 1 by simp [Nat.cast_add]]
    ring]
  rw [Complex.cos_add]

/-- `|0⟩ ⊗ M`: the ancilla qubit in `|0⟩` tensored with a three-qudit matrix state. -/
def quraKet0Mat (d : ℕ) (M : Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ) :
    Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin d) ℂ :=
  Matrix.of fun a s => k₀ a.1 * M (a.2.1, (a.2.2.1, a.2.2.2)) s

/-- `c₀•|0⟩A + c₁•|0⟩B = |0⟩(c₀•A + c₁•B)`. -/
lemma quraKet0Mat_smul_add (d : ℕ) (c0 c1 : ℂ)
    (A B : Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ) :
    c0 • quraKet0Mat d A + c1 • quraKet0Mat d B = quraKet0Mat d (c0 • A + c1 • B) := by
  ext a s
  simp [quraKet0Mat, smul_eq_mul, mul_comm]
  ring

/-- `D̃(U)` acts linearly on the span: `D̃(c₀·|0⟩Ψ₀ + c₁·|0⟩Ψ⊥) = c₀·|0⟩Λ⊥ + c₁·|0⟩Λ₀`. -/
lemma quraTildeD_mul_ket0_span (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (c0 c1 : ℂ) :
    quraTildeD d U * (c0 • quraKet0Mat d (quraPsi0 d U) + c1 • quraKet0Mat d (quraPsiPerp d U)) =
      c0 • quraKet0Mat d (quraLambdaPerp d U) + c1 • quraKet0Mat d (quraLambda0 d) := by
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
  simp only [quraKet0Mat]
  rw [quraTildeD_mul_ket0_psi0]
  rw [quraTildeD_mul_ket0_psiPerp d hd U hU]

/-- `A(U)` rotates the span by `Δ`: on the `(Ψ₀, Ψ⊥)` basis it is the rotation matrix. -/
lemma quraAmplifier_mul_ket0_span (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (c0 c1 : ℂ) :
    quraAmplifier d U * (c0 • quraKet0Mat d (quraPsi0 d U) + c1 • quraKet0Mat d (quraPsiPerp d U)) =
      (c0 * quraCosDelta d + c1 * (1 / (d : ℂ))) • quraKet0Mat d (quraPsi0 d U) +
        (c1 * quraCosDelta d - c0 * (1 / (d : ℂ))) • quraKet0Mat d (quraPsiPerp d U) := by
  rw [quraAmplifier]
  simp only [Matrix.mul_assoc]
  rw [quraTildeD_mul_ket0_span d hd U hU]
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
  simp only [quraKet0Mat]
  rw [quraI2E_mul_ket0]
  rw [quraI2E_mul_ket0]
  rw [E_LambdaPerp_decompose hd U hU]
  rw [E_Lambda0_decompose hd U]
  ext a s
  simp [smul_eq_mul, mul_add, mul_sub, add_mul, sub_mul, mul_assoc, mul_left_comm]
  ring

/-- The encoded initial matrix state `(1₂⊗E(U))·(|0⟩⊗Λ₀) = |0⟩⊗(sinΔ·Ψ₀ + cosΔ·Ψ⊥)`. -/
def quraEncodedState (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin d) ℂ :=
  (1 / (d : ℂ)) • quraKet0Mat d (quraPsi0 d U) + quraCosDelta d • quraKet0Mat d (quraPsiPerp d U)

/-- The rotated span state `sin(k·θ_d)·|0⟩⊗Ψ₀ + cos(k·θ_d)·|0⟩⊗Ψ⊥`. -/
def quraSpanState (hd : 1 ≤ d) (k : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin d) ℂ :=
  Complex.sin (((k : ℕ) : ℂ) * quraTheta hd) • quraKet0Mat d (quraPsi0 d U) +
    Complex.cos (((k : ℕ) : ℂ) * quraTheta hd) • quraKet0Mat d (quraPsiPerp d U)

/-- Arc-length rotation identity (paper Eq. A.8): after `k` amplifier rounds,
`A(U)^k · (1₂⊗E(U))·(|0⟩⊗Λ₀) = sin((k+1)·θ_d)·|0⟩⊗Ψ₀ + cos((k+1)·θ_d)·|0⟩⊗Ψ⊥`. -/
lemma quraAmplifier_pow_mul_encoded (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (k : ℕ) :
    (quraAmplifier d U) ^ k * quraEncodedState d U =
      quraSpanState (by omega : 1 ≤ d) (k + 1) U := by
  induction k with
  | zero =>
      rw [pow_zero]
      simp only [zero_add]
      simp only [quraEncodedState, quraSpanState]
      rw [← quraTheta_sin (by omega : 1 ≤ d)]
      rw [← quraTheta_cos (by omega : 1 ≤ d)]
      simp
  | succ k ih =>
      rw [pow_succ']
      simp only [Matrix.mul_assoc]
      rw [ih]
      simp only [quraSpanState]
      rw [quraAmplifier_mul_ket0_span d hd U hU]
      rw [← quraTheta_sin (by omega : 1 ≤ d)]
      rw [← quraTheta_cos (by omega : 1 ≤ d)]
      rw [quraTheta_sin_add_one (by omega : 1 ≤ d) (k + 1)]
      rw [quraTheta_cos_add_one (by omega : 1 ≤ d) (k + 1)]

/-- `(1₂⊗E(U))·(|0⟩⊗Λ₀) = |0⟩⊗(sinΔ·Ψ₀ + cosΔ·Ψ⊥)`. -/
lemma quraI2E_mul_ket0_lambda0 (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (U : Matrix (Fin d) (Fin d) ℂ) :
    quraI2E d U * quraKet0Mat d (quraLambda0 d) = quraEncodedState d U := by
  simp only [quraKet0Mat]
  rw [quraI2E_mul_ket0]
  rw [E_Lambda0_decompose hd U]
  rw [quraEncodedState]
  rw [quraKet0Mat_smul_add]
  rfl

end

end QuantumAlg.UnitaryReversal
