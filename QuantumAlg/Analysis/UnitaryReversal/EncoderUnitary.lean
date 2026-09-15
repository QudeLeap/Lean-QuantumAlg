/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Analysis.UnitaryReversal.Decoding

/-!
# Unitarity of the encoder formula

Unitarity is conditional on a unitary input matrix. The conjugate input is
used directly in the encoder formula [CML+24, main.tex:738].
-/

@[expose] public section

namespace QuantumAlg.UnitaryReversal

noncomputable section

open MatrixWeyl

variable {d : ℕ}

local notation "Z[" d "]" => (clockMatrix d : Matrix (Fin d) (Fin d) ℂ)
local notation "X[" d "]" => (shiftMatrix d : Matrix (Fin d) (Fin d) ℂ)
local notation "FT[" d "]" => (quditFT d : Matrix (Fin d) (Fin d) ℂ)



-- Declaration-scoped exception: simp unfolds ket entries before inverse-square-root rewrites.
set_option linter.flexible false in
lemma quraKet00Perp_decompose (hd : 2 ≤ d) (a : Fin d × Fin d) :
    quraKet00Perp d a =
      ((Real.sqrt ((d : ℝ) ^ 2 - 1) : ℝ) : ℂ)⁻¹ *
        ((d : ℂ) * quraKetPlusPlus d a - quraKet00 d a) := by
  by_cases h0 : a.1.val = 0 ∧ a.2.val = 0
  · have hd0 : (d : ℂ) ≠ 0 := by
      exact_mod_cast (by omega : d ≠ 0)
    simp [quraKet00Perp, quraKetPlusPlus, quraKet00, h0]
    rw [invSqrtD_mul_self]
    field_simp [hd0]
    simp
  · have hd0 : (d : ℂ) ≠ 0 := by
      exact_mod_cast (by omega : d ≠ 0)
    simp [quraKet00Perp, quraKetPlusPlus, quraKet00, h0]
    rw [invSqrtD_mul_self]
    field_simp [hd0]
    simp

/-- `D(U)·(|00⟩⊗I) = |00⟩⊗U`. -/
lemma quraDecoder_mulVec_ket00 [NeZero d] (U : Matrix (Fin d) (Fin d) ℂ) :
    quraDecoder U * quraLambda0 d = quraLambda0 d * U := by
  ext a s
  rw [Matrix.mul_apply]
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (0, (0, s))]
  · -- main term: D(a,(0,(0,s)))·1 = ket00(a.1,a.2.1)·U(a.2.2,s)
    have hD : quraDecoder U a (0, (0, s)) =
        (if a.1 = 0 ∧ a.2.1 = 0 then U a.2.2 s else 0) := by
      by_cases h0 : a.1 = 0 ∧ a.2.1 = 0
      · have ha1 : (a.1.val : ℕ) = 0 := congrArg Fin.val h0.1
        have ha2 : (a.2.1.val : ℕ) = 0 := congrArg Fin.val h0.2
        change (if a.1 = 0 ∧ a.2.1 = 0 then
            ((X[d])⁻¹ ^ a.1.val * (Z[d])⁻¹ ^ a.2.1.val * U *
              (X[d])⁻¹ ^ a.1.val * Z[d] ^ a.2.1.val) a.2.2 s
          else 0) = (if a.1 = 0 ∧ a.2.1 = 0 then U a.2.2 s else 0)
        rw [if_pos h0]
        rw [if_pos h0]
        rw [ha1, ha2]
        simp
      · change (if a.1 = 0 ∧ a.2.1 = 0 then
            ((X[d])⁻¹ ^ a.1.val * (Z[d])⁻¹ ^ a.2.1.val * U *
              (X[d])⁻¹ ^ a.1.val * Z[d] ^ a.2.1.val) a.2.2 s
          else 0) = (if a.1 = 0 ∧ a.2.1 = 0 then U a.2.2 s else 0)
        rw [if_neg h0]
        rw [if_neg h0]
    have hL : quraLambda0 d (0, (0, s)) s = 1 := by
      simp [quraLambda0]
    have hR : (∑ j : Fin d, quraLambda0 d a j * U j s) = quraLambda0 d a a.2.2 * U a.2.2 s := by
      rw [Finset.sum_eq_single a.2.2]
      · intro j hj hne
        have hL0 : quraLambda0 d a j = 0 := by
          simp only [quraLambda0]
          dsimp
          have hnotj : ¬ a.2.2 = j := fun hh => hne hh.symm
          simp [hnotj]
        rw [hL0]
        simp
      · intro h
        exact False.elim (h (Finset.mem_univ a.2.2))
    rw [hD, hL, hR]
    by_cases h0 : a.1 = 0 ∧ a.2.1 = 0
    · have ha1 : (a.1.val : ℕ) = 0 := congrArg Fin.val h0.1
      have ha2 : (a.2.1.val : ℕ) = 0 := congrArg Fin.val h0.2
      rw [if_pos h0]
      change U a.2.2 s * 1 = (if a.1.val = 0 ∧ a.2.1.val = 0 then 1 else 0) *
        (if a.2.2 = a.2.2 then 1 else 0) * U a.2.2 s
      rw [ha1, ha2]
      simp
    · have hL0 : quraLambda0 d a a.2.2 = 0 := by
        have hnot : ¬ (a.1.val = 0 ∧ a.2.1.val = 0) := by
          intro hh
          apply h0
          exact ⟨Fin.ext hh.1, Fin.ext hh.2⟩
        simp only [quraLambda0]
        dsimp
        rw [if_neg hnot]
        simp
      rw [if_neg h0, hL0]
      simp
  · -- h₀: other b: D(a,b)·Λ₀(b,s) = 0
    intro b hb hne
    by_cases h00 : b.1.val = 0 ∧ b.2.1.val = 0
    · by_cases h3 : b.2.2 = s
      · -- b = (0,(0,s)): contradiction with hne
        exfalso
        apply hne
        apply Prod.ext
        · exact Fin.ext h00.1
        · apply Prod.ext
          · exact Fin.ext h00.2
          · exact h3
      · have h3' : ¬(b.2.2 = s) := h3
        simp [quraLambda0, h3']
    · have hL : quraLambda0 d b s = 0 := by
        simp only [quraLambda0]
        dsimp
        rw [if_neg h00]
        simp
      rw [hL]
      simp
  · -- h₁: the singleton is in univ
    intro h
    exact False.elim (h (Finset.mem_univ (0, (0, s))))

/-- Each select block `M_{jk} = Z^j X^k U* Z^{-j} X^k` is unitary. -/
lemma select_block_unitary' (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (j k : Fin d) :
    Z[d] ^ j.val * X[d] ^ k.val * (U.map (starRingEnd ℂ)) *
      (Z[d])⁻¹ ^ j.val * X[d] ^ k.val *
      (Z[d] ^ j.val * X[d] ^ k.val * (U.map (starRingEnd ℂ)) *
        (Z[d])⁻¹ ^ j.val * X[d] ^ k.val).conjTranspose = 1 := by
  set M : Matrix (Fin d) (Fin d) ℂ :=
    Z[d] ^ j.val * X[d] ^ k.val * (U.map (starRingEnd ℂ)) *
      (Z[d])⁻¹ ^ j.val * X[d] ^ k.val with hMdef
  have hM : M ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    rw [hMdef]
    exact mul_mem (mul_mem (mul_mem (mul_mem (pow_mem (clockMatrix d).property j.val)
      (pow_mem (shiftMatrix d).property k.val)) (map_star_mem_unitaryGroup U hU))
      (clockMatrix_inv_pow_mem_unitaryGroup j)) (pow_mem (shiftMatrix d).property k.val)
  have h' : M * star M = 1 := Matrix.mem_unitaryGroup_iff.mp hM
  rw [Matrix.star_eq_conjTranspose] at h'
  exact h'

-- Declaration-scoped exception: simp exposes select blocks before finite-sum extraction.
set_option linter.flexible false in
/-- The block-select matrix `E_FT(U*)` is unitary when `U` is. -/
private lemma quraSelect_mem_unitaryGroup (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quraSelect (U.map (starRingEnd ℂ)) ∈ Matrix.unitaryGroup (Fin d × (Fin d × Fin d)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  rw [Matrix.mul_apply]
  by_cases hb : a.1 = b.1 ∧ a.2.1 = b.2.1
  · rcases hb with ⟨r, t⟩
    have hsum : (∑ c : Fin d × (Fin d × Fin d),
        quraSelect (U.map (starRingEnd ℂ)) a c * star (quraSelect (U.map (starRingEnd ℂ))) c b) =
        (if a.2.2 = b.2.2 then 1 else 0) := by
      simp [quraSelect]
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single a.1]
      · rw [Fintype.sum_prod_type]
        rw [Finset.sum_eq_single a.2.1]
        · -- remaining sum over x: Σ x, M_{a.2.2,x}·star(M_{b.2.2,x}) = δ
          simp [r, t]
          have hmm : (∑ x : Fin d,
              (Z[d] ^ b.1.val * X[d] ^ b.2.1.val * (U.map (starRingEnd ℂ)) *
                (Z[d])⁻¹ ^ b.1.val * X[d] ^ b.2.1.val) a.2.2 x *
                starRingEnd ℂ ((Z[d] ^ b.1.val * X[d] ^ b.2.1.val *
                  (U.map (starRingEnd ℂ)) * (Z[d])⁻¹ ^ b.1.val * X[d] ^ b.2.1.val)
                    b.2.2 x)) =
              (Z[d] ^ b.1.val * X[d] ^ b.2.1.val * (U.map (starRingEnd ℂ)) *
                (Z[d])⁻¹ ^ b.1.val * X[d] ^ b.2.1.val *
                (Z[d] ^ b.1.val * X[d] ^ b.2.1.val * (U.map (starRingEnd ℂ)) *
                  (Z[d])⁻¹ ^ b.1.val * X[d] ^ b.2.1.val).conjTranspose) a.2.2
                  b.2.2 := by
            rw [Matrix.mul_apply]
            simp only [Matrix.conjTranspose_apply]
            rfl
          rw [hmm]
          have hblock := select_block_unitary' U hU b.1 b.2.1
          rw [hblock]
          simp [Matrix.one_apply]
        · intro p hp hne
          apply Finset.sum_eq_zero
          intro y hy
          have hnot : ¬(a.2.1 = p) := fun h => hne h.symm
          simp [hnot]
        · intro h
          exact False.elim (h (Finset.mem_univ a.2.1))
      · intro c1 hc1 hne
        by_cases h : c1 = a.1
        · exfalso
          apply hne
          exact h
        · apply Finset.sum_eq_zero
          intro x hx
          have hnot : ¬(a.1 = c1) := fun hh => h hh.symm
          simp [hnot]
      · intro h
        exact False.elim (h (Finset.mem_univ a.1))
    rw [hsum]
    simp only [Matrix.one_apply]
    by_cases h22 : a.2.2 = b.2.2
    · have hab : a = b := by
        apply Prod.ext
        · exact r
        · apply Prod.ext
          · exact t
          · exact h22
      simp [hab]
    · have hab : a ≠ b := by
        intro h
        apply h22
        exact congrArg (fun x : Fin d × (Fin d × Fin d) => x.2.2) h
      simp [hab, h22]
  · -- a.1 ≠ b.1 ∨ a.2.1 ≠ b.2.1 → the sum is 0 = δ
    have hsum0 : (∑ c : Fin d × (Fin d × Fin d),
        quraSelect (U.map (starRingEnd ℂ)) a c * star (quraSelect (U.map (starRingEnd ℂ))) c b) = 0
        := by
      apply Finset.sum_eq_zero
      intro c hc
      by_cases hca : a.1 = c.1 ∧ a.2.1 = c.2.1
      · have hcb : ¬(c.1 = b.1 ∧ c.2.1 = b.2.1) := by
          intro h
          apply hb
          exact ⟨hca.1.trans h.1, hca.2.trans h.2⟩
        have hcb' : ¬(b.1 = c.1 ∧ b.2.1 = c.2.1) := by
          intro h
          apply hcb
          exact ⟨h.1.symm, h.2.symm⟩
        have h1' : a.1 = c.1 ∧ a.2.1 = c.2.1 := hca
        simp [quraSelect, h1', hcb']
      · have hca' : ¬(a.1 = c.1 ∧ a.2.1 = c.2.1) := hca
        simp [quraSelect, hca']
    rw [hsum0]
    have hab : a ≠ b := by
      intro h
      apply hb
      exact ⟨congrArg (fun x : Fin d × (Fin d × Fin d) => x.1) h,
        congrArg (fun x : Fin d × (Fin d × Fin d) => x.2.1) h⟩
    simp [hab]

/-- `(A⊗B⊗C)† = A†⊗B†⊗C†` for the three-qudit tensor. -/
lemma quraTensorT_conjTranspose (d : ℕ) :
    (qudTensor3 (FT[d]).conjTranspose (FT[d]).conjTranspose 1).conjTranspose =
      qudTensor3 (FT[d]) (FT[d]) 1 := by
  ext a b
  rw [Matrix.conjTranspose_apply]
  simp only [qudTensor3_apply, Matrix.one_apply, Matrix.conjTranspose_apply]
  by_cases h : a.2.2 = b.2.2
  · have h' : b.2.2 = a.2.2 := h.symm
    simp [h']
  · have h' : ¬(b.2.2 = a.2.2) := fun hh => h hh.symm
    rw [if_neg h, if_neg h']
    simp

/-- The Fourier tensor `T = FT†⊗FT†⊗I` is unitary. -/
lemma quraT_mem_unitaryGroup (d : ℕ) :
    qudTensor3 (FT[d]).conjTranspose (FT[d]).conjTranspose 1 ∈
      Matrix.unitaryGroup (Fin d × (Fin d × Fin d)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  rw [Matrix.star_eq_conjTranspose]
  rw [quraTensorT_conjTranspose]
  have hft : (FT[d]).conjTranspose * FT[d] = 1 := by
    have hmem : FT[d] ∈ Matrix.unitaryGroup (Fin d) ℂ :=
      (quditFT d).property
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hmem
  ext a b
  rw [Matrix.mul_apply]
  simp only [Fintype.sum_prod_type, qudTensor3_apply, Matrix.one_apply]
  calc
    (∑ c1 : Fin d, ∑ c2 : Fin d, ∑ t : Fin d,
        (FT[d]).conjTranspose a.1 c1 * (FT[d]).conjTranspose a.2.1 c2 *
          (if a.2.2 = t then 1 else 0) *
          (FT[d] c1 b.1 * FT[d] c2 b.2.1 * (if t = b.2.2 then 1 else 0)))
        = ∑ c1 : Fin d, ∑ c2 : Fin d,
            (FT[d]).conjTranspose a.1 c1 * (FT[d]).conjTranspose a.2.1 c2 *
              (FT[d] c1 b.1 * FT[d] c2 b.2.1) * (if a.2.2 = b.2.2 then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro c1 hc1
          apply Finset.sum_congr rfl
          intro c2 hc2
          rw [Finset.sum_eq_single a.2.2]
          · by_cases hab : a.2.2 = b.2.2
            · rw [if_pos rfl, if_pos hab]
              ring
            · rw [if_pos rfl, if_neg hab]
              simp
          · intro t ht hne
            rw [if_neg (fun hh => hne hh.symm)]
            simp
          · intro h
            exact False.elim (h (Finset.mem_univ a.2.2))
    _ = (∑ c1 : Fin d, (FT[d]).conjTranspose a.1 c1 * FT[d] c1 b.1) *
          (∑ c2 : Fin d, (FT[d]).conjTranspose a.2.1 c2 * FT[d] c2 b.2.1) *
          (if a.2.2 = b.2.2 then 1 else 0) := by
          by_cases hab : a.2.2 = b.2.2
          · rw [if_pos hab]
            simp only [mul_one]
            rw [show (∑ c1 : Fin d, ∑ c2 : Fin d,
                  (FT[d]).conjTranspose a.1 c1 * (FT[d]).conjTranspose a.2.1 c2 *
                    (FT[d] c1 b.1 * FT[d] c2 b.2.1)) =
                ∑ c1 : Fin d, ((FT[d]).conjTranspose a.1 c1 * FT[d] c1 b.1) *
                    (∑ c2 : Fin d, (FT[d]).conjTranspose a.2.1 c2 * FT[d] c2 b.2.1) by
              apply Finset.sum_congr rfl
              intro c1 hc1
              symm
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro c2 hc2
              ring]
            rw [← Finset.sum_mul]
          · rw [if_neg hab]
            simp
    _ = (1 : Matrix (Fin d × (Fin d × Fin d)) (Fin d × (Fin d × Fin d)) ℂ) a b := by
          have hf : (∑ c1 : Fin d, (FT[d]).conjTranspose a.1 c1 * FT[d] c1 b.1) =
              if a.1 = b.1 then 1 else 0 := by
            rw [← Matrix.mul_apply]
            rw [hft]
            rfl
          have hg : (∑ c2 : Fin d, (FT[d]).conjTranspose a.2.1 c2 * FT[d] c2 b.2.1) =
              if a.2.1 = b.2.1 then 1 else 0 := by
            rw [← Matrix.mul_apply]
            rw [hft]
            rfl
          rw [hf, hg]
          have hprod : (if a.1 = b.1 then (1 : ℂ) else 0) * (if a.2.1 = b.2.1 then (1 : ℂ) else 0) *
                (if a.2.2 = b.2.2 then (1 : ℂ) else 0) = if a = b then (1 : ℂ) else 0 := by
            by_cases hab : a = b
            · subst b
              simp
            · have h1' : ¬(a.1 = b.1 ∧ a.2.1 = b.2.1 ∧ a.2.2 = b.2.2) := by
                intro h
                apply hab
                apply Prod.ext
                · exact h.1
                · apply Prod.ext
                  · exact h.2.1
                  · exact h.2.2
              by_cases h1 : a.1 = b.1
              · by_cases h2 : a.2.1 = b.2.1
                · have h3' : ¬(a.2.2 = b.2.2) := by
                    intro h
                    apply h1'
                    exact ⟨h1, h2, h⟩
                  rw [if_pos h1, if_pos h2, if_neg h3', if_neg hab]
                  norm_num
                · rw [if_pos h1, if_neg h2, if_neg hab]
                  simp
              · rw [if_neg h1, if_neg hab]
                simp
          have h1ab : (if a = b then 1 else 0) =
              (1 : Matrix (Fin d × (Fin d × Fin d)) (Fin d × (Fin d × Fin d)) ℂ) a b := by
            rfl
          exact hprod.trans h1ab

/-- The matrix encoder with direct conjugate input, `E(U) = T·S·T` is unitary when `U` is. -/
private lemma quraEncoder_mem_unitaryGroup (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quraEncoder U ∈ Matrix.unitaryGroup (Fin d × (Fin d × Fin d)) ℂ := by
  have hT : qudTensor3 (FT[d]).conjTranspose (FT[d]).conjTranspose 1 ∈
      Matrix.unitaryGroup (Fin d × (Fin d × Fin d)) ℂ := quraT_mem_unitaryGroup d
  have hS : quraSelect (U.map (starRingEnd ℂ)) ∈ Matrix.unitaryGroup (Fin d × (Fin d × Fin d)) ℂ :=
    quraSelect_mem_unitaryGroup U hU
  have hE : quraEncoder U ∈ Matrix.unitaryGroup (Fin d × (Fin d × Fin d)) ℂ := by
    rw [show quraEncoder U =
        qudTensor3 (FT[d]).conjTranspose (FT[d]).conjTranspose 1 *
        quraSelect (U.map (starRingEnd ℂ)) *
        qudTensor3 (FT[d]).conjTranspose (FT[d]).conjTranspose 1 by rfl]
    exact mul_mem (mul_mem hT hS) hT
  rw [Matrix.mem_unitaryGroup_iff]
  exact Matrix.mem_unitaryGroup_iff.mp hE

/-- Certified encoder for a unitary matrix, still using its conjugate directly. -/
def encoderOperator (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix.unitaryGroup (Fin d × (Fin d × Fin d)) ℂ :=
  ⟨quraEncoder (d := d) (U : Matrix (Fin d) (Fin d) ℂ), by
    exact quraEncoder_mem_unitaryGroup (d := d)
      (U : Matrix (Fin d) (Fin d) ℂ) U.property⟩

/-- The certified encoder has exactly the declared conjugate-input formula. -/
@[simp] theorem encoderOperator_coe (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (encoderOperator U : Matrix (Fin d × (Fin d × Fin d)) (Fin d × (Fin d × Fin d)) ℂ) =
      quraEncoder U := rfl

end

end QuantumAlg.UnitaryReversal
