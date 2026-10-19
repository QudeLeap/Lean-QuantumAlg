/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.Matrix.Fourier
public import QuantumAlg.Util.Matrix.TripleTensor

/-!
# Unitary-reversal encoder and decoder identities

These are total matrix formulas. The encoder uses the entrywise conjugate of U
as mathematical input; it does not construct that conjugate from calls to U.
The projection and duality statements follow [CML+24, main.tex:743]
and [CML+24, main.tex:839].
-/

@[expose] public section

namespace QuantumAlg.UnitaryReversal

noncomputable section

open MatrixWeyl

variable {d : ℕ}

local notation "Z[" d "]" => (clockMatrix d : Matrix (Fin d) (Fin d) ℂ)
local notation "X[" d "]" => (shiftMatrix d : Matrix (Fin d) (Fin d) ℂ)
local notation "FT[" d "]" => (quditFT d : Matrix (Fin d) (Fin d) ℂ)



/-- The initial matrix `Λ₀ = |00⟩ ⊗ 1`. -/
def quraLambda0 (d : ℕ) : Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ :=
  Matrix.of fun a s => (if a.1.val = 0 ∧ a.2.1.val = 0 then (1 : ℂ) else 0) *
    (if a.2.2 = s then (1 : ℂ) else 0)

/-- The target matrix `|00⟩ ⊗ U†`. -/
def quraTarget (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ :=
  Matrix.of fun a s => (if a.1.val = 0 ∧ a.2.1.val = 0 then (1 : ℂ) else 0) *
    U.conjTranspose a.2.2 s

/-- The block-select matrix `E_FT(U) = Σ_{j,k} |j,k⟩⟨j,k| ⊗ Z^j X^k U Z^{-j} X^k`. -/
def quraSelect (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × (Fin d × Fin d)) (Fin d × (Fin d × Fin d)) ℂ :=
  Matrix.of fun a b =>
    if a.1 = b.1 ∧ a.2.1 = b.2.1 then
      (Z[d] ^ a.1.val * X[d] ^ a.2.1.val * U *
        (Z[d])⁻¹ ^ a.1.val * X[d] ^ a.2.1.val) a.2.2 b.2.2
    else 0

/-- The matrix encoder with direct conjugate input:
`E(U) = (FT† ⊗ FT† ⊗ I) · E_FT(U*) · (FT† ⊗ FT† ⊗ I)`. -/
def quraEncoder (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × (Fin d × Fin d)) (Fin d × (Fin d × Fin d)) ℂ :=
  let T : Matrix (Fin d × (Fin d × Fin d)) (Fin d × (Fin d × Fin d)) ℂ :=
    qudTensor3 (FT[d]).conjTranspose (FT[d]).conjTranspose 1
  T * quraSelect (U.map (starRingEnd ℂ)) * T

/-- The decoder `D(U) = Σ_{j,k} |j,k⟩⟨j,k| ⊗ X^{-j} Z^{-k} U X^{-j} Z^k`. -/
def quraDecoder (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × (Fin d × Fin d)) (Fin d × (Fin d × Fin d)) ℂ :=
  Matrix.of fun a b =>
    if a.1 = b.1 ∧ a.2.1 = b.2.1 then
      ((X[d])⁻¹ ^ a.1.val * (Z[d])⁻¹ ^ a.2.1.val * U *
        (X[d])⁻¹ ^ a.1.val * Z[d] ^ a.2.1.val) a.2.2 b.2.2
    else 0

/-! ## Encoder projection (Lemma A.2 `lem:preparation` block) -/

/-- `(U.map star).transpose = U†`. -/
lemma map_star_transpose_eq_conjTranspose (U : Matrix (Fin d) (Fin d) ℂ) :
    (U.map (starRingEnd ℂ)).transpose = U.conjTranspose := by
  ext i j
  simp [Matrix.map_apply, Matrix.conjTranspose_apply]

/-- Matrix-level Lemma S2: `Σ_{j,k} Z^j X^k V Z^{-j} X^k = d • Vᵀ`. -/
lemma s2_sum_decompose_mul (hd : d ≠ 0) (V : Matrix (Fin d) (Fin d) ℂ) :
    (∑ j : Fin d, ∑ k : Fin d,
      Z[d] ^ j.val * X[d] ^ k.val * V *
        (Z[d])⁻¹ ^ j.val * X[d] ^ k.val) =
      (d : ℂ) • V.transpose := by
  have hdec := matrix_transpose_decompose V
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hscale : (d : ℂ) • V.transpose = (∑ j : Fin d, ∑ k : Fin d,
      Z[d] ^ j.val * X[d] ^ k.val * V *
        (Z[d])⁻¹ ^ j.val * X[d] ^ k.val) := by
    calc
      (d : ℂ) • V.transpose = (d : ℂ) • ((1 / (d : ℂ)) • (∑ j : Fin d, ∑ k : Fin d,
          Z[d] ^ j.val * X[d] ^ k.val * V *
            (Z[d])⁻¹ ^ j.val * X[d] ^ k.val)) := by rw [hdec]
      _ = ((d : ℂ) * (1 / (d : ℂ))) • (∑ j : Fin d, ∑ k : Fin d,
          Z[d] ^ j.val * X[d] ^ k.val * V *
            (Z[d])⁻¹ ^ j.val * X[d] ^ k.val) := by rw [smul_smul]
      _ = ∑ j : Fin d, ∑ k : Fin d,
          Z[d] ^ j.val * X[d] ^ k.val * V *
            (Z[d])⁻¹ ^ j.val * X[d] ^ k.val := by
            field_simp [hd']
            simp
  exact hscale.symm

/-- Entrywise Lemma S2: `Σ_{j,k} (Z^j X^k V Z^{-j} X^k)_{rs} = d · Vᵀ_{rs}`. -/
lemma s2_sum_entry_of_transpose (hd : d ≠ 0) (V : Matrix (Fin d) (Fin d) ℂ)
    (r s : Fin d) :
    (∑ j : Fin d, ∑ k : Fin d,
      (Z[d] ^ j.val * X[d] ^ k.val * V *
        (Z[d])⁻¹ ^ j.val * X[d] ^ k.val) r s) =
      (d : ℂ) * V.transpose r s := by
  have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M r s) (s2_sum_decompose_mul hd V)
  rw [Matrix.smul_apply, smul_eq_mul] at h
  simp only [Matrix.sum_apply] at h
  exact h

/-- The `(0,0,r)` row of the tensor `T = FT† ⊗ FT† ⊗ I`. -/
lemma qudTensor3_00_row (d : ℕ) [NeZero d] (r : Fin d) (b : Fin d × (Fin d × Fin d)) :
    qudTensor3 (FT[d]).conjTranspose (FT[d]).conjTranspose 1 (0, 0, r) b =
      invSqrtD d * invSqrtD d * (if r = b.2.2 then 1 else 0) := by
  simp [qudTensor3_apply, Matrix.one_apply]

/-- The `(0,0,s)` column of the tensor `T = FT† ⊗ FT† ⊗ I`. -/
lemma qudTensor3_00_col (d : ℕ) [NeZero d] (s : Fin d) (c : Fin d × (Fin d × Fin d)) :
    qudTensor3 (FT[d]).conjTranspose (FT[d]).conjTranspose 1 c (0, 0, s) =
      invSqrtD d * invSqrtD d * (if c.2.2 = s then 1 else 0) := by
  simp [qudTensor3_apply, Matrix.one_apply]

/-- For a fixed `x`, the sum over `c` collapses to the unique `c = (x.1, x.2.1, r)`. -/
lemma quraSelect_inner_row (U : Matrix (Fin d) (Fin d) ℂ)
    (r : Fin d) (x : Fin d × (Fin d × Fin d)) :
    (∑ c : Fin d × (Fin d × Fin d),
        ((invSqrtD d * invSqrtD d) * (if r = c.2.2 then 1 else 0)) *
          quraSelect (U.map (starRingEnd ℂ)) c x) =
      (invSqrtD d * invSqrtD d) *
        (Z[d] ^ x.1.val * X[d] ^ x.2.1.val * (U.map (starRingEnd ℂ)) *
          (Z[d])⁻¹ ^ x.1.val * X[d] ^ x.2.1.val) r x.2.2 := by
  rw [Finset.sum_eq_single (x.1, x.2.1, r)]
  · simp [quraSelect]
  · intro c hc hne
    by_cases h3 : r = c.2.2
    · have hx : ¬(c.1 = x.1 ∧ c.2.1 = x.2.1) := by
        intro h
        apply hne
        cases c with
        | mk c1 c2 =>
          cases c2 with
          | mk c21 c22 =>
            have h' : c1 = x.1 ∧ c21 = x.2.1 := by simpa using h
            simp [h'.1, h'.2, h3]
      simp [quraSelect, hx, h3]
    · simp [quraSelect, h3]
  · intro h
    exact False.elim (h (Finset.mem_univ (x.1, x.2.1, r)))

/-- Collapse the outer sum over the triple index to a double sum over `j1, j2`. -/
lemma quraEncoder_outer_sum (U : Matrix (Fin d) (Fin d) ℂ)
    (r s : Fin d) :
    (∑ x : Fin d × (Fin d × Fin d),
      (invSqrtD d * invSqrtD d) *
        (Z[d] ^ x.1.val * X[d] ^ x.2.1.val * (U.map (starRingEnd ℂ)) *
          (Z[d])⁻¹ ^ x.1.val * X[d] ^ x.2.1.val) r x.2.2 *
        ((invSqrtD d * invSqrtD d) * (if x.2.2 = s then 1 else 0))) =
      (invSqrtD d * invSqrtD d) * (invSqrtD d * invSqrtD d) *
        (∑ j1 : Fin d, ∑ j2 : Fin d,
          (Z[d] ^ j1.val * X[d] ^ j2.val * (U.map (starRingEnd ℂ)) *
            (Z[d])⁻¹ ^ j1.val * X[d] ^ j2.val) r s) := by
  have hrew : (∑ x : Fin d × (Fin d × Fin d),
      (invSqrtD d * invSqrtD d) *
        (Z[d] ^ x.1.val * X[d] ^ x.2.1.val * (U.map (starRingEnd ℂ)) *
          (Z[d])⁻¹ ^ x.1.val * X[d] ^ x.2.1.val) r x.2.2 *
        ((invSqrtD d * invSqrtD d) * (if x.2.2 = s then 1 else 0))) =
      (∑ x : Fin d × (Fin d × Fin d),
      (invSqrtD d * invSqrtD d) * (invSqrtD d * invSqrtD d) *
        ((Z[d] ^ x.1.val * X[d] ^ x.2.1.val * (U.map (starRingEnd ℂ)) *
          (Z[d])⁻¹ ^ x.1.val * X[d] ^ x.2.1.val) r x.2.2 *
          (if x.2.2 = s then 1 else 0))) := by
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hrew]
  have hconst : (∑ x : Fin d × (Fin d × Fin d),
      (invSqrtD d * invSqrtD d) * (invSqrtD d * invSqrtD d) *
        ((Z[d] ^ x.1.val * X[d] ^ x.2.1.val * (U.map (starRingEnd ℂ)) *
          (Z[d])⁻¹ ^ x.1.val * X[d] ^ x.2.1.val) r x.2.2 *
          (if x.2.2 = s then 1 else 0))) =
      (invSqrtD d * invSqrtD d) * (invSqrtD d * invSqrtD d) *
        (∑ x : Fin d × (Fin d × Fin d),
          (Z[d] ^ x.1.val * X[d] ^ x.2.1.val * (U.map (starRingEnd ℂ)) *
            (Z[d])⁻¹ ^ x.1.val * X[d] ^ x.2.1.val) r x.2.2 *
            (if x.2.2 = s then 1 else 0)) := by
    rw [← Finset.mul_sum]
  rw [hconst]
  have hsum2 : (∑ x : Fin d × (Fin d × Fin d),
      (Z[d] ^ x.1.val * X[d] ^ x.2.1.val * (U.map (starRingEnd ℂ)) *
        (Z[d])⁻¹ ^ x.1.val * X[d] ^ x.2.1.val) r x.2.2 *
          (if x.2.2 = s then 1 else 0)) =
      (∑ j1 : Fin d, ∑ j2 : Fin d,
        (Z[d] ^ j1.val * X[d] ^ j2.val * (U.map (starRingEnd ℂ)) *
          (Z[d])⁻¹ ^ j1.val * X[d] ^ j2.val) r s) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j1 hj1
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j2 hj2
    rw [Finset.sum_eq_single s]
    · simp
    · intro j3 hj3 hne
      simp [hne]
    · intro h
      exact False.elim (h (Finset.mem_univ s))
  rw [hsum2]

/-- The `(0,0)` block of the encoder is `(1/d)·U†`; equivalently
`P·E(U)·Λ₀ = (1/d)·|00⟩⊗U†` (Lemma A.2). -/
lemma quraEncoder_00_block [NeZero d] (hd : d ≠ 0) (U : Matrix (Fin d) (Fin d) ℂ)
    (r s : Fin d) :
    quraEncoder U (0, 0, r) (0, 0, s) = (1 / (d : ℂ)) * U.conjTranspose r s := by
  unfold quraEncoder
  simp only [Matrix.mul_apply]
  simp only [qudTensor3_00_row, qudTensor3_00_col]
  simp only [quraSelect_inner_row]
  rw [quraEncoder_outer_sum]
  rw [invSqrtD_mul_self]
  rw [s2_sum_entry_of_transpose hd (U.map (starRingEnd ℂ))]
  rw [map_star_transpose_eq_conjTranspose]
  rw [← Complex.ofReal_natCast]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  field_simp [hd']

lemma fin_add_sub_cancel (a b : Fin d) : (a + b) - b = a := by
  exact add_right_cancel (fin_sub_add_cancel (a + b) b)

/-- `(a + b) - a = b` for `Fin`. -/
lemma fin_add_sub_cancel_right (a b : Fin d) : (a + b) - a = b := by
  rw [add_comm a b]
  exact fin_add_sub_cancel b a

/-- The dual-phase identity: `(ω^{rj})⁻¹ · ω^{jm} · (ω^{j((s+k)%d)})⁻¹ = ω^{j((m+3d-r-s-k)%d)}`. -/
lemma clockRoot_dual_phase (hd : d ≠ 0) (j m r s k : ℕ)
    (hr : r < d) (hs : s < d) (hk : k < d) :
    (clockRoot d ^ (r * j))⁻¹ * clockRoot d ^ (j * m) *
        (clockRoot d ^ (j * ((s + k) % d)))⁻¹ =
      clockRoot d ^ (j * ((m + 3 * d - r - s - k) % d)) := by
  let Y := clockRoot d ^ (r * j) * clockRoot d ^ (j * ((s + k) % d))
  have hne : Y ≠ 0 := by
    dsimp [Y]
    exact mul_ne_zero (pow_ne_zero _ (Complex.exp_ne_zero _))
      (pow_ne_zero _ (Complex.exp_ne_zero _))
  apply mul_left_cancel₀ (a := Y) hne
  have hL : Y * ((clockRoot d ^ (r * j))⁻¹ * clockRoot d ^ (j * m) *
      (clockRoot d ^ (j * ((s + k) % d)))⁻¹) = clockRoot d ^ (j * m) := by
    calc
      Y * ((clockRoot d ^ (r * j))⁻¹ * clockRoot d ^ (j * m) *
          (clockRoot d ^ (j * ((s + k) % d)))⁻¹)
          = (clockRoot d ^ (r * j) * (clockRoot d ^ (r * j))⁻¹) *
              (clockRoot d ^ (j * ((s + k) % d)) *
                (clockRoot d ^ (j * ((s + k) % d)))⁻¹) * clockRoot d ^ (j * m) := by
            ring
      _ = clockRoot d ^ (j * m) := by
          rw [mul_inv_cancel₀, mul_inv_cancel₀, one_mul, one_mul]
          · exact pow_ne_zero _ (Complex.exp_ne_zero _)
          · exact pow_ne_zero _ (Complex.exp_ne_zero _)
  have hR : Y * clockRoot d ^ (j * ((m + 3 * d - r - s - k) % d)) = clockRoot d ^ (j * m) := by
    calc
      Y * clockRoot d ^ (j * ((m + 3 * d - r - s - k) % d))
          = clockRoot d ^ (r * j) * clockRoot d ^ (j * ((s + k) % d)) *
              clockRoot d ^ (j * ((m + 3 * d - r - s - k) % d)) := by rfl
      _ = clockRoot d ^ (r * j + j * ((s + k) % d) + j * ((m + 3 * d - r - s - k) % d)) := by
            rw [pow_add, pow_add]
      _ = clockRoot d ^ ((r * j + j * ((s + k) % d) + j * ((m + 3 * d - r - s - k) % d)) % d) := by
            exact (clockRoot_pow_mod_add hd _).symm
      _ = clockRoot d ^ ((j * m) % d) := by
            congr 1
            have h1 : Nat.ModEq d (j * ((s + k) % d)) (j * (s + k)) := by
              simp [Nat.ModEq, Nat.mul_mod]
            have h2 : Nat.ModEq d (j * ((m + 3 * d - r - s - k) % d))
                (j * (m + 3 * d - r - s - k)) := by
              simp [Nat.ModEq, Nat.mul_mod]
            let e := m + 3 * d - r - s - k
            have hsum' : r * j + j * (s + k) + j * e = j * m + j * (3 * d) := by
              dsimp [e]
              rw [Nat.sub_sub, Nat.sub_sub]
              rw [mul_comm r j, ← Nat.mul_add, ← Nat.mul_add, ← Nat.mul_add]
              congr 1
              have hle : r + s + k ≤ m + 3 * d := by omega
              have hsub : (r + s + k) + (m + 3 * d - (r + s + k)) = m + 3 * d :=
                Nat.add_sub_of_le hle
              simpa [Nat.add_assoc] using hsub
            have hstep1 : r * j + (j * ((s + k) % d) + j * (e % d)) ≡
                r * j + (j * (s + k) + j * (e % d)) [MOD d] := by
              exact (h1.add_right (j * (e % d))).add_left (r * j)
            have hstep2 : r * j + (j * (s + k) + j * (e % d)) ≡
                r * j + (j * (s + k) + j * e) [MOD d] := by
              exact (h2.add_left (j * (s + k))).add_left (r * j)
            have hstep3 : r * j + (j * (s + k) + j * e) ≡ j * m [MOD d] := by
              rw [← Nat.add_assoc, hsum']
              simp [Nat.ModEq, Nat.mul_mod, Nat.add_mod]
            calc
              r * j + j * ((s + k) % d) + j * (e % d)
                  ≡ r * j + (j * ((s + k) % d) + j * (e % d)) [MOD d] := by
                    rw [Nat.add_assoc]
              _ ≡ r * j + (j * (s + k) + j * (e % d)) [MOD d] := hstep1
              _ ≡ r * j + (j * (s + k) + j * e) [MOD d] := hstep2
              _ ≡ j * m [MOD d] := hstep3
      _ = clockRoot d ^ (j * m) := by exact clockRoot_pow_mod_add hd (j * m)
  rw [hL, hR]

/-- Entrywise form of the inverse of a power of the shift matrix: `(X^{-k})_{ab} = 1`
iff `b = a + k`. -/
lemma shiftMatrix_inv_pow_apply_add [NeZero d] (k : Fin d) (a b : Fin d) :
    ((X[d])⁻¹ ^ k.val) a b = if b = a + k then 1 else 0 := by
  have hpow : (X[d])⁻¹ ^ k.val = (X[d] ^ k.val)⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse]
    rw [Ring.inverse_pow]
    rw [← Matrix.nonsing_inv_eq_ringInverse]
  rw [hpow]
  have hmem : X[d] ^ k.val ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    exact pow_mem (shiftMatrix d).property k.val
  have hmul : (X[d] ^ k.val) * (X[d] ^ k.val).conjTranspose = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hmem
  have hmul' : (X[d] ^ k.val).conjTranspose * (X[d] ^ k.val) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hmem
  let u : (Matrix (Fin d) (Fin d) ℂ)ˣ :=
    ⟨X[d] ^ k.val, (X[d] ^ k.val).conjTranspose, hmul, hmul'⟩
  have hinv : (X[d] ^ k.val)⁻¹ = (X[d] ^ k.val).conjTranspose := by
    rw [← Matrix.coe_units_inv u]
    rfl
  rw [hinv]
  simp [Matrix.conjTranspose_apply, shiftMatrix_pow_apply_add]

-- Declaration-scoped exception: simp expands Weyl entries before selecting the shifted index.
set_option linter.flexible false in
/-- Entrywise form of `V = X^{-r} Z^{-t} U X^{-r} Z^t` at `(m, s)`. -/
lemma x_inv_z_inv_uxz_entry [NeZero d] (U : Matrix (Fin d) (Fin d) ℂ)
    (r t m s : Fin d) :
    ((X[d])⁻¹ ^ r.val * (Z[d])⁻¹ ^ t.val * U *
      (X[d])⁻¹ ^ r.val * Z[d] ^ t.val) m s =
      (clockRoot d ^ (t.val * s.val)) * U (m + r) (s - r) *
        (clockRoot d ^ (t.val * ((m.val + r.val) % d)))⁻¹ := by
  simp [Matrix.mul_apply, clockMatrix_inv_pow_apply, shiftMatrix_inv_pow_apply_add,
    clockMatrix_pow_apply, Fin.val_add]
  rw [Finset.sum_eq_single (s - r)]
  · rw [if_pos (fin_sub_add_cancel s r).symm]
    -- phases: (ω^{t((m+r)%d)})⁻¹ · U (m+r) (s−r) · ω^{s·t} with s·t vs t·s
    have hphase1 : (clockRoot d ^ (((m.val + r.val) % d) * t.val))⁻¹ =
        (clockRoot d ^ (t.val * ((m.val + r.val) % d)))⁻¹ := by
      congr 1
      congr 1
      rw [Nat.mul_comm]
    have hphase2 : clockRoot d ^ (s.val * t.val) = clockRoot d ^ (t.val * s.val) := by
      congr 1
      rw [Nat.mul_comm]
    rw [hphase1, hphase2]
    ring
  · intro x hx hne
    rw [if_neg]
    intro hxr
    apply hne
    apply Fin.ext
    have hxr' : x = s - r := by
      rw [hxr]
      exact (fin_add_sub_cancel x r).symm
    exact congrArg Fin.val hxr'
  · intro h
    exact False.elim (h (Finset.mem_univ (s - r)))

/-- Entrywise form of `V†` at `(m, s)`, `V = X^{-r} Z^{-t} U X^{-r} Z^t`. -/
lemma xz_uxz_conjTranspose_entry [NeZero d] (U : Matrix (Fin d) (Fin d) ℂ)
    (r t m s : Fin d) :
    ((X[d])⁻¹ ^ r.val * (Z[d])⁻¹ ^ t.val * U *
      (X[d])⁻¹ ^ r.val * Z[d] ^ t.val).conjTranspose m s =
      (clockRoot d ^ (t.val * ((s.val + r.val) % d))) * star (U (s + r) (m - r)) *
        (clockRoot d ^ (t.val * m.val))⁻¹ := by
  rw [Matrix.conjTranspose_apply]
  rw [x_inv_z_inv_uxz_entry U r t s m]
  -- V_{s,m} = ω^{tm} · U (s+r) (m-r) · (ω^{t((s+r)%d)})⁻¹
  -- star: (ω^{tm})⁻¹ · star(U) · ω^{t((s+r)%d)}
  have hstar1 : star (clockRoot d ^ (t.val * m.val)) =
      (clockRoot d ^ (t.val * m.val))⁻¹ := by
    rw [star_pow]
    rw [star_clockRoot (NeZero.ne d)]
    exact inv_pow _ _
  have hstar2 : star ((clockRoot d ^ (t.val * ((s.val + r.val) % d)))⁻¹) =
      clockRoot d ^ (t.val * ((s.val + r.val) % d)) := by
    have hx : star (clockRoot d ^ (t.val * ((s.val + r.val) % d))) =
        (clockRoot d ^ (t.val * ((s.val + r.val) % d)))⁻¹ := by
      rw [star_pow]
      rw [star_clockRoot (NeZero.ne d)]
      exact inv_pow _ _
    rw [← hx]
    simp
  simp only [star_mul]
  rw [hstar1, hstar2]
  ring

/-- The unique `k` with `(m + 3d - r - s - k) % d = 0`. -/
def dualK0 (d : ℕ) [NeZero d] (m r s : Fin d) : Fin d :=
  ⟨(m.val + 3 * d - r.val - s.val) % d,
    Nat.mod_lt (m.val + 3 * d - r.val - s.val) (Nat.pos_of_ne_zero (NeZero.ne d))⟩

/-- `k₀ + r + s = m` modulo `d`. -/
lemma dual_k0_add_r_s [NeZero d] (m r s : Fin d) :
    dualK0 d m r s + r + s = m := by
  apply Fin.ext
  rw [Fin.val_add, Fin.val_add]
  have hnorm : (((dualK0 d m r s).val + r.val) % d + s.val) % d =
      ((dualK0 d m r s).val + r.val + s.val) % d := by
    have h1 : Nat.ModEq d (((dualK0 d m r s).val + r.val) % d + s.val)
        ((dualK0 d m r s).val + r.val + s.val) := by
      have hm : Nat.ModEq d (((dualK0 d m r s).val + r.val) % d)
          ((dualK0 d m r s).val + r.val) := by
        exact Nat.mod_mod ((dualK0 d m r s).val + r.val) d
      simpa [Nat.add_assoc] using hm.add_right s.val
    exact h1
  rw [hnorm]
  change (((m.val + 3 * d - r.val - s.val) % d) + r.val + s.val) % d = m.val
  have hA : Nat.ModEq d ((m.val + 3 * d - r.val - s.val) % d) (m.val + 3 * d - r.val - s.val) := by
    exact Nat.mod_mod (m.val + 3 * d - r.val - s.val) d
  have hsum : Nat.ModEq d (((m.val + 3 * d - r.val - s.val) % d) + r.val + s.val)
      (m.val + 3 * d - r.val - s.val + r.val + s.val) := by
    simpa [Nat.add_assoc] using hA.add_right (r.val + s.val)
  have hge : r.val + s.val ≤ m.val + 3 * d := by omega
  have hred : m.val + 3 * d - r.val - s.val + r.val + s.val = m.val + 3 * d := by
    rw [Nat.sub_sub]
    rw [Nat.add_assoc]
    exact Nat.sub_add_cancel hge
  have hfinal : Nat.ModEq d (((m.val + 3 * d - r.val - s.val) % d) + r.val + s.val) m.val := by
    calc
      ((m.val + 3 * d - r.val - s.val) % d) + r.val + s.val
          ≡ m.val + 3 * d - r.val - s.val + r.val + s.val [MOD d] := hsum
      _ ≡ m.val + 3 * d [MOD d] := by rw [hred]
      _ ≡ m.val [MOD d] := by
            have hm : m.val % d = m.val := Nat.mod_eq_of_lt m.isLt
            simp [Nat.ModEq, Nat.add_mod, hm]
  have hm : m.val % d = m.val := Nat.mod_eq_of_lt m.isLt
  rw [hfinal, hm]

/-- `m - k₀ = s + r`. -/
lemma dual_k0_sub [NeZero d] (m r s : Fin d) : m - dualK0 d m r s = s + r := by
  have h := dual_k0_add_r_s m r s
  calc
    m - dualK0 d m r s = (dualK0 d m r s + r + s) - dualK0 d m r s := by rw [h]
    _ = r + s := by
      simp [add_assoc]
    _ = s + r := by exact add_comm r s

/-- `s + k₀ = m - r`. -/
lemma dual_k0_add [NeZero d] (m r s : Fin d) : s + dualK0 d m r s = m - r := by
  have h := dual_k0_add_r_s m r s
  exact (calc
    m - r = (dualK0 d m r s + r + s) - r := by rw [h]
    _ = dualK0 d m r s + s := by
      rw [show dualK0 d m r s + r + s = (dualK0 d m r s + s) + r by
        rw [add_assoc, add_comm r s, ← add_assoc]]
      exact fin_add_sub_cancel (dualK0 d m r s + s) r
    _ = s + dualK0 d m r s := by exact add_comm (dualK0 d m r s) s).symm

/-- The phase identity `(ω^{t k₀})⁻¹ = ω^{t((s+r)%d)} · (ω^{t m})⁻¹`. -/
lemma dual_k0_phase [NeZero d] (hd : d ≠ 0) (t m r s : Fin d) :
    (clockRoot d ^ (t.val * (dualK0 d m r s).val))⁻¹ =
      clockRoot d ^ (t.val * ((s.val + r.val) % d)) * (clockRoot d ^ (t.val * m.val))⁻¹ := by
  apply mul_left_cancel₀
    (a := clockRoot d ^ (t.val * (dualK0 d m r s).val) * clockRoot d ^ (t.val * m.val))
  · dsimp
    exact mul_ne_zero (pow_ne_zero _ (Complex.exp_ne_zero _))
      (pow_ne_zero _ (Complex.exp_ne_zero _))
  · have hL : (clockRoot d ^ (t.val * (dualK0 d m r s).val) * clockRoot d ^ (t.val * m.val)) *
        (clockRoot d ^ (t.val * (dualK0 d m r s).val))⁻¹ = clockRoot d ^ (t.val * m.val) := by
      calc
        (clockRoot d ^ (t.val * (dualK0 d m r s).val) * clockRoot d ^ (t.val * m.val)) *
            (clockRoot d ^ (t.val * (dualK0 d m r s).val))⁻¹
            = clockRoot d ^ (t.val * m.val) *
                (clockRoot d ^ (t.val * (dualK0 d m r s).val) *
                  (clockRoot d ^ (t.val * (dualK0 d m r s).val))⁻¹) := by ring
        _ = clockRoot d ^ (t.val * m.val) := by
            have hcancel : clockRoot d ^ (t.val * (dualK0 d m r s).val) *
                (clockRoot d ^ (t.val * (dualK0 d m r s).val))⁻¹ = 1 :=
              mul_inv_cancel₀ (pow_ne_zero _ (Complex.exp_ne_zero _))
            rw [hcancel]
            rw [mul_one]
    have hR : (clockRoot d ^ (t.val * (dualK0 d m r s).val) * clockRoot d ^ (t.val * m.val)) *
        (clockRoot d ^ (t.val * ((s.val + r.val) % d)) * (clockRoot d ^ (t.val * m.val))⁻¹) =
        clockRoot d ^ (t.val * m.val) := by
      calc
        (clockRoot d ^ (t.val * (dualK0 d m r s).val) * clockRoot d ^ (t.val * m.val)) *
            (clockRoot d ^ (t.val * ((s.val + r.val) % d)) *
              (clockRoot d ^ (t.val * m.val))⁻¹)
            = clockRoot d ^ (t.val * (dualK0 d m r s).val) *
                (clockRoot d ^ (t.val * m.val) * (clockRoot d ^ (t.val * m.val))⁻¹) *
                clockRoot d ^ (t.val * ((s.val + r.val) % d)) := by ring
        _ = clockRoot d ^ (t.val * (dualK0 d m r s).val) *
              clockRoot d ^ (t.val * ((s.val + r.val) % d)) := by
              have hcancel : clockRoot d ^ (t.val * m.val) *
                  (clockRoot d ^ (t.val * m.val))⁻¹ = 1 :=
                mul_inv_cancel₀ (pow_ne_zero _ (Complex.exp_ne_zero _))
              rw [hcancel, mul_one]
        _ = clockRoot d ^ (t.val * ((dualK0 d m r s).val + ((s.val + r.val) % d))) := by
              rw [← pow_add]
              congr 1
              ring
        _ = clockRoot d ^ ((t.val * ((dualK0 d m r s).val + ((s.val + r.val) % d))) % d) := by
              exact (clockRoot_pow_mod_add hd _).symm
        _ = clockRoot d ^ ((t.val * m.val) % d) := by
              congr 1
              have hk : dualK0 d m r s + r + s = m := dual_k0_add_r_s m r s
              have hkv : ((dualK0 d m r s).val + r.val + s.val) % d = m.val := by
                rw [← congrArg Fin.val hk]
                simp [Fin.val_add]
              have hkm : Nat.ModEq d ((dualK0 d m r s).val + ((s.val + r.val) % d))
                  ((dualK0 d m r s).val + r.val + s.val) := by
                have hm : Nat.ModEq d ((s.val + r.val) % d) (r.val + s.val) := by
                  simp [Nat.ModEq, Nat.add_comm]
                simpa [Nat.add_assoc] using hm.add_left (dualK0 d m r s).val
              have hkm' : Nat.ModEq d ((dualK0 d m r s).val + ((s.val + r.val) % d)) m.val := by
                have hmv : Nat.ModEq d ((dualK0 d m r s).val + r.val + s.val) m.val := by
                  simpa [Nat.ModEq, Nat.mod_eq_of_lt m.isLt] using hkv
                simpa [Nat.add_assoc] using hkm.trans hmv
              have hmul : Nat.ModEq d (t.val * ((dualK0 d m r s).val + ((s.val + r.val) % d)))
                  (t.val * m.val) := by
                exact hkm'.mul_left t.val
              exact hmul
        _ = clockRoot d ^ (t.val * m.val) := by exact clockRoot_pow_mod_add hd (t.val * m.val)
    rw [hL, hR]

/-- `(a - a % d) % d = 0`. -/
lemma sub_mod_mod (a d : ℕ) : (a - a % d) % d = 0 := by
  have h := Nat.div_add_mod a d
  have h' : a - a % d = a / d * d := by
    have h1 := Nat.sub_add_cancel (Nat.mod_le a d)
    exact add_right_cancel (h1.trans (by simpa [Nat.mul_comm] using h.symm))
  rw [h']
  simp

/-- `e_{k₀} = 0`: the chosen representative kills the phase. -/
lemma dual_k0_e_zero [NeZero d] (m r s : Fin d) :
    (m.val + 3 * d - r.val - s.val - (dualK0 d m r s).val) % d = 0 := by
  have hA : m.val + 3 * d - r.val - s.val - (dualK0 d m r s).val =
      (m.val + 3 * d - r.val - s.val) - (m.val + 3 * d - r.val - s.val) % d := by
    rw [show (dualK0 d m r s).val = (m.val + 3 * d - r.val - s.val) % d by rfl]
  rw [hA]
  exact sub_mod_mod (m.val + 3 * d - r.val - s.val) d

/-- If `e_k = 0` then `k = k₀`. -/
lemma dual_k0_e_eq [NeZero d] (m r s k : Fin d)
    (hk : (m.val + 3 * d - r.val - s.val - k.val) % d = 0) :
    k = dualK0 d m r s := by
  apply Fin.ext
  -- (A - k) % d = 0 → A ≡ k (mod d) → k.val = A % d since k.val < d
  have hmod0 : Nat.ModEq d (m.val + 3 * d - r.val - s.val - k.val) 0 := by
    simpa [Nat.ModEq] using hk
  have hge : k.val ≤ m.val + 3 * d - r.val - s.val := by omega
  have hmod : Nat.ModEq d (m.val + 3 * d - r.val - s.val) k.val := by
    -- (A - k) + k = A
    have hsum : (m.val + 3 * d - r.val - s.val - k.val) + k.val =
        m.val + 3 * d - r.val - s.val := Nat.sub_add_cancel hge
    have h' : Nat.ModEq d ((m.val + 3 * d - r.val - s.val - k.val) + k.val) k.val := by
      simpa using hmod0.add_right k.val
    simpa [hsum] using h'
  have hmod' : Nat.ModEq d (m.val + 3 * d - r.val - s.val)
      ((m.val + 3 * d - r.val - s.val) % d) := by
    exact (Nat.mod_mod (m.val + 3 * d - r.val - s.val) d).symm
  have hk' : k.val % d = (m.val + 3 * d - r.val - s.val) % d := by
    exact hmod.symm
  -- k.val < d so k.val % d = k.val
  have hk'' : k.val = (m.val + 3 * d - r.val - s.val) % d := by
    rw [Nat.mod_eq_of_lt k.isLt] at hk'
    exact hk'
  simpa [dualK0] using hk''

/-- The `|++⟩ ⊗ I` state matrix. -/
def qudPlusState (d : ℕ) : Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ :=
  Matrix.of fun a s => (invSqrtD d * invSqrtD d) * (if a.2.2 = s then 1 else 0)

@[simp]
lemma qudPlusState_apply (d : ℕ) (a : Fin d × (Fin d × Fin d)) (s : Fin d) :
    qudPlusState d a s = (invSqrtD d * invSqrtD d) * (if a.2.2 = s then 1 else 0) := by
  rfl

/-- Core duality identity: `Σ_{j,k} ω^{-rj-tk} (Z^j X^k U* Z^{-j} X^k)_{m,s} = d·V†_{m,s}`
with `V = X^{-r} Z^{-t} U X^{-r} Z^t`. -/
lemma dual_sum_entry [NeZero d] (hd : d ≠ 0) (U : Matrix (Fin d) (Fin d) ℂ)
    (r t m s : Fin d) :
    (∑ j : Fin d, ∑ k : Fin d,
      (clockRoot d ^ (r.val * j.val))⁻¹ * (clockRoot d ^ (t.val * k.val))⁻¹ *
        (Z[d] ^ j.val * X[d] ^ k.val * (U.map (starRingEnd ℂ)) *
          (Z[d])⁻¹ ^ j.val * X[d] ^ k.val) m s) =
      (d : ℂ) * (((X[d])⁻¹ ^ r.val * (Z[d])⁻¹ ^ t.val * U *
        (X[d])⁻¹ ^ r.val * Z[d] ^ t.val).conjTranspose m s) := by
  have hint := zx_uzx_entry (U.map (starRingEnd ℂ)) m s
  have hsum1 : (∑ j : Fin d, ∑ k : Fin d,
      (clockRoot d ^ (r.val * j.val))⁻¹ * (clockRoot d ^ (t.val * k.val))⁻¹ *
        (Z[d] ^ j.val * X[d] ^ k.val * (U.map (starRingEnd ℂ)) *
          (Z[d])⁻¹ ^ j.val * X[d] ^ k.val) m s) =
      (∑ j : Fin d, ∑ k : Fin d,
      (clockRoot d ^ (t.val * k.val))⁻¹ * (U.map (starRingEnd ℂ)) (m - k) (s + k) *
        clockRoot d ^ (j.val * ((m.val + 3 * d - r.val - s.val - k.val) % d))) := by
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    rw [hint j k]
    have hp := clockRoot_dual_phase hd j.val m.val r.val s.val k.val r.isLt s.isLt k.isLt
    calc
      (clockRoot d ^ (r.val * j.val))⁻¹ * (clockRoot d ^ (t.val * k.val))⁻¹ *
          (clockRoot d ^ (j.val * m.val) * (U.map (starRingEnd ℂ)) (m - k) (s + k) *
            (clockRoot d ^ (j.val * ((s.val + k.val) % d)))⁻¹)
          = (clockRoot d ^ (t.val * k.val))⁻¹ * (U.map (starRingEnd ℂ)) (m - k) (s + k) *
              ((clockRoot d ^ (r.val * j.val))⁻¹ * (clockRoot d ^ (j.val * m.val)) *
                (clockRoot d ^ (j.val * ((s.val + k.val) % d)))⁻¹) := by ring
      _ = (clockRoot d ^ (t.val * k.val))⁻¹ * (U.map (starRingEnd ℂ)) (m - k) (s + k) *
            clockRoot d ^ (j.val * ((m.val + 3 * d - r.val - s.val - k.val) % d)) := by
            rw [hp]
  rw [hsum1]
  rw [Finset.sum_comm]
  have hsum2 : (∑ k : Fin d, ∑ j : Fin d,
      (clockRoot d ^ (t.val * k.val))⁻¹ * (U.map (starRingEnd ℂ)) (m - k) (s + k) *
        clockRoot d ^ (j.val * ((m.val + 3 * d - r.val - s.val - k.val) % d))) =
      (∑ k : Fin d, ((clockRoot d ^ (t.val * k.val))⁻¹ * (U.map (starRingEnd ℂ)) (m - k) (s + k)) *
        (if ((m.val + 3 * d - r.val - s.val - k.val) % d) % d = 0 then (d : ℂ) else 0)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Finset.mul_sum]
    rw [sum_clockRoot_pow hd ((m.val + 3 * d - r.val - s.val - k.val) % d)]
  rw [hsum2]
  let k0 := dualK0 d m r s
  have hsum3 : (∑ k : Fin d,
      ((clockRoot d ^ (t.val * k.val))⁻¹ * (U.map (starRingEnd ℂ)) (m - k) (s + k)) *
        (if ((m.val + 3 * d - r.val - s.val - k.val) % d) % d = 0 then (d : ℂ) else 0)) =
      (d : ℂ) * ((clockRoot d ^ (t.val * (dualK0 d m r s).val))⁻¹ *
        (U.map (starRingEnd ℂ)) (m - dualK0 d m r s) (s + dualK0 d m r s)) := by
    rw [Finset.sum_eq_single (dualK0 d m r s)]
    · have hz := dual_k0_e_zero m r s
      rw [if_pos (by simpa using hz)]
      ring
    · intro k hk hne
      have hz : (m.val + 3 * d - r.val - s.val - k.val) % d ≠ 0 := by
        intro h
        apply hne
        exact dual_k0_e_eq m r s k h
      rw [if_neg (by simpa using hz)]
      ring
    · intro h
      exact False.elim (h (Finset.mem_univ (dualK0 d m r s)))
  rw [hsum3]
  rw [xz_uxz_conjTranspose_entry U r t m s]
  rw [Matrix.map_apply]
  rw [dual_k0_sub m r s, dual_k0_add m r s]
  rw [dual_k0_phase hd t m r s]
  rw [← inv_pow]
  have hsr : (starRingEnd ℂ) (U (s + r) (m - r)) = star (U (s + r) (m - r)) := by rfl
  rw [hsr]
  ring

/-- `(FT†)_{rj} = (1/√d) · (ω^{rj})⁻¹`. -/
lemma quditFT_conjTranspose_entry [NeZero d] (r j : Fin d) :
    (FT[d]).conjTranspose r j = invSqrtD d * (clockRoot d ^ (r.val * j.val))⁻¹ := by
  rw [Matrix.conjTranspose_apply, quditFT_entry]
  rw [star_mul']
  rw [star_invSqrtD]
  rw [star_pow]
  rw [star_clockRoot (NeZero.ne d)]
  rw [inv_pow]
  congr 2
  congr 1
  rw [Nat.mul_comm]

/-- `(FT† ⊗ FT† ⊗ I) · Λ₀ = |++⟩ ⊗ I`. -/
lemma T_mul_lambda0 [NeZero d] :
    qudTensor3 (FT[d]).conjTranspose (FT[d]).conjTranspose 1 * quraLambda0 d =
      qudPlusState d := by
  ext a s
  simp only [Matrix.mul_apply, quraLambda0, qudPlusState_apply]
  -- collapse the sum over b to the unique b = (0, 0, s) (when a.2.2 = s)
  rw [Finset.sum_eq_single (0, 0, s)]
  · -- main term
    simp [Matrix.one_apply]
  · intro b hb hne
    by_cases h1 : b.1.val = 0 ∧ b.2.1.val = 0
    · by_cases h3 : b.2.2 = s
      · -- b ≠ (0,0,s) but b.1 = 0 ∧ b.2.1 = 0 ∧ b.2.2 = s → contradiction
        apply False.elim
        apply hne
        cases b with
        | mk b1 b2 =>
          cases b2 with
          | mk b21 b22 =>
            have hb1 : b1 = 0 := Fin.ext h1.1
            have hb21 : b21 = 0 := Fin.ext h1.2
            have hb22 : b22 = s := by simpa using h3
            simp [hb1, hb21, hb22]
      · simp [h3]
    · have hnot : ¬(b.1 = 0 ∧ b.2.1 = 0) := by
        intro h
        apply h1
        exact ⟨congrArg Fin.val h.1, congrArg Fin.val h.2⟩
      simp [hnot]
  · intro h
    exact False.elim (h (Finset.mem_univ (0, 0, s)))

/-- `(quraSelect (U*) · (|++⟩ ⊗ I))` collapses to the block entry. -/
lemma encoder_lambda0_entry [NeZero d] (U : Matrix (Fin d) (Fin d) ℂ)
    (a : Fin d × (Fin d × Fin d)) (s : Fin d) :
    (quraEncoder U * quraLambda0 d) a s =
      (invSqrtD d * invSqrtD d) * (invSqrtD d * invSqrtD d) *
        (∑ j : Fin d, ∑ k : Fin d,
          (clockRoot d ^ (a.1.val * j.val))⁻¹ * (clockRoot d ^ (a.2.1.val * k.val))⁻¹ *
            (Z[d] ^ j.val * X[d] ^ k.val * (U.map (starRingEnd ℂ)) *
              (Z[d])⁻¹ ^ j.val * X[d] ^ k.val) a.2.2 s) := by
  have hin : ∀ b : Fin d × (Fin d × Fin d),
      (qudTensor3 (FT[d]).conjTranspose (FT[d]).conjTranspose 1 *
          quraSelect (U.map (starRingEnd ℂ))) a b =
      (FT[d]).conjTranspose a.1 b.1 * (FT[d]).conjTranspose a.2.1 b.2.1 *
        (Z[d] ^ b.1.val * X[d] ^ b.2.1.val * (U.map (starRingEnd ℂ)) *
          (Z[d])⁻¹ ^ b.1.val * X[d] ^ b.2.1.val) a.2.2 b.2.2 := by
    intro b
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (b.1, b.2.1, a.2.2)]
    · simp [quraSelect, qudTensor3_apply]
    · intro c hc hne
      by_cases h3 : c.2.2 = a.2.2
      · have hx : ¬(c.1 = b.1 ∧ c.2.1 = b.2.1) := by
          intro h
          apply hne
          cases c with
          | mk c1 c2 =>
            cases c2 with
            | mk c21 c22 =>
              have h' : c1 = b.1 ∧ c21 = b.2.1 := h
              have h3' : c22 = a.2.2 := by simpa using h3
              simp [h'.1, h'.2, h3']
        simp [quraSelect, hx]
      · have h3' : ¬(a.2.2 = c.2.2) := fun h => h3 h.symm
        simp [qudTensor3_apply, h3']
    · intro h
      exact False.elim (h (Finset.mem_univ (b.1, b.2.1, a.2.2)))
  calc
    (quraEncoder U * quraLambda0 d) a s = (quraEncoder U * quraLambda0 d) a s := rfl
    _ = (qudTensor3 (FT[d]).conjTranspose (FT[d]).conjTranspose 1 *
          quraSelect (U.map (starRingEnd ℂ)) * qudPlusState d) a s := by
          unfold quraEncoder
          rw [Matrix.mul_assoc]
          rw [T_mul_lambda0]
    _ = (∑ b : Fin d × (Fin d × Fin d),
          (qudTensor3 (FT[d]).conjTranspose (FT[d]).conjTranspose 1 *
            quraSelect (U.map (starRingEnd ℂ))) a b * qudPlusState d b s) := by
          simp only [Matrix.mul_apply]
    _ = (∑ b : Fin d × (Fin d × Fin d),
          ((FT[d]).conjTranspose a.1 b.1 * (FT[d]).conjTranspose a.2.1 b.2.1 *
            (Z[d] ^ b.1.val * X[d] ^ b.2.1.val * (U.map (starRingEnd ℂ)) *
              (Z[d])⁻¹ ^ b.1.val * X[d] ^ b.2.1.val) a.2.2 b.2.2) *
            qudPlusState d b s) := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [hin b]
    _ = (invSqrtD d * invSqrtD d) * (invSqrtD d * invSqrtD d) *
          (∑ j : Fin d, ∑ k : Fin d,
            (clockRoot d ^ (a.1.val * j.val))⁻¹ * (clockRoot d ^ (a.2.1.val * k.val))⁻¹ *
              (Z[d] ^ j.val * X[d] ^ k.val * (U.map (starRingEnd ℂ)) *
                (Z[d])⁻¹ ^ j.val * X[d] ^ k.val) a.2.2 s) := by
          simp only [quditFT_conjTranspose_entry, qudPlusState_apply]
          have hrew : (∑ b : Fin d × (Fin d × Fin d),
              (invSqrtD d * (clockRoot d ^ (a.1.val * b.1.val))⁻¹) *
                (invSqrtD d * (clockRoot d ^ (a.2.1.val * b.2.1.val))⁻¹) *
                (Z[d] ^ b.1.val * X[d] ^ b.2.1.val * (U.map (starRingEnd ℂ)) *
                  (Z[d])⁻¹ ^ b.1.val * X[d] ^ b.2.1.val) a.2.2 b.2.2 *
                ((invSqrtD d * invSqrtD d) * (if b.2.2 = s then 1 else 0))) =
              (∑ b : Fin d × (Fin d × Fin d),
              (invSqrtD d * invSqrtD d) * (invSqrtD d * invSqrtD d) *
                ((clockRoot d ^ (a.1.val * b.1.val))⁻¹ * (clockRoot d ^ (a.2.1.val * b.2.1.val))⁻¹ *
                  (Z[d] ^ b.1.val * X[d] ^ b.2.1.val * (U.map (starRingEnd ℂ)) *
                    (Z[d])⁻¹ ^ b.1.val * X[d] ^ b.2.1.val) a.2.2 b.2.2 *
                  (if b.2.2 = s then 1 else 0))) := by
            apply Finset.sum_congr rfl
            intro b hb
            ring
          rw [hrew]
          rw [← Finset.mul_sum]
          rw [Fintype.sum_prod_type]
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_eq_single s]
          · simp
          · intro x hx hne
            simp [hne]
          · intro h
            exact False.elim (h (Finset.mem_univ s))

/-- The decoder-conjugate applied to `|++⟩ ⊗ I`, entrywise. -/
lemma decoder_conjTranspose_mul_plus_entry (U : Matrix (Fin d) (Fin d) ℂ)
    (a : Fin d × (Fin d × Fin d)) (s : Fin d) :
    ((quraDecoder U).conjTranspose * qudPlusState d) a s =
      (invSqrtD d * invSqrtD d) *
        (((X[d])⁻¹ ^ a.1.val * (Z[d])⁻¹ ^ a.2.1.val * U *
          (X[d])⁻¹ ^ a.1.val * Z[d] ^ a.2.1.val).conjTranspose a.2.2 s) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (a.1, a.2.1, s)]
  · rw [Matrix.conjTranspose_apply]
    have hD : quraDecoder U (a.1, a.2.1, s) a =
        ((X[d])⁻¹ ^ a.1.val * (Z[d])⁻¹ ^ a.2.1.val * U *
          (X[d])⁻¹ ^ a.1.val * Z[d] ^ a.2.1.val) s a.2.2 := by
      simp [quraDecoder]
    rw [hD]
    rw [← Matrix.conjTranspose_apply]
    simp [qudPlusState_apply]
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
      simp [quraDecoder, hx, h3]
    · simp [quraDecoder, h3]
  · intro h
    exact False.elim (h (Finset.mem_univ (a.1, a.2.1, s)))

/-- Duality relation (Corollary `cor:O1`): `E(U)·Λ₀ = D(U)†·(|++⟩ ⊗ I)`. -/
lemma qura_duality [NeZero d] (hd : d ≠ 0) (U : Matrix (Fin d) (Fin d) ℂ) :
    quraEncoder U * quraLambda0 d = (quraDecoder U).conjTranspose * qudPlusState d := by
  ext a s
  rw [encoder_lambda0_entry U a s]
  rw [decoder_conjTranspose_mul_plus_entry U a s]
  rw [invSqrtD_mul_self]
  rw [dual_sum_entry hd U a.1 a.2.1 a.2.2 s]
  rw [← Complex.ofReal_natCast]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  field_simp [hd']

lemma D_dag_lambda0 [NeZero d] (U : Matrix (Fin d) (Fin d) ℂ) :
    (quraDecoder U).conjTranspose * quraLambda0 d = quraTarget d U := by
  ext a s
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (0, 0, s)]
  · rw [Matrix.conjTranspose_apply]
    have hD : quraDecoder U (0, 0, s) a =
        (if 0 = a.1 ∧ 0 = a.2.1 then U s a.2.2 else 0) := by
      simp [quraDecoder]
    have hL : quraLambda0 d (0, 0, s) s = 1 := by
      simp [quraLambda0]
    rw [hD, hL]
    have hstar : star (if 0 = a.1 ∧ 0 = a.2.1 then U s a.2.2 else 0) =
        if a.1 = 0 ∧ a.2.1 = 0 then star (U s a.2.2) else 0 := by
      by_cases h : 0 = a.1 ∧ 0 = a.2.1
      · have h' : a.1 = 0 ∧ a.2.1 = 0 := ⟨h.1.symm, h.2.symm⟩
        rw [if_pos h, if_pos h']
      · have h' : ¬(a.1 = 0 ∧ a.2.1 = 0) := by
          intro hh
          apply h
          exact ⟨hh.1.symm, hh.2.symm⟩
        rw [if_neg h, if_neg h']
        simp
    rw [hstar]
    rw [← Matrix.conjTranspose_apply]
    by_cases h0 : a.1 = 0 ∧ a.2.1 = 0
    · have h0v : a.1.val = 0 ∧ a.2.1.val = 0 := ⟨congrArg Fin.val h0.1, congrArg Fin.val h0.2⟩
      simp [quraTarget, h0]
    · have h0v : ¬(a.1.val = 0 ∧ a.2.1.val = 0) := by
        intro hh
        apply h0
        exact ⟨Fin.ext hh.1, Fin.ext hh.2⟩
      simp [quraTarget, h0]
  · intro c hc hne
    by_cases h0 : c.1.val = 0 ∧ c.2.1.val = 0
    · by_cases h3 : c.2.2 = s
      · -- c ≠ (0,0,s) but all components match → contradiction
        apply False.elim
        apply hne
        cases c with
        | mk c1 c2 =>
          cases c2 with
          | mk c21 c22 =>
            have hc1 : c1 = 0 := Fin.ext h0.1
            have hc21 : c21 = 0 := Fin.ext h0.2
            have hc22 : c22 = s := h3
            simp [hc1, hc21, hc22]
      · -- c.2.2 ≠ s → Λ₀ gives 0
        simp [quraLambda0, h3]
    · -- c.1 ≠ 0 ∨ c.2.1 ≠ 0 → Λ₀ gives 0
      have hnot : ¬(c.1 = 0 ∧ c.2.1 = 0) := by
        intro h
        apply h0
        exact ⟨congrArg Fin.val h.1, congrArg Fin.val h.2⟩
      simp [quraLambda0, hnot]
  · intro h
    exact False.elim (h (Finset.mem_univ (0, 0, s)))

lemma decoder_block_unitary' (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (j k : Fin d) :
    (X[d])⁻¹ ^ j.val * (Z[d])⁻¹ ^ k.val * U *
      (X[d])⁻¹ ^ j.val * Z[d] ^ k.val *
      ((X[d])⁻¹ ^ j.val * (Z[d])⁻¹ ^ k.val * U *
        (X[d])⁻¹ ^ j.val * Z[d] ^ k.val).conjTranspose = 1 := by
  set M : Matrix (Fin d) (Fin d) ℂ :=
    (X[d])⁻¹ ^ j.val * (Z[d])⁻¹ ^ k.val * U *
      (X[d])⁻¹ ^ j.val * Z[d] ^ k.val with hMdef
  have hM : M ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    rw [hMdef]
    exact mul_mem (mul_mem (mul_mem (mul_mem (shiftMatrix_inv_pow_mem_unitaryGroup j)
      (clockMatrix_inv_pow_mem_unitaryGroup k)) hU)
      (shiftMatrix_inv_pow_mem_unitaryGroup j))
      (pow_mem (clockMatrix d).property k.val)
  have h' : M * star M = 1 := Matrix.mem_unitaryGroup_iff.mp hM
  rw [Matrix.star_eq_conjTranspose] at h'
  exact h'

-- Declaration-scoped exception: simp exposes decoder blocks before finite-sum extraction.
set_option linter.flexible false in
/-- The decoder matrix `D(U)` is unitary when `U` is. -/
private lemma quraDecoder_mem_unitaryGroup (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quraDecoder U ∈ Matrix.unitaryGroup (Fin d × (Fin d × Fin d)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  rw [Matrix.mul_apply]
  by_cases hb : a.1 = b.1 ∧ a.2.1 = b.2.1
  · rcases hb with ⟨hr, ht⟩
    have hsum : (∑ c : Fin d × (Fin d × Fin d),
        quraDecoder U a c * star (quraDecoder U) c b) =
        (if a.2.2 = b.2.2 then 1 else 0) := by
      simp [quraDecoder]
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single a.1]
      · rw [Fintype.sum_prod_type]
        rw [Finset.sum_eq_single a.2.1]
        · -- remaining sum over x: Σ x, M_{a.2.2,x}·star(M_{b.2.2,x}) = δ
          simp [hr, ht]
          have hmm : (∑ x : Fin d,
              ((X[d])⁻¹ ^ b.1.val * (Z[d])⁻¹ ^ b.2.1.val * U *
                (X[d])⁻¹ ^ b.1.val * Z[d] ^ b.2.1.val) a.2.2 x *
                starRingEnd ℂ (((X[d])⁻¹ ^ b.1.val * (Z[d])⁻¹ ^ b.2.1.val * U *
                  (X[d])⁻¹ ^ b.1.val * Z[d] ^ b.2.1.val) b.2.2 x)) =
              ((X[d])⁻¹ ^ b.1.val * (Z[d])⁻¹ ^ b.2.1.val * U *
                (X[d])⁻¹ ^ b.1.val * Z[d] ^ b.2.1.val *
                ((X[d])⁻¹ ^ b.1.val * (Z[d])⁻¹ ^ b.2.1.val * U *
                  (X[d])⁻¹ ^ b.1.val * Z[d] ^ b.2.1.val).conjTranspose) a.2.2
                  b.2.2 := by
            rw [Matrix.mul_apply]
            simp only [Matrix.conjTranspose_apply]
            rfl
          rw [hmm]
          have hblock := decoder_block_unitary' U hU b.1 b.2.1
          rw [hblock]
          simp [Matrix.one_apply]
        · intro p hp hne
          -- p ≠ a.2.1 → the condition fails → 0
          apply Finset.sum_eq_zero
          intro y hy
          have hnot : ¬(a.2.1 = p) := fun h => hne h.symm
          simp [hnot]
        · intro h
          exact False.elim (h (Finset.mem_univ a.2.1))
      · intro c1 hc1 hne
        by_cases h : c1 = a.1
        · apply False.elim
          apply hne
          exact h
        · -- c1 ≠ a.1 → the sum is 0
          apply Finset.sum_eq_zero
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
        · exact hr
        · apply Prod.ext
          · exact ht
          · exact h22
      simp [hab]
    · have hab : a ≠ b := by
        intro h
        apply h22
        exact congrArg (fun x : Fin d × (Fin d × Fin d) => x.2.2) h
      simp [hab, h22]
  · -- a.1 ≠ b.1 ∨ a.2.1 ≠ b.2.1 → the sum is 0 = δ
    have hsum0 : (∑ c : Fin d × (Fin d × Fin d),
        quraDecoder U a c * star (quraDecoder U) c b) = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      -- both factors have disjoint conditions
      by_cases hca : c.1 = a.1 ∧ c.2.1 = a.2.1
      · have hcb : ¬(c.1 = b.1 ∧ c.2.1 = b.2.1) := by
          intro h
          apply hb
          exact ⟨hca.1.symm.trans h.1, hca.2.symm.trans h.2⟩
        have hcb' : ¬(b.1 = c.1 ∧ b.2.1 = c.2.1) := by
          intro h
          apply hcb
          exact ⟨h.1.symm, h.2.symm⟩
        have h1' : a.1 = c.1 ∧ a.2.1 = c.2.1 := ⟨hca.1.symm, hca.2.symm⟩
        simp [quraDecoder, h1', hcb']
      · have hca' : ¬(a.1 = c.1 ∧ a.2.1 = c.2.1) := by
          intro h
          apply hca
          exact ⟨h.1.symm, h.2.symm⟩
        simp [quraDecoder, hca']
    rw [hsum0]
    -- δ_{a,b} = 0 since a ≠ b
    have hab : a ≠ b := by
      intro h
      apply hb
      exact ⟨congrArg (fun x : Fin d × (Fin d × Fin d) => x.1) h,
        congrArg (fun x : Fin d × (Fin d × Fin d) => x.2.1) h⟩
    simp [hab]
/-- Certified decoder when its input matrix is unitary. -/
def decoderOperator (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix.unitaryGroup (Fin d × (Fin d × Fin d)) ℂ :=
  ⟨quraDecoder (d := d) (U : Matrix (Fin d) (Fin d) ℂ), by
    exact quraDecoder_mem_unitaryGroup (d := d)
      (U : Matrix (Fin d) (Fin d) ℂ) U.property⟩

/-- The certified decoder has the declared block-diagonal formula. -/
@[simp] lemma decoderOperator_coe (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (decoderOperator U : Matrix (Fin d × (Fin d × Fin d)) (Fin d × (Fin d × Fin d)) ℂ) =
      quraDecoder U := rfl

end

end QuantumAlg.UnitaryReversal
