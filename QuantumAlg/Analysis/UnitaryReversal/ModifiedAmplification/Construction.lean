/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.State.Normalized

public import QuantumAlg.Analysis.UnitaryReversal.Amplification

/-!
# Modified-amplifier matrix construction

Parameterized ancilla matrices and their basic actions, following
[CML+24, main.tex:1030] and [CML+24, main.tex:1040].
The formula still contains the encoder with direct access to the conjugate
input; it is not an implementation from an unknown-unitary oracle.
-/

@[expose] public section

namespace QuantumAlg.UnitaryReversal

noncomputable section

open MatrixWeyl

-- Preserve symbolic basis coefficients until a proof requests their entry formula.
attribute [-simp] NormalizedVector.ket_apply

variable {d : ℕ}

local notation "k₀" => (NormalizedVector.ket (R := Qubits 1) 0)
local notation "k₁" => (NormalizedVector.ket (R := Qubits 1) 1)


/-!
# Modified amplifier `A_α` (paper Lemma S9)

`A_α,θ(U) = (1₂⊗E(U))·(G''_α⊗1)·(X⊗D(U))·(G'_α⊗1)` with
`G'_α = (|1⟩⟨1|₂⊗F_α + |0⟩⟨0|₂⊗1)·((X₂⁻¹)⊗|00⟩⟨00| + 1₂⊗1)` and
`G''_α = ((R_y(t)−1₂)⊗|00⟩⟨00| + 1₂⊗1)·(|1⟩⟨1|₂⊗F† + |0⟩⟨0|₂⊗1)`,
where `F_α|00⟩ = √(1−α²)|00⟩ + α|00⊥⟩` (Eq. A.83), `F` is the base Householder
with `F|00⊥⟩ = |00⟩`, and `R_y(t)` has angle `t = −2·arctan(1/(tanθ·√(1−α²)))`.
-/

/-- The total `α`-rotation formula: `F_α|00⟩ = √(1−α²)|00⟩ + α|00⊥⟩`,
`F_α|00⊥⟩ = −α|00⟩ + √(1−α²)|00⊥⟩`, identity on the complement. -/
def quraFα (d : ℕ) [NeZero d] (α : ℝ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.of fun a b =>
    ((((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) * (if a = (0, 0) then 1 else 0) +
        (α : ℂ) * quraKet00Perp d a) * (if b = (0, 0) then 1 else 0)) +
    (-((α : ℂ) * (if a = (0, 0) then 1 else 0)) +
        ((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) * quraKet00Perp d a) * star (quraKet00Perp d b) +
    (if a = b then 1 else 0) -
    (if a = (0, 0) ∧ b = (0, 0) then 1 else 0) -
    quraKet00Perp d a * star (quraKet00Perp d b)

/-- `F_α|00⟩ = √(1−α²)|00⟩ + α|00⊥⟩`. -/
lemma quraFα_mulVec_ket00 (d : ℕ) [NeZero d] (_hd : 2 ≤ d) (α : ℝ) :
    Matrix.mulVec (quraFα d α) (quraKet00 d) =
      ((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) • quraKet00 d + (α : ℂ) • quraKet00Perp d := by
  ext a
  change (∑ b : Fin d × Fin d, quraFα d α a b * quraKet00 d b) =
    ((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) * quraKet00 d a + (α : ℂ) * quraKet00Perp d a
  rw [Finset.sum_eq_single (0, (0 : Fin d))]
  · have hperp00 : quraKet00Perp d (0, 0) = 0 := by
      simp [quraKet00Perp]
    have hk00 : quraKet00 d (0, 0) = 1 := by
      simp [quraKet00]
    simp [quraFα, hperp00, hk00]
    by_cases ha : a.1 = 0 ∧ a.2 = 0
    · have ha' : a = (0, 0) := by
        apply Prod.ext
        · exact ha.1
        · exact ha.2
      simp [quraKet00, ha']
    · have ha' : a ≠ (0, 0) := by
        intro h
        apply ha
        exact ⟨congrArg (fun x : Fin d × Fin d => x.1) h,
          congrArg (fun x : Fin d × Fin d => x.2) h⟩
      simp [quraKet00, ha, ha']
  · intro b hb hne
    have hnot : ¬(b.1 = 0 ∧ b.2 = 0) := by
      intro h
      apply hne
      apply Prod.ext
      · exact h.1
      · exact h.2
    simp [quraKet00, hnot]
  · intro h
    exact False.elim (h (Finset.mem_univ (0, (0 : Fin d))))

/-- The single-qubit Y-rotation by angle `t`. -/
def quraRy (t : ℝ) : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨Matrix.of (fun i j =>
    if i = 0 ∧ j = 0 then (Real.cos (t / 2) : ℂ)
    else if i = 0 ∧ j = 1 then -(Real.sin (t / 2) : ℂ)
    else if i = 1 ∧ j = 0 then (Real.sin (t / 2) : ℂ)
    else (Real.cos (t / 2) : ℂ)), by
    have h : (Real.cos (t / 2) : ℂ) ^ 2 + (Real.sin (t / 2) : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.cos_sq_add_sin_sq (t / 2)
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      norm_num only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
        Matrix.one_apply, Matrix.of_apply, Fin.ext_iff, Fin.val_zero, Fin.val_one,
        and_true, and_false,
        true_and, false_and, ite_true, ite_false, Complex.star_def, Complex.conj_ofReal,
        map_neg, neg_mul, mul_neg, neg_neg]
      solve | ring | linear_combination h⟩

local notation "Y[" t "]" => (quraRy t : Matrix (Fin 2) (Fin 2) ℂ)

/-- `cos(arctan(y/x)) = x / √(x²+y²)` for `x > 0`. -/
lemma quraRy_cos_arctan (x y : ℝ) (hx : 0 < x) :
    Real.cos (Real.arctan (y / x)) = x / Real.sqrt (x ^ 2 + y ^ 2) := by
  rw [Real.cos_arctan]
  rw [show 1 + (y / x) ^ 2 = (x ^ 2 + y ^ 2) / x ^ 2 by field_simp [hx.ne']]
  rw [Real.sqrt_div (by positivity : 0 ≤ x ^ 2 + y ^ 2)]
  rw [Real.sqrt_sq hx.le]
  field_simp [hx.ne']

/-- `sin(arctan(y/x)) = y / √(x²+y²)` for `x > 0`. -/
lemma quraRy_sin_arctan (x y : ℝ) (hx : 0 < x) :
    Real.sin (Real.arctan (y / x)) = y / Real.sqrt (x ^ 2 + y ^ 2) := by
  rw [Real.sin_arctan]
  rw [show 1 + (y / x) ^ 2 = (x ^ 2 + y ^ 2) / x ^ 2 by field_simp [hx.ne']]
  rw [Real.sqrt_div (by positivity : 0 ≤ x ^ 2 + y ^ 2)]
  rw [Real.sqrt_sq hx.le]
  field_simp [hx.ne']

/-- `R_y(−2·arctan(y/x))·(x|0⟩ + y|1⟩) = √(x²+y²)·|0⟩` for `x > 0`. -/
lemma quraRy_mulVec_align (x y : ℝ) (hx : 0 < x) :
    Matrix.mulVec (Y[-2 * Real.arctan (y / x)])
        (fun i : Fin 2 => if i = 0 then (x : ℂ) else (y : ℂ)) =
      fun i : Fin 2 => if i = 0 then ((Real.sqrt (x ^ 2 + y ^ 2) : ℝ) : ℂ) else 0 := by
  have hcosℂ : Complex.cos ((Real.arctan (y / x) : ℝ) : ℂ) =
      ((x / Real.sqrt (x ^ 2 + y ^ 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cos]
    rw [Real.cos_arctan]
    rw [show 1 + (y / x) ^ 2 = (x ^ 2 + y ^ 2) / x ^ 2 by field_simp [hx.ne']]
    rw [Real.sqrt_div (by positivity : 0 ≤ x ^ 2 + y ^ 2)]
    rw [Real.sqrt_sq hx.le]
    field_simp [hx.ne']
  have hsinℂ : Complex.sin ((Real.arctan (y / x) : ℝ) : ℂ) =
      ((y / Real.sqrt (x ^ 2 + y ^ 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sin]
    rw [Real.sin_arctan]
    rw [show 1 + (y / x) ^ 2 = (x ^ 2 + y ^ 2) / x ^ 2 by field_simp [hx.ne']]
    rw [Real.sqrt_div (by positivity : 0 ≤ x ^ 2 + y ^ 2)]
    rw [Real.sqrt_sq hx.le]
    field_simp [hx.ne']
  ext i
  fin_cases i
  · change (∑ j : Fin 2, (Y[-2 * Real.arctan (y / x)]) 0 j *
        (if j = 0 then (x : ℂ) else (y : ℂ))) = ((Real.sqrt (x ^ 2 + y ^ 2) : ℝ) : ℂ)
    have hhalf : (-(2 * Real.arctan (y / x))) / 2 = -Real.arctan (y / x) := by ring
    rw [Fin.sum_univ_two]
    simp [quraRy, hhalf, hcosℂ, hsinℂ]
    have hs : (Real.sqrt (x ^ 2 + y ^ 2) : ℝ) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (by nlinarith [hx] : 0 < x ^ 2 + y ^ 2))
    field_simp [hx.ne', (by exact_mod_cast hs : (((Real.sqrt (x ^ 2 + y ^ 2) : ℝ) : ℂ) ≠ 0))]
    norm_num [← Complex.ofReal_pow, ← Complex.ofReal_add]
    rw [Real.sq_sqrt (by nlinarith [hx] : 0 ≤ x ^ 2 + y ^ 2)]
  · change (∑ j : Fin 2, (Y[-2 * Real.arctan (y / x)]) 1 j *
        (if j = 0 then (x : ℂ) else (y : ℂ))) = 0
    have hhalf : (-(2 * Real.arctan (y / x))) / 2 = -Real.arctan (y / x) := by ring
    rw [Fin.sum_univ_two]
    simp [quraRy, hhalf, hcosℂ, hsinℂ]
    have hs : (Real.sqrt (x ^ 2 + y ^ 2) : ℝ) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (by nlinarith [hx] : 0 < x ^ 2 + y ^ 2))
    field_simp [hx.ne', (by exact_mod_cast hs : (((Real.sqrt (x ^ 2 + y ^ 2) : ℝ) : ℂ) ≠ 0))]
    ring

/-- `|1⟩⟨1|₂⊗F_α + |0⟩⟨0|₂⊗1` on the (ancilla, d²) register. -/
def quraG1α (d : ℕ) [NeZero d] (α : ℝ) :
    Matrix (Fin 2 × (Fin d × Fin d)) (Fin 2 × (Fin d × Fin d)) ℂ :=
  Matrix.of fun a b =>
    (if a.1 = 1 ∧ b.1 = 1 then quraFα d α a.2 b.2 else 0) +
      (if a.1 = 0 ∧ b.1 = 0 then (if a.2 = b.2 then 1 else 0) else 0)

/-- `((R_y(t)−1₂)⊗|00⟩⟨00| + 1₂⊗1)` on the (ancilla, d²) register. -/
@[nolint unusedArguments]
def quraG4 (d : ℕ) [NeZero d] (t : ℝ) :
    Matrix (Fin 2 × (Fin d × Fin d)) (Fin 2 × (Fin d × Fin d)) ℂ :=
  Matrix.of fun a b =>
    ((Y[t] a.1 b.1 - (if a.1 = b.1 then 1 else 0)) * quraKet00 d a.2 * quraKet00 d b.2) +
      (if a.1 = b.1 then 1 else 0) * (if a.2 = b.2 then 1 else 0)

/-- `G'_α = (|1⟩⟨1|₂⊗F_α + |0⟩⟨0|₂⊗1)·((X₂⁻¹)⊗|00⟩⟨00| + 1₂⊗1)`. -/
def quraGPrime (d : ℕ) [NeZero d] (α : ℝ) :
    Matrix (Fin 2 × (Fin d × Fin d)) (Fin 2 × (Fin d × Fin d)) ℂ :=
  quraG1α d α * quraG2 d

/-- `|1⟩⊗M` with the ancilla qubit in `|1⟩`. -/
def quraKet1Mat (d : ℕ) (M : Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ) :
    Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin d) ℂ :=
  Matrix.of fun a s => k₁ a.1 * M (a.2.1, (a.2.2.1, a.2.2.2)) s

/-- The `F_α|00⟩ = √(1−α²)|00⟩ + α|00⊥⟩` image tensored with `U†`. -/
@[nolint unusedArguments]
def quraFαImage (d : ℕ) [NeZero d] (α : ℝ) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ :=
  Matrix.of fun a s =>
    (((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) * quraKet00 d (a.1, a.2.1) +
      (α : ℂ) * quraKet00Perp d (a.1, a.2.1)) * U.conjTranspose a.2.2 s

/-- `G'_α·(|1⟩|00⟩) = |1⟩⊗F_α|00⟩`. -/
lemma quraG1α_mulVec_ket1_ket00 (d : ℕ) [NeZero d] (hd : 2 ≤ d) (α : ℝ) :
    Matrix.mulVec (quraG1α d α) (fun a : Fin 2 × (Fin d × Fin d) => k₁ a.1 * quraKet00 d a.2)
    =
      fun a : Fin 2 × (Fin d × Fin d) =>
        k₁ a.1 * (((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) * quraKet00 d a.2 +
          (α : ℂ) * quraKet00Perp d a.2) := by
  ext a
  change (∑ b : Fin 2 × (Fin d × Fin d),
      quraG1α d α a b * (k₁ b.1 * quraKet00 d b.2)) =
    k₁ a.1 * (((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) * quraKet00 d a.2 +
      (α : ℂ) * quraKet00Perp d a.2)
  by_cases ha1 : a.1 = 1
  · have hcol : (∑ b : Fin 2 × (Fin d × Fin d),
        quraG1α d α a b * (k₁ b.1 * quraKet00 d b.2)) =
        (∑ b : Fin d × Fin d, quraFα d α a.2 b * quraKet00 d b) := by
      rw [show a = (1, a.2) by
        apply Prod.ext
        · exact ha1
        · rfl]
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single (1 : Fin 2)]
      · simp [quraG1α, NormalizedVector.ket_apply]
      · intro i hi hi0
        have hi' : i ≠ (1 : Fin 2) := fun h => hi0 h
        simp [quraG1α, hi', NormalizedVector.ket_apply]
      · intro h
        exact False.elim (h (Finset.mem_univ (1 : Fin 2)))
    rw [hcol]
    change (Matrix.mulVec (quraFα d α) (quraKet00 d)) a.2 =
      k₁ a.1 * (((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) * quraKet00 d a.2 +
        (α : ℂ) * quraKet00Perp d a.2)
    rw [quraFα_mulVec_ket00 d hd α]
    rw [ha1]
    have hk1 : k₁ (1 : Fin 2) = 1 := by simp [NormalizedVector.ket_apply]
    rw [hk1]
    simp [mul_add, mul_left_comm]
  · have hcol : (∑ b : Fin 2 × (Fin d × Fin d),
        quraG1α d α a b * (k₁ b.1 * quraKet00 d b.2)) = 0 := by
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single (1 : Fin 2)]
      · simp [quraG1α, ha1, NormalizedVector.ket_apply]
      · intro i hi hi0
        have hi' : i ≠ (1 : Fin 2) := fun h => hi0 h
        simp [quraG1α, hi', NormalizedVector.ket_apply]
      · intro h
        exact False.elim (h (Finset.mem_univ (1 : Fin 2)))
    rw [hcol]
    have hk1 : k₁ a.1 = 0 := by simp [ha1, NormalizedVector.ket_apply]
    simp [hk1]

/-- `G'_α·(|0⟩|00⟩) = |1⟩⊗F_α|00⟩`. -/
lemma quraGPrime_mulVec_ket0_ket00 (d : ℕ) [NeZero d] (hd : 2 ≤ d) (α : ℝ) :
    Matrix.mulVec (quraGPrime d α) (fun a : Fin 2 × (Fin d × Fin d) => k₀ a.1 * quraKet00 d
    a.2) =
      fun a : Fin 2 × (Fin d × Fin d) =>
        k₁ a.1 * (((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) * quraKet00 d a.2 +
          (α : ℂ) * quraKet00Perp d a.2) := by
  rw [quraGPrime]
  rw [← Matrix.mulVec_mulVec]
  rw [show Matrix.mulVec (quraG2 d) (fun a : Fin 2 × (Fin d × Fin d) =>
      k₀ a.1 * quraKet00 d a.2) = fun a => k₁ a.1 * quraKet00 d a.2 by
    change Matrix.mulVec (quraG2 d) (quraV00 d) = fun a => k₁ a.1 * quraKet00 d a.2
    rw [quraG2_mulVec_ket0_ket00]]
  exact quraG1α_mulVec_ket1_ket00 d hd α

/-- The `R_y` angle `t = −2·arctan(cosθ/(√(1−α²)·sinθ))`, the paper's
`−2·arctan(1/(tanθ·√(1−α²)))` (equal since `cosθ/(sinθ) = 1/tanθ`). -/
def quraAlphaT (α θ : ℝ) : ℝ :=
  -2 * Real.arctan (Real.cos θ / (Real.sqrt (1 - α ^ 2) * Real.sin θ))

/-- `G''_α = ((R_y(t)−1₂)⊗|00⟩⟨00| + 1₂⊗1)·(|1⟩⟨1|₂⊗F + |0⟩⟨0|₂⊗1)` with the
base Householder `F` (`F†|00⊥⟩ = |00⟩`) and the angle `t` of Eq. (A.85). -/
def quraGDoublePrime (d : ℕ) [NeZero d] (α θ : ℝ) :
    Matrix (Fin 2 × (Fin d × Fin d)) (Fin 2 × (Fin d × Fin d)) ℂ :=
  quraG4 d (quraAlphaT α θ) * quraG1 d

/-- `G'_α ⊗ 1` on the (ancilla, three-qudit) register. -/
def quraGPrimeTensor (d : ℕ) [NeZero d] (α : ℝ) :
    Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin 2 × (Fin d × (Fin d × Fin d))) ℂ :=
  Matrix.of fun a b =>
    quraGPrime d α (a.1, (a.2.1, a.2.2.1)) (b.1, (b.2.1, b.2.2.1)) *
      (if a.2.2.2 = b.2.2.2 then 1 else 0)

/-- `G''_α ⊗ 1` on the (ancilla, three-qudit) register. -/
def quraGDoublePrimeTensor (d : ℕ) [NeZero d] (α θ : ℝ) :
    Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin 2 × (Fin d × (Fin d × Fin d))) ℂ :=
  Matrix.of fun a b =>
    quraGDoublePrime d α θ (a.1, (a.2.1, a.2.2.1)) (b.1, (b.2.1, b.2.2.1)) *
      (if a.2.2.2 = b.2.2.2 then 1 else 0)

/-- The modified-amplifier matrix
`A_α,θ(U) = (1₂⊗E(U))·(G''_α⊗1)·(X⊗D(U))·(G'_α⊗1)`. -/
@[nolint unusedArguments]
def quraV1Fα (d : ℕ) [NeZero d] (α : ℝ) : Fin 2 × (Fin d × Fin d) → ℂ :=
  fun a => k₁ a.1 * (((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) * quraKet00 d a.2 +
    (α : ℂ) * quraKet00Perp d a.2)

/-- `(G'_α⊗I)·(|0⟩⊗(|00⟩⊗U†)) = |1⟩⊗(F_α|00⟩⊗U†)`. -/
lemma quraGPrimeTensor_mul_ket0_ket00_U (d : ℕ) [NeZero d] (hd : 2 ≤ d) (α : ℝ)
    (U : Matrix (Fin d) (Fin d) ℂ) :
    quraGPrimeTensor d α * (Matrix.of fun (a : Fin 2 × (Fin d × (Fin d × Fin d))) (s : Fin d) =>
        k₀ a.1 * (quraKet00 d (a.2.1, a.2.2.1) * U.conjTranspose a.2.2.2 s)) =
      Matrix.of fun (a : Fin 2 × (Fin d × (Fin d × Fin d))) (s : Fin d) =>
        k₁ a.1 * (((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) * quraKet00 d (a.2.1, a.2.2.1) +
          (α : ℂ) * quraKet00Perp d (a.2.1, a.2.2.1)) * U.conjTranspose a.2.2.2 s := by
  ext a s
  rw [Matrix.mul_apply]
  change (∑ b : Fin 2 × (Fin d × (Fin d × Fin d)),
      quraGPrime d α (a.1, (a.2.1, a.2.2.1)) (b.1, (b.2.1, b.2.2.1)) * (if a.2.2.2 = b.2.2.2 then 1
      else 0) *
        (k₀ b.1 * (quraKet00 d (b.2.1, b.2.2.1) * U.conjTranspose b.2.2.2 s))) =
      k₁ a.1 * (((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) * quraKet00 d (a.2.1, a.2.2.1) +
        (α : ℂ) * quraKet00Perp d (a.2.1, a.2.2.1)) * U.conjTranspose a.2.2.2 s
  have hG00 : quraGPrime d α (a.1, (a.2.1, a.2.2.1)) (0, (0, 0)) * k₀ 0 * quraKet00 d (0, 0) =
      quraV1Fα d α (a.1, (a.2.1, a.2.2.1)) := by
    have hcol : (Matrix.mulVec (quraGPrime d α) (quraV00 d)) (a.1, (a.2.1, a.2.2.1)) =
        quraGPrime d α (a.1, (a.2.1, a.2.2.1)) (0, (0, 0)) * quraV00 d (0, (0, 0)) := by
      rw [Matrix.mulVec]
      change (∑ b : Fin 2 × (Fin d × Fin d), quraGPrime d α (a.1, (a.2.1, a.2.2.1)) b * quraV00 d
      b) =
        quraGPrime d α (a.1, (a.2.1, a.2.2.1)) (0, (0, 0)) * quraV00 d (0, (0, 0))
      rw [Finset.sum_eq_single (0, (0, 0))]
      · intro b hb hne
        have hv : quraV00 d b = 0 := by
          by_cases hb0 : b.1 = 0
          · by_cases hb00 : b.2 = (0, 0)
            · exfalso
              apply hne
              apply Prod.ext
              · exact hb0
              · exact hb00
            · have hk : quraKet00 d b.2 = 0 := by
                change (if b.2.1.val = 0 ∧ b.2.2.val = 0 then 1 else 0) = 0
                have hnot : ¬ (b.2.1.val = 0 ∧ b.2.2.val = 0) := by
                  intro h
                  apply hb00
                  apply Prod.ext
                  · exact Fin.ext h.1
                  · exact Fin.ext h.2
                rw [if_neg hnot]
              change k₀ b.1 * quraKet00 d b.2 = 0
              rw [hk]
              simp [hb0]
          · simp [quraV00, hb0, NormalizedVector.ket_apply]
        rw [hv]
        simp
      · intro h
        exact False.elim (h (Finset.mem_univ (0, (0, 0))))
    calc
      quraGPrime d α (a.1, (a.2.1, a.2.2.1)) (0, (0, 0)) * k₀ 0 * quraKet00 d (0, 0)
          = quraGPrime d α (a.1, (a.2.1, a.2.2.1)) (0, (0, 0)) * quraV00 d (0, (0, 0)) := by
            rw [show quraV00 d (0, (0, 0)) = k₀ 0 * quraKet00 d (0, 0) by rfl]
            ring
      _ = (Matrix.mulVec (quraGPrime d α) (quraV00 d)) (a.1, (a.2.1, a.2.2.1)) := by
            rw [← hcol]
      _ = quraV1Fα d α (a.1, (a.2.1, a.2.2.1)) := by
            change (Matrix.mulVec (quraGPrime d α) (fun a : Fin 2 × (Fin d × Fin d) =>
              k₀ a.1 * quraKet00 d a.2)) (a.1, (a.2.1, a.2.2.1)) =
                quraV1Fα d α (a.1, (a.2.1, a.2.2.1))
            rw [quraGPrime_mulVec_ket0_ket00 d hd α]
            rfl
  rw [Finset.sum_eq_single (0, (0, (0, a.2.2.2)))]
  · calc
      quraGPrime d α (a.1, (a.2.1, a.2.2.1)) (0, (0, 0)) *
            (if a.2.2.2 = a.2.2.2 then 1 else 0) *
            (k₀ 0 * (quraKet00 d (0, 0) * U.conjTranspose a.2.2.2 s))
          = quraGPrime d α (a.1, (a.2.1, a.2.2.1)) (0, (0, 0)) * 1 *
            (k₀ 0 * (quraKet00 d (0, 0) * U.conjTranspose a.2.2.2 s)) := by
            rw [if_pos rfl]
      _ = (quraGPrime d α (a.1, (a.2.1, a.2.2.1)) (0, (0, 0)) * k₀ 0 * quraKet00 d (0, 0)) *
            U.conjTranspose a.2.2.2 s := by
            ring
      _ = quraV1Fα d α (a.1, (a.2.1, a.2.2.1)) * U.conjTranspose a.2.2.2 s := by
            rw [hG00]
      _ = k₁ a.1 * (((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) * quraKet00 d (a.2.1, a.2.2.1) +
            (α : ℂ) * quraKet00Perp d (a.2.1, a.2.2.1)) * U.conjTranspose a.2.2.2 s := by
            rw [show quraV1Fα d α (a.1, (a.2.1, a.2.2.1)) =
              k₁ a.1 * (((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) * quraKet00 d (a.2.1, a.2.2.1) +
                (α : ℂ) * quraKet00Perp d (a.2.1, a.2.2.1)) by rfl]
  · intro b hb hne
    by_cases hb0 : b.1 = 0
    · by_cases hb00 : b.2.1 = 0 ∧ b.2.2.1 = 0
      · by_cases ht : b.2.2.2 = a.2.2.2
        · exfalso
          apply hne
          apply Prod.ext
          · exact hb0
          · apply Prod.ext
            · exact hb00.1
            · apply Prod.ext
              · exact hb00.2
              · exact ht
        · have hnot : ¬ a.2.2.2 = b.2.2.2 := fun hh => ht hh.symm
          rw [if_neg hnot]
          simp
      · have hk : quraKet00 d (b.2.1, b.2.2.1) = 0 := by
          change (if b.2.1.val = 0 ∧ b.2.2.1.val = 0 then 1 else 0) = 0
          have hnot : ¬ (b.2.1.val = 0 ∧ b.2.2.1.val = 0) := by
            intro h
            apply hb00
            exact ⟨Fin.ext h.1, Fin.ext h.2⟩
          rw [if_neg hnot]
        rw [hk]
        simp
    · have hk : k₀ b.1 = 0 := by simp [hb0, NormalizedVector.ket_apply]
      rw [hk]
      simp
  · intro h
    exact False.elim (h (Finset.mem_univ (0, (0, (0, a.2.2.2)))))

/-- `G1α·|0⟩⊗x = |0⟩⊗x` for any `x`. -/
lemma quraG1α_mulVec_ket0 (d : ℕ) [NeZero d] (α : ℝ) (x : Fin d × Fin d → ℂ) :
    Matrix.mulVec (quraG1α d α) (fun a => k₀ a.1 * x a.2) =
      fun a => k₀ a.1 * x a.2 := by
  ext a
  change (∑ b : Fin 2 × (Fin d × Fin d),
      quraG1α d α a b * (k₀ b.1 * x b.2)) = k₀ a.1 * x a.2
  by_cases ha0 : a.1 = 0
  · have ha' : a = (0, a.2) := by
      apply Prod.ext
      · exact ha0
      · rfl
    rw [ha']
    rw [Finset.sum_eq_single (0, a.2)]
    · simp [quraG1α, NormalizedVector.ket_apply]
    · intro b hb hne
      by_cases hb1 : b.1 = 0
      · have hb2 : b.2 ≠ a.2 := by
          intro h
          apply hne
          apply Prod.ext
          · exact hb1
          · exact h
        have hg : quraG1α d α (0, a.2) b = 0 := by
          have hnot : ¬(a.2 = b.2) := fun h => hb2 h.symm
          simp [quraG1α, hb1, hnot]
        rw [hg]
        simp
      · have hb1' : b.1 = 1 := by
          apply Fin.ext
          have hlt : b.1.val < 2 := b.1.isLt
          have hne0 : b.1.val ≠ 0 := by
            intro h
            apply hb1
            apply Fin.ext
            exact h
          omega
        have hg : quraG1α d α (0, a.2) b = 0 := by
          simp [quraG1α, hb1']
        rw [hg]
        simp
    · intro h
      exact False.elim (h (Finset.mem_univ (0, a.2)))
  · have ha1 : a.1 = 1 := by
      apply Fin.ext
      have hlt : a.1.val < 2 := a.1.isLt
      have hne0 : a.1.val ≠ 0 := by
        intro h
        apply ha0
        apply Fin.ext
        exact h
      omega
    have ha' : a = (1, a.2) := by
      apply Prod.ext
      · exact ha1
      · rfl
    rw [ha']
    have hk : k₀ (1 : Fin 2) = 0 := by simp [NormalizedVector.ket_apply]
    rw [hk, zero_mul]
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hb1 : b.1 = 0
    · have hg : quraG1α d α (1, a.2) b = 0 := by
        simp [quraG1α, hb1]
      rw [hg]
      simp
    · have hb1' : b.1 = 1 := by
        apply Fin.ext
        have hlt : b.1.val < 2 := b.1.isLt
        have hne0 : b.1.val ≠ 0 := by
          intro h
          apply hb1
          apply Fin.ext
          exact h
        omega
      have hk : k₀ b.1 = 0 := by simp [hb1', NormalizedVector.ket_apply]
      rw [hk]
      simp

/-- `G'_α·|0⟩⊗x = |0⟩⊗x` when `x` has no `|00⟩` component. -/
lemma quraGPrime_mulVec_ket0_of_perp (d : ℕ) [NeZero d] (α : ℝ) (x : Fin d × Fin d → ℂ)
    (hx : x (0, 0) = 0) :
    Matrix.mulVec (quraGPrime d α) (fun a => k₀ a.1 * x a.2) =
      fun a => k₀ a.1 * x a.2 := by
  rw [quraGPrime, ← Matrix.mulVec_mulVec]
  rw [show Matrix.mulVec (quraG2 d) (fun a : Fin 2 × (Fin d × Fin d) => k₀ a.1 * x a.2) =
      fun a => k₀ a.1 * x a.2 by
    exact quraG2_mulVec_ket0_of_perp d x hx]
  exact quraG1α_mulVec_ket0 d α x

/-- Collapse the target-qudit sum in `G'_α⊗I`. -/
lemma quraGPrime_collapse_t (d : ℕ) [NeZero d] (α : ℝ) (a : Fin 2 × (Fin d × (Fin d × Fin d)))
    (v : Fin 2 × (Fin d × (Fin d × Fin d)) → ℂ) :
    (∑ b : Fin 2 × (Fin d × (Fin d × Fin d)),
        quraGPrime d α (a.1, (a.2.1, a.2.2.1)) (b.1, (b.2.1, b.2.2.1)) * (if a.2.2.2 = b.2.2.2 then
        1 else 0) * v b) =
      ∑ b : Fin 2 × (Fin d × Fin d),
        quraGPrime d α (a.1, (a.2.1, a.2.2.1)) b * v (b.1, (b.2.1, (b.2.2, a.2.2.2))) := by
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro c1 hc1
  apply Finset.sum_congr rfl
  intro c2 hc2
  rw [Finset.sum_eq_single a.2.2.2]
  · rw [if_pos rfl]
    simp
  · intro t ht hne
    rw [if_neg (fun hh => hne hh.symm)]
    simp
  · intro h
    exact False.elim (h (Finset.mem_univ a.2.2.2))


/-- The modified-amplifier matrix
`A_α,θ(U) = (1₂⊗E(U))·(G''_α⊗1)·(X⊗D(U))·(G'_α⊗1)`. -/
def quraModifiedAmplifier (d : ℕ) [NeZero d] (U : Matrix (Fin d) (Fin d) ℂ) (α θ : ℝ) :
    Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin 2 × (Fin d × (Fin d × Fin d))) ℂ :=
  quraI2E d U * (quraGDoublePrimeTensor d α θ * (quraX2D d U * quraGPrimeTensor d α))

/-- `D(U)·(|00⟩⊗U†) = Λ₀`. -/
lemma quraDecoder_mul_ket00_Udag (d : ℕ) [NeZero d] (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quraDecoder U * (Matrix.of fun a s =>
        quraKet00 d (a.1, a.2.1) * U.conjTranspose a.2.2 s) =
      quraLambda0 d := by
  have hLU : (Matrix.of fun a s =>
      quraKet00 d (a.1, a.2.1) * U.conjTranspose a.2.2 s) = quraLambda0 d * U.conjTranspose := by
    ext a s
    simp [quraLambda0, Matrix.mul_apply, quraKet00, mul_comm]
  have hUU : U * U.conjTranspose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hU
  calc
    quraDecoder U * (Matrix.of fun a s =>
        quraKet00 d (a.1, a.2.1) * U.conjTranspose a.2.2 s)
        = quraDecoder U * (quraLambda0 d * U.conjTranspose) := by
          rw [hLU]
    _ = (quraDecoder U * quraLambda0 d) * U.conjTranspose := by
          rw [Matrix.mul_assoc]
    _ = (quraLambda0 d * U) * U.conjTranspose := by
          rw [quraDecoder_mulVec_ket00]
    _ = quraLambda0 d * (U * U.conjTranspose) := by
          rw [Matrix.mul_assoc]
    _ = quraLambda0 d * (1 : Matrix (Fin d) (Fin d) ℂ) := by
          rw [hUU]
    _ = quraLambda0 d := by
          simp

/-- `D(U)·(F_α|00⟩⊗U†) = √(1−α²)·Λ₀ + α·Λ⊥`. -/
lemma quraDecoder_mul_FαImage (d : ℕ) [NeZero d] (α : ℝ)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quraDecoder U * quraFαImage d α U =
      ((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) • quraLambda0 d + (α : ℂ) • quraLambdaPerp d U := by
  have hsplit : quraFαImage d α U =
      ((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) •
          (Matrix.of fun a s => quraKet00 d (a.1, a.2.1) * U.conjTranspose a.2.2 s) +
        (α : ℂ) •
          (Matrix.of fun a s => quraKet00Perp d (a.1, a.2.1) * U.conjTranspose a.2.2 s) := by
    ext a s
    simp [quraFαImage]
    ring
  rw [hsplit]
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
  rw [quraDecoder_mul_ket00_Udag d U hU]
  rw [show quraDecoder U * (Matrix.of fun a s =>
      quraKet00Perp d (a.1, a.2.1) * U.conjTranspose a.2.2 s) = quraLambdaPerp d U by rfl]

/-- `D(U)·Ψ⊥ = |00⊥⟩⊗I`. -/
lemma quraDecoder_mul_psiPerp (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quraDecoder U * quraPsiPerp d U = quraVecState d (quraKet00Perp d) := by
  rw [quraPsiPerp]
  exact quraDecoder_mul_conjTranspose_mul d U hU (quraVecState d (quraKet00Perp d))

/-- `(X₂⊗D(U))·(|1⟩⊗F_α|00⟩U†) = |0⟩⊗(√(1−α²)·Λ₀ + α·Λ⊥)`. -/
lemma quraX2D_mul_ket1_FαImage (d : ℕ) [NeZero d] (α : ℝ)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quraX2D d U * quraKet1Mat d (quraFαImage d α U) =
      quraKet0Mat d (((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) • quraLambda0 d +
        (α : ℂ) • quraLambdaPerp d U) := by
  simp only [quraKet1Mat, quraKet0Mat]
  rw [quraX2D_mul_ket1]
  rw [quraDecoder_mul_FαImage d α U hU]

/-- `(X₂⊗D(U))·(|0⟩⊗Ψ⊥) = |1⟩⊗(|00⊥⟩⊗I)`. -/
lemma quraX2D_mul_ket0_psiPerp (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quraX2D d U * quraKet0Mat d (quraPsiPerp d U) =
      quraKet1Mat d (quraVecState d (quraKet00Perp d)) := by
  simp only [quraKet0Mat, quraKet1Mat]
  rw [quraX2D_mul_ket0]
  rw [quraDecoder_mul_psiPerp d U hU]

/-- Step 2: `(X₂⊗D(U))` on the `G'_α` output. -/
lemma quraX2D_mul_GPrimeOut (d : ℕ) [NeZero d] (α θ : ℝ)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quraX2D d U * ((Real.sin θ : ℂ) • quraKet1Mat d (quraFαImage d α U) +
        (Real.cos θ : ℂ) • quraKet0Mat d (quraPsiPerp d U)) =
      (Real.sin θ : ℂ) • quraKet0Mat d (((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) • quraLambda0 d +
          (α : ℂ) • quraLambdaPerp d U) +
        (Real.cos θ : ℂ) • quraKet1Mat d (quraVecState d (quraKet00Perp d)) := by
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
  rw [quraX2D_mul_ket1_FαImage d α U hU]
  rw [quraX2D_mul_ket0_psiPerp d U hU]

/-- `|1⟩⟨1|₂⊗F + |0⟩⟨0|₂⊗1` tensored with the third-qudit identity. -/
def quraG1Tensor (d : ℕ) :
    Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin 2 × (Fin d × (Fin d × Fin d))) ℂ :=
  Matrix.of fun a b =>
    quraG1 d (a.1, (a.2.1, a.2.2.1)) (b.1, (b.2.1, b.2.2.1)) * (if a.2.2.2 = b.2.2.2 then 1 else 0)

/-- `((R_y(t)−1₂)⊗|00⟩⟨00| + 1₂⊗1)` tensored with the third-qudit identity. -/
def quraG4Tensor (d : ℕ) [NeZero d] (t : ℝ) :
    Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin 2 × (Fin d × (Fin d × Fin d))) ℂ :=
  Matrix.of fun a b =>
    quraG4 d t (a.1, (a.2.1, a.2.2.1)) (b.1, (b.2.1, b.2.2.1)) *
      (if a.2.2.2 = b.2.2.2 then 1 else 0)

/-- `(R_y(t)|i0⟩)⊗M`: the ancilla in the rotated `|i0⟩` state. -/
def quraRyState (t : ℝ) (M : Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ) (i0 : Fin 2) :
    Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin d) ℂ :=
  Matrix.of fun a s => Y[t] a.1 i0 * M (a.2.1, (a.2.2.1, a.2.2.2)) s

/-- Collapse the target-qudit sum in `G1⊗I`. -/
lemma quraG1_collapse_t (d : ℕ) (a : Fin 2 × (Fin d × (Fin d × Fin d)))
    (v : Fin 2 × (Fin d × (Fin d × Fin d)) → ℂ) :
    (∑ b : Fin 2 × (Fin d × (Fin d × Fin d)),
        quraG1 d (a.1, (a.2.1, a.2.2.1)) (b.1, (b.2.1, b.2.2.1)) *
            (if a.2.2.2 = b.2.2.2 then 1 else 0) * v b) =
      ∑ b : Fin 2 × (Fin d × Fin d),
        quraG1 d (a.1, (a.2.1, a.2.2.1)) b * v (b.1, (b.2.1, (b.2.2, a.2.2.2))) := by
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro c1 hc1
  apply Finset.sum_congr rfl
  intro c2 hc2
  rw [Finset.sum_eq_single a.2.2.2]
  · rw [if_pos rfl]
    simp
  · intro t ht hne
    rw [if_neg (fun hh => hne hh.symm)]
    simp
  · intro h
    exact False.elim (h (Finset.mem_univ a.2.2.2))

/-- `(G1⊗I)·(|1⟩⊗(|00⊥⟩⊗I)) = |1⟩⊗(|00⟩⊗I)`. -/
lemma quraG1Tensor_mul_ket1_ket00perp_I (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    quraG1Tensor d * quraKet1Mat d (quraVecState d (quraKet00Perp d)) =
      quraKet1Mat d (quraLambda0 d) := by
  ext a s
  rw [Matrix.mul_apply]
  change (∑ b : Fin 2 × (Fin d × (Fin d × Fin d)),
      quraG1 d (a.1, (a.2.1, a.2.2.1)) (b.1, (b.2.1, b.2.2.1)) *
          (if a.2.2.2 = b.2.2.2 then 1 else 0) *
        (k₁ b.1 * (quraKet00Perp d (b.2.1, b.2.2.1) * (if b.2.2.2 = s then 1 else 0)))) =
      k₁ a.1 * (quraKet00 d (a.2.1, a.2.2.1) * (if a.2.2.2 = s then 1 else 0))
  rw [quraG1_collapse_t d a
    (fun b => k₁ b.1 * (quraKet00Perp d (b.2.1, b.2.2.1) * (if b.2.2.2 = s then 1 else 0)))]
  calc
    (∑ b : Fin 2 × (Fin d × Fin d),
        quraG1 d (a.1, (a.2.1, a.2.2.1)) b *
          (k₁ b.1 * (quraKet00Perp d (b.2.1, b.2.2) * (if a.2.2.2 = s then 1 else 0))))
        = ∑ b : Fin 2 × (Fin d × Fin d),
            quraG1 d (a.1, (a.2.1, a.2.2.1)) b *
              (k₁ b.1 * quraKet00Perp d (b.2.1, b.2.2)) * (if a.2.2.2 = s then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro b hb
          ring
    _ = (∑ b : Fin 2 × (Fin d × Fin d),
            quraG1 d (a.1, (a.2.1, a.2.2.1)) b * (k₁ b.1 * quraKet00Perp d (b.2.1, b.2.2))) *
            (if a.2.2.2 = s then 1 else 0) := by
          rw [← Finset.sum_mul]
    _ = (Matrix.mulVec (quraG1 d) (quraV1perp d)) (a.1, (a.2.1, a.2.2.1)) *
            (if a.2.2.2 = s then 1 else 0) := by
          change (∑ b : Fin 2 × (Fin d × Fin d),
              quraG1 d (a.1, (a.2.1, a.2.2.1)) b * (quraV1perp d b)) *
                (if a.2.2.2 = s then 1 else 0) =
              (Matrix.mulVec (quraG1 d) (quraV1perp d)) (a.1, (a.2.1, a.2.2.1)) *
                (if a.2.2.2 = s then 1 else 0)
          rfl
    _ = k₁ a.1 * (quraKet00 d (a.2.1, a.2.2.1) * (if a.2.2.2 = s then 1 else 0)) := by
          change (Matrix.mulVec (quraG1 d) (fun a : Fin 2 × (Fin d × Fin d) =>
              k₁ a.1 * quraKet00Perp d a.2)) (a.1, (a.2.1, a.2.2.1)) *
                (if a.2.2.2 = s then 1 else 0) =
              k₁ a.1 * (quraKet00 d (a.2.1, a.2.2.1) * (if a.2.2.2 = s then 1 else 0))
          rw [quraG1_mulVec_ket1_ket00Perp d hd]
          change k₁ a.1 * quraKet00 d (a.2.1, a.2.2.1) * (if a.2.2.2 = s then 1 else 0) =
            k₁ a.1 * (quraKet00 d (a.2.1, a.2.2.1) * (if a.2.2.2 = s then 1 else 0))
          ring

/-- `(G1⊗I)·(|0⟩⊗M) = |0⟩⊗M` for any `M`. -/
lemma quraG1Tensor_mul_ket0 (d : ℕ)
    (M : Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ) :
    quraG1Tensor d * quraKet0Mat d M = quraKet0Mat d M := by
  ext a s
  rw [Matrix.mul_apply]
  change (∑ b : Fin 2 × (Fin d × (Fin d × Fin d)),
      quraG1 d (a.1, (a.2.1, a.2.2.1)) (b.1, (b.2.1, b.2.2.1)) *
          (if a.2.2.2 = b.2.2.2 then 1 else 0) *
        (k₀ b.1 * M (b.2.1, (b.2.2.1, b.2.2.2)) s)) =
      k₀ a.1 * M (a.2.1, (a.2.2.1, a.2.2.2)) s
  rw [quraG1_collapse_t d a (fun b => k₀ b.1 * M (b.2.1, (b.2.2.1, b.2.2.2)) s)]
  change (Matrix.mulVec (quraG1 d) (fun bb => k₀ bb.1 * M (bb.2.1, (bb.2.2, a.2.2.2)) s))
      (a.1, (a.2.1, a.2.2.1)) = k₀ a.1 * M (a.2.1, (a.2.2.1, a.2.2.2)) s
  rw [quraG1_mulVec_ket0 d (fun c : Fin d × Fin d => M (c.1, (c.2, a.2.2.2)) s)]

/-- Collapse the target-qudit sum in `G4⊗I`. -/
lemma quraG4_collapse_t (d : ℕ) [NeZero d] (t : ℝ) (a : Fin 2 × (Fin d × (Fin d × Fin d)))
    (v : Fin 2 × (Fin d × (Fin d × Fin d)) → ℂ) :
    (∑ b : Fin 2 × (Fin d × (Fin d × Fin d)),
        quraG4 d t (a.1, (a.2.1, a.2.2.1)) (b.1, (b.2.1, b.2.2.1)) *
            (if a.2.2.2 = b.2.2.2 then 1 else 0) * v b) =
      ∑ b : Fin 2 × (Fin d × Fin d),
        quraG4 d t (a.1, (a.2.1, a.2.2.1)) b * v (b.1, (b.2.1, (b.2.2, a.2.2.2))) := by
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro c1 hc1
  apply Finset.sum_congr rfl
  intro c2 hc2
  rw [Finset.sum_eq_single a.2.2.2]
  · rw [if_pos rfl]
    simp
  · intro t' ht hne
    rw [if_neg (fun hh => hne hh.symm)]
    simp
  · intro h
    exact False.elim (h (Finset.mem_univ a.2.2.2))

/-- The computational-basis ket `|i⟩`. -/
def quraKetI (i j : Fin 2) : ℂ := if i = j then 1 else 0

/-- `G4·(|i⟩|00⟩) = (R_y(t)|i⟩)|00⟩`. -/
lemma quraG4_mulVec_ket_i_ket00 (d : ℕ) [NeZero d] (t : ℝ) (i : Fin 2) :
    Matrix.mulVec (quraG4 d t)
        (fun a : Fin 2 × (Fin d × Fin d) => quraKetI i a.1 * quraKet00 d a.2) =
      fun a => Y[t] a.1 i * quraKet00 d a.2 := by
  ext a
  change (∑ b : Fin 2 × (Fin d × Fin d),
      quraG4 d t a b * (quraKetI i b.1 * quraKet00 d b.2)) =
    Y[t] a.1 i * quraKet00 d a.2
  have hsplit : (∑ b : Fin 2 × (Fin d × Fin d),
      quraG4 d t a b * (quraKetI i b.1 * quraKet00 d b.2)) =
      (∑ b : Fin 2 × (Fin d × Fin d),
        (Y[t] a.1 b.1 - (if a.1 = b.1 then 1 else 0)) * quraKet00 d a.2 *
          quraKet00 d b.2 * (quraKetI i b.1 * quraKet00 d b.2)) +
      (∑ b : Fin 2 × (Fin d × Fin d),
        (if a.1 = b.1 then 1 else 0) * (if a.2 = b.2 then 1 else 0) *
          (quraKetI i b.1 * quraKet00 d b.2)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    rw [quraG4]
    by_cases h1 : a.1 = b.1
    · by_cases h2 : a.2 = b.2
      · simp [h1, h2]
        ring
      · simp [h1, h2]
    · by_cases h2 : a.2 = b.2
      · simp [h1, h2]
      · simp [h1, h2]
  rw [hsplit]
  have h1 : (∑ b : Fin 2 × (Fin d × Fin d),
      (Y[t] a.1 b.1 - (if a.1 = b.1 then 1 else 0)) * quraKet00 d a.2 *
        quraKet00 d b.2 * (quraKetI i b.1 * quraKet00 d b.2)) =
      (Y[t] a.1 i - (if a.1 = i then 1 else 0)) * quraKet00 d a.2 := by
    rw [Finset.sum_eq_single (i, (0, 0))]
    · have hi : quraKetI i i = 1 := by simp [quraKetI]
      have hk00 : quraKet00 d (0, 0) = 1 := by simp [quraKet00]
      simp [hi, hk00]
    · intro b hb hne
      by_cases hb1 : b.1 = i
      · have hb2 : b.2 ≠ (0, 0) := by
          intro h
          apply hne
          apply Prod.ext
          · exact hb1
          · exact h
        have hk : quraKet00 d b.2 = 0 := by
          change (if b.2.1.val = 0 ∧ b.2.2.val = 0 then 1 else 0) = 0
          have hnot : ¬ (b.2.1.val = 0 ∧ b.2.2.val = 0) := by
            intro h
            apply hb2
            apply Prod.ext
            · exact Fin.ext h.1
            · exact Fin.ext h.2
          rw [if_neg hnot]
        rw [hk]
        simp
      · have hk : quraKetI i b.1 = 0 := by
          simp [quraKetI, show ¬(i = b.1) from fun h => hb1 h.symm]
        rw [hk]
        simp
    · intro h
      exact False.elim (h (Finset.mem_univ (i, (0, 0))))
  have h2 : (∑ b : Fin 2 × (Fin d × Fin d),
      (if a.1 = b.1 then 1 else 0) * (if a.2 = b.2 then 1 else 0) *
        (quraKetI i b.1 * quraKet00 d b.2)) =
      quraKetI i a.1 * quraKet00 d a.2 := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b hb hne
      by_cases hb1 : a.1 = b.1
      · have hb2 : a.2 ≠ b.2 := by
          intro h
          apply hne
          apply Prod.ext
          · exact hb1.symm
          · exact h.symm
        have hnot : ¬(a.2 = b.2) := hb2
        simp [hnot]
      · simp [hb1]
    · intro h
      exact False.elim (h (Finset.mem_univ a))
  rw [h1, h2]
  -- (R_y a.1 i - δ_{a.1,i} + ket_i i a.1)·ket00 a.2 = R_y a.1 i·ket00 a.2
  have hk : quraKetI i a.1 = (if i = a.1 then 1 else 0) := by rfl
  rw [hk]
  by_cases hai : i = a.1
  · rw [hai]
    simp
    ring
  · simp [hai, show ¬(a.1 = i) from fun h => hai h.symm]

end

end QuantumAlg.UnitaryReversal
