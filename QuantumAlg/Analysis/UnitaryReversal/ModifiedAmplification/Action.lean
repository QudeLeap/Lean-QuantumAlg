/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.State.Normalized

public import QuantumAlg.Analysis.UnitaryReversal.ModifiedAmplification.Construction

/-!
# Modified-amplifier action on the invariant subspace

Exact angle update for the matrix formula, with the real-domain assumptions
required for its square roots and inverse trigonometric functions
[CML+24, main.tex:1053].
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


local notation "Y[" t "]" => (quraRy t : Matrix (Fin 2) (Fin 2) ℂ)



/-- The computational-basis embedding `|i⟩ ⊗ M` into the ancilla register. -/
def quraKetIMat (i : Fin 2) (d : ℕ) (M : Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ) :
    Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin d) ℂ :=
  Matrix.of fun a s => quraKetI i a.1 * M (a.2.1, (a.2.2.1, a.2.2.2)) s

/-- `(G4⊗I)·(|i⟩⊗Λ₀) = (R_y(t)|i⟩)⊗Λ₀`. -/
lemma quraG4Tensor_mul_ket_i_lambda0 (d : ℕ) [NeZero d] (t : ℝ) (i : Fin 2) :
    quraG4Tensor d t * quraKetIMat i d (quraLambda0 d) =
      quraRyState t (quraLambda0 d) i := by
  ext a s
  rw [Matrix.mul_apply]
  change (∑ b : Fin 2 × (Fin d × (Fin d × Fin d)),
      quraG4 d t (a.1, (a.2.1, a.2.2.1)) (b.1, (b.2.1, b.2.2.1)) *
          (if a.2.2.2 = b.2.2.2 then 1 else 0) *
        (quraKetI i b.1 * quraLambda0 d (b.2.1, (b.2.2.1, b.2.2.2)) s)) =
      Y[t] a.1 i * quraLambda0 d (a.2.1, (a.2.2.1, a.2.2.2)) s
  rw [quraG4_collapse_t d t a (fun b =>
    quraKetI i b.1 * quraLambda0 d (b.2.1, (b.2.2.1, b.2.2.2)) s)]
  calc
    (∑ b : Fin 2 × (Fin d × Fin d),
        quraG4 d t (a.1, (a.2.1, a.2.2.1)) b *
          (quraKetI i b.1 * quraLambda0 d (b.2.1, (b.2.2, a.2.2.2)) s))
        = ∑ b : Fin 2 × (Fin d × Fin d),
            quraG4 d t (a.1, (a.2.1, a.2.2.1)) b *
              (quraKetI i b.1 * quraKet00 d (b.2.1, b.2.2)) * (if a.2.2.2 = s then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro b hb
          have hL : quraLambda0 d (b.2.1, (b.2.2, a.2.2.2)) s =
              quraKet00 d (b.2.1, b.2.2) * (if a.2.2.2 = s then 1 else 0) := by
            simp [quraLambda0, quraKet00]
          rw [hL]
          ring
    _ = (∑ b : Fin 2 × (Fin d × Fin d),
            quraG4 d t (a.1, (a.2.1, a.2.2.1)) b *
              (quraKetI i b.1 * quraKet00 d (b.2.1, b.2.2))) *
            (if a.2.2.2 = s then 1 else 0) := by
          rw [← Finset.sum_mul]
    _ = (Matrix.mulVec (quraG4 d t) (fun a => quraKetI i a.1 * quraKet00 d a.2))
            (a.1, (a.2.1, a.2.2.1)) * (if a.2.2.2 = s then 1 else 0) := by
          rfl
    _ = Y[t] a.1 i * quraLambda0 d (a.2.1, (a.2.2.1, a.2.2.2)) s := by
          rw [quraG4_mulVec_ket_i_ket00 d t i]
          change Y[t] a.1 i * quraKet00 d (a.2.1, a.2.2.1) * (if a.2.2.2 = s then 1 else 0) =
            Y[t] a.1 i * quraLambda0 d (a.2.1, (a.2.2.1, a.2.2.2)) s
          simp [quraLambda0, quraKet00]

/-- For `Λ⊥` (no `|00⟩` component), the `(R_y−1₂)⊗|00⟩⟨00|` part of `G4` vanishes. -/
lemma quraG4_scalar_lambdaPerp (d : ℕ) [NeZero d] (t : ℝ) (U : Matrix (Fin d) (Fin d) ℂ)
    (a : Fin 2 × (Fin d × (Fin d × Fin d))) (s : Fin d)
    (b : Fin 2 × (Fin d × Fin d)) :
    quraG4 d t (a.1, (a.2.1, a.2.2.1)) b *
        (k₀ b.1 * quraLambdaPerp d U (b.2.1, (b.2.2, a.2.2.2)) s) =
      (if a.1 = b.1 then 1 else 0) * (if (a.2.1, a.2.2.1) = b.2 then 1 else 0) *
        (k₀ b.1 * quraLambdaPerp d U (b.2.1, (b.2.2, a.2.2.2)) s) := by
  have hL : quraKet00 d (b.2.1, b.2.2) * quraLambdaPerp d U (b.2.1, (b.2.2, a.2.2.2)) s = 0 := by
    have h00 : quraLambdaPerp d U (0, (0, a.2.2.2)) s = 0 := quraLambdaPerp_00_zero d U s a.2.2.2
    by_cases hb00 : b.2.1 = 0 ∧ b.2.2 = 0
    · rw [hb00.1, hb00.2]
      simp [h00]
    · have hk : quraKet00 d (b.2.1, b.2.2) = 0 := by
        change (if b.2.1.val = 0 ∧ b.2.2.val = 0 then 1 else 0) = 0
        have hnot : ¬ (b.2.1.val = 0 ∧ b.2.2.val = 0) := by
          intro h
          apply hb00
          exact ⟨Fin.ext h.1, Fin.ext h.2⟩
        rw [if_neg hnot]
      rw [hk]
      simp
  calc
    quraG4 d t (a.1, (a.2.1, a.2.2.1)) b *
        (k₀ b.1 * quraLambdaPerp d U (b.2.1, (b.2.2, a.2.2.2)) s)
        = (((Y[t] a.1 b.1 - (if a.1 = b.1 then 1 else 0)) *
              quraKet00 d (a.2.1, a.2.2.1) * quraKet00 d (b.2.1, b.2.2)) +
            (if a.1 = b.1 then 1 else 0) * (if (a.2.1, a.2.2.1) = b.2 then 1 else 0)) *
            (k₀ b.1 * quraLambdaPerp d U (b.2.1, (b.2.2, a.2.2.2)) s) := by
          rfl
    _ = (Y[t] a.1 b.1 - (if a.1 = b.1 then 1 else 0)) * quraKet00 d (a.2.1, a.2.2.1) *
          (quraKet00 d (b.2.1, b.2.2) * quraLambdaPerp d U (b.2.1, (b.2.2, a.2.2.2)) s) *
            k₀ b.1 +
          (if a.1 = b.1 then 1 else 0) * (if (a.2.1, a.2.2.1) = b.2 then 1 else 0) *
            (k₀ b.1 * quraLambdaPerp d U (b.2.1, (b.2.2, a.2.2.2)) s) := by
          ring
    _ = (if a.1 = b.1 then 1 else 0) * (if (a.2.1, a.2.2.1) = b.2 then 1 else 0) *
          (k₀ b.1 * quraLambdaPerp d U (b.2.1, (b.2.2, a.2.2.2)) s) := by
          rw [hL]
          ring

/-- `(G4⊗I)·(|0⟩⊗Λ⊥) = |0⟩⊗Λ⊥` for the `|00⟩`-free matrix state `Λ⊥`. -/
lemma quraG4Tensor_mul_ket0_lambdaPerp (d : ℕ) [NeZero d] (t : ℝ)
    (U : Matrix (Fin d) (Fin d) ℂ) :
    quraG4Tensor d t * quraKet0Mat d (quraLambdaPerp d U) =
      quraKet0Mat d (quraLambdaPerp d U) := by
  ext a s
  rw [Matrix.mul_apply]
  change (∑ b : Fin 2 × (Fin d × (Fin d × Fin d)),
      quraG4 d t (a.1, (a.2.1, a.2.2.1)) (b.1, (b.2.1, b.2.2.1)) *
          (if a.2.2.2 = b.2.2.2 then 1 else 0) *
        (k₀ b.1 * quraLambdaPerp d U (b.2.1, (b.2.2.1, b.2.2.2)) s)) =
      k₀ a.1 * quraLambdaPerp d U (a.2.1, (a.2.2.1, a.2.2.2)) s
  rw [quraG4_collapse_t d t a (fun b =>
    k₀ b.1 * quraLambdaPerp d U (b.2.1, (b.2.2.1, b.2.2.2)) s)]
  calc
    (∑ b : Fin 2 × (Fin d × Fin d),
        quraG4 d t (a.1, (a.2.1, a.2.2.1)) b *
          (k₀ b.1 * quraLambdaPerp d U (b.2.1, (b.2.2, a.2.2.2)) s))
        = ∑ b : Fin 2 × (Fin d × Fin d),
            (if a.1 = b.1 then 1 else 0) * (if (a.2.1, a.2.2.1) = b.2 then 1 else 0) *
              (k₀ b.1 * quraLambdaPerp d U (b.2.1, (b.2.2, a.2.2.2)) s) := by
          apply Finset.sum_congr rfl
          intro b hb
          exact quraG4_scalar_lambdaPerp d t U a s b
    _ = k₀ a.1 * quraLambdaPerp d U (a.2.1, (a.2.2.1, a.2.2.2)) s := by
          rw [Finset.sum_eq_single (a.1, (a.2.1, a.2.2.1))]
          · simp
          · intro b hb hne
            by_cases h1 : a.1 = b.1
            · have h2 : (a.2.1, a.2.2.1) ≠ b.2 := by
                intro h
                apply hne
                apply Prod.ext
                · exact h1.symm
                · exact h.symm
              have hnot : ¬((a.2.1, a.2.2.1) = b.2) := h2
              simp [hnot]
            · simp [h1]
          · intro h
            exact False.elim (h (Finset.mem_univ (a.1, (a.2.1, a.2.2.1))))

/-- `quraKetI 0 = k₀` (the same computational-basis ket). -/
lemma quraKetI_zero (j : Fin 2) : quraKetI 0 j = k₀ j := by
  by_cases hj : j = 0
  · rw [hj]
    simp [quraKetI, NormalizedVector.ket_apply]
  · have hj0 : 0 ≠ j := fun h => hj h.symm
    simp [quraKetI, hj, hj0, NormalizedVector.ket_apply]

/-- `quraKetI 1 = k₁` (the same computational-basis ket). -/
lemma quraKetI_one (j : Fin 2) : quraKetI 1 j = k₁ j := by
  by_cases hj : j = 1
  · rw [hj]
    simp [quraKetI, NormalizedVector.ket_apply]
  · have hj0 : 1 ≠ j := fun h => hj h.symm
    simp [quraKetI, hj, hj0, NormalizedVector.ket_apply]

/-- `(G4⊗I)·(|0⟩⊗Λ0) = R_y(t)|0⟩⊗Λ0`. -/
lemma quraG4Tensor_mul_ket0_lambda0 (d : ℕ) [NeZero d] (t : ℝ) :
    quraG4Tensor d t * quraKet0Mat d (quraLambda0 d) = quraRyState t (quraLambda0 d) 0 := by
  simpa [quraKet0Mat, quraKetIMat, quraKetI_zero] using quraG4Tensor_mul_ket_i_lambda0 d t 0

/-- `(G4⊗I)·(|1⟩⊗Λ0) = R_y(t)|1⟩⊗Λ0`. -/
lemma quraG4Tensor_mul_ket1_lambda0 (d : ℕ) [NeZero d] (t : ℝ) :
    quraG4Tensor d t * quraKet1Mat d (quraLambda0 d) = quraRyState t (quraLambda0 d) 1 := by
  simpa [quraKet1Mat, quraKetIMat, quraKetI_one] using quraG4Tensor_mul_ket_i_lambda0 d t 1

/-- `R_y(−2·arctan(y/x))·(x|0⟩+y|1⟩)⊗M = √(x²+y²)·|0⟩⊗M` for `x > 0`. -/
lemma quraRyState_align (x y : ℝ) (hx : 0 < x)
    (M : Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ) :
    ((x : ℝ) : ℂ) • quraRyState (-2 * Real.arctan (y / x)) M 0 +
        ((y : ℝ) : ℂ) • quraRyState (-2 * Real.arctan (y / x)) M 1 =
      ((Real.sqrt (x ^ 2 + y ^ 2) : ℝ) : ℂ) • quraKet0Mat d M := by
  let t : ℝ := -2 * Real.arctan (y / x)
  ext a s
  change ((x : ℂ) * (Y[t] a.1 0 * M (a.2.1, (a.2.2.1, a.2.2.2)) s) +
      (y : ℂ) * (Y[t] a.1 1 * M (a.2.1, (a.2.2.1, a.2.2.2)) s)) =
    ((Real.sqrt (x ^ 2 + y ^ 2) : ℝ) : ℂ) * (k₀ a.1 * M (a.2.1, (a.2.2.1, a.2.2.2)) s)
  have h := congrFun (quraRy_mulVec_align x y hx) a.1
  have hc : (x : ℂ) * Y[t] a.1 0 + (y : ℂ) * Y[t] a.1 1 =
      (if a.1 = 0 then ((Real.sqrt (x ^ 2 + y ^ 2) : ℝ) : ℂ) else 0) := by
    have h' : Y[t] a.1 0 * (x : ℂ) + Y[t] a.1 1 * (y : ℂ) =
        (if a.1 = 0 then ((Real.sqrt (x ^ 2 + y ^ 2) : ℝ) : ℂ) else 0) := by
      simpa [t, Matrix.mulVec, Fin.sum_univ_two] using h
    rw [← h']
    ring
  calc
    (x : ℂ) * (Y[t] a.1 0 * M (a.2.1, (a.2.2.1, a.2.2.2)) s) +
        (y : ℂ) * (Y[t] a.1 1 * M (a.2.1, (a.2.2.1, a.2.2.2)) s)
        = ((x : ℂ) * Y[t] a.1 0 + (y : ℂ) * Y[t] a.1 1) *
            M (a.2.1, (a.2.2.1, a.2.2.2)) s := by
          ring
    _ = (if a.1 = 0 then ((Real.sqrt (x ^ 2 + y ^ 2) : ℝ) : ℂ) else 0) *
            M (a.2.1, (a.2.2.1, a.2.2.2)) s := by
          rw [hc]
    _ = ((Real.sqrt (x ^ 2 + y ^ 2) : ℝ) : ℂ) *
          (k₀ a.1 * M (a.2.1, (a.2.2.1, a.2.2.2)) s) := by
          by_cases ha : a.1 = 0
          · rw [ha]
            simp [NormalizedVector.ket_apply]
          · have hk : k₀ a.1 = 0 := by simp [ha, NormalizedVector.ket_apply]
            rw [hk]
            simp [ha]

/-- `(√(1−α²)·sinθ)² + cos²θ = 1 − (α·sinθ)²` for `α² ≤ 1`. -/
lemma quraS9_sqrt_sq (α θ : ℝ) (hα : α ^ 2 ≤ 1) :
    (Real.sqrt (1 - α ^ 2) * Real.sin θ) ^ 2 + Real.cos θ ^ 2 = 1 - (α * Real.sin θ) ^ 2 := by
  have h' : 0 ≤ 1 - α ^ 2 := by nlinarith
  rw [mul_pow, Real.sq_sqrt h']
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- `sin(arcsin(α·sinθ) + Δ_d) = √(1−(α·sinθ)²)·sinΔ_d + α·sinθ·cosΔ_d`. -/
lemma quraS9_sin (d : ℕ) (hd1 : 1 ≤ d) (α θ : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) :
    Complex.sin ((Real.arcsin (α * Real.sin θ) : ℂ) + quraTheta hd1) =
      ((Real.sqrt (1 - (α * Real.sin θ) ^ 2) : ℝ) : ℂ) * (1 / (d : ℂ)) +
        ((α * Real.sin θ : ℝ) : ℂ) * quraCosDelta d := by
  have hb : α * Real.sin θ ∈ Set.Icc (-1 : ℝ) 1 := by
    have hs := Real.sin_mem_Icc θ
    constructor
    · nlinarith [hs.1, hα0, hα1]
    · nlinarith [hs.2, hα0, hα1]
  rw [Complex.sin_add]
  rw [← Complex.ofReal_sin, ← Complex.ofReal_cos]
  rw [Real.sin_arcsin hb.1 hb.2, Real.cos_arcsin]
  rw [quraTheta_sin hd1, quraTheta_cos hd1]
  ring

/-- `cos(arcsin(α·sinθ) + Δ_d) = √(1−(α·sinθ)²)·cosΔ_d − α·sinθ·sinΔ_d`. -/
lemma quraS9_cos (d : ℕ) (hd1 : 1 ≤ d) (α θ : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) :
    Complex.cos ((Real.arcsin (α * Real.sin θ) : ℂ) + quraTheta hd1) =
      ((Real.sqrt (1 - (α * Real.sin θ) ^ 2) : ℝ) : ℂ) * quraCosDelta d -
        ((α * Real.sin θ : ℝ) : ℂ) * (1 / (d : ℂ)) := by
  have hb : α * Real.sin θ ∈ Set.Icc (-1 : ℝ) 1 := by
    have hs := Real.sin_mem_Icc θ
    constructor
    · nlinarith [hs.1, hα0, hα1]
    · nlinarith [hs.2, hα0, hα1]
  rw [Complex.cos_add]
  rw [← Complex.ofReal_sin, ← Complex.ofReal_cos]
  rw [Real.sin_arcsin hb.1 hb.2, Real.cos_arcsin]
  rw [quraTheta_sin hd1, quraTheta_cos hd1]

/-- Group a scalar combination of `|0⟩⊗Ψ0` and `|0⟩⊗Ψ⊥` by common state. -/
lemma quraSmul_group (c0 c1 c2 c3 c4 c5 : ℂ)
    (X Y : Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin d) ℂ) :
    c0 • (c1 • X + c2 • Y) + c3 • (c4 • X - c5 • Y) =
      (c0 * c1 + c3 * c4) • X + (c0 * c2 - c3 * c5) • Y := by
  ext a s
  simp [smul_eq_mul, sub_eq_add_neg]
  ring

/-- The `(X₂⊗D(U))` output in the Lemma S9 chain. -/
def quraS9State2 (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) (α θ : ℝ) :
    Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin d) ℂ :=
  (Real.sin θ : ℂ) •
      quraKet0Mat d (((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) • quraLambda0 d +
        (α : ℂ) • quraLambdaPerp d U) +
    (Real.cos θ : ℂ) • quraKet1Mat d (quraVecState d (quraKet00Perp d))

/-- The state after `G1 = |1⟩⟨1|⊗F† + |0⟩⟨0|⊗1` in the Lemma S9 chain. -/
def quraS9State3 (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) (α θ : ℝ) :
    Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin d) ℂ :=
  (Real.sin θ : ℂ) •
      quraKet0Mat d (((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) • quraLambda0 d +
        (α : ℂ) • quraLambdaPerp d U) +
    (Real.cos θ : ℂ) • quraKet1Mat d (quraLambda0 d)

/-- The state after `G4` (before `1₂⊗E(U)`) in the Lemma S9 chain. -/
def quraS9State4 (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) (α θ : ℝ) :
    Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin d) ℂ :=
  ((Real.sqrt (1 - (α * Real.sin θ) ^ 2) : ℝ) : ℂ) • quraKet0Mat d (quraLambda0 d) +
    ((α * Real.sin θ : ℝ) : ℂ) • quraKet0Mat d (quraLambdaPerp d U)

/-- `(A·B)⊗1 = (A⊗1)·(B⊗1)` on the (ancilla, two-qudit) register. -/
lemma quraTensor4_mul (d : ℕ)
    (A B : Matrix (Fin 2 × (Fin d × Fin d)) (Fin 2 × (Fin d × Fin d)) ℂ) :
    (Matrix.of fun (a b : Fin 2 × (Fin d × (Fin d × Fin d))) =>
        (A * B) (a.1, (a.2.1, a.2.2.1)) (b.1, (b.2.1, b.2.2.1)) *
        (if a.2.2.2 = b.2.2.2 then 1 else 0)) =
      (Matrix.of fun (a b : Fin 2 × (Fin d × (Fin d × Fin d))) =>
          A (a.1, (a.2.1, a.2.2.1)) (b.1, (b.2.1, b.2.2.1)) *
          (if a.2.2.2 = b.2.2.2 then 1 else 0)) *
        (Matrix.of fun (a b : Fin 2 × (Fin d × (Fin d × Fin d))) =>
          B (a.1, (a.2.1, a.2.2.1)) (b.1, (b.2.1, b.2.2.1)) *
          (if a.2.2.2 = b.2.2.2 then 1 else 0)) := by
  ext a b
  simp only [Matrix.mul_apply, Finset.sum_mul, Fintype.sum_prod_type]
  change (∑ i : Fin 2, ∑ j : Fin d, ∑ k : Fin d,
      (A (a.1, (a.2.1, a.2.2.1)) (i, (j, k)) * B (i, (j, k)) (b.1, (b.2.1, b.2.2.1))) *
        (if a.2.2.2 = b.2.2.2 then 1 else 0)) =
    (∑ i : Fin 2, ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d,
      (A (a.1, (a.2.1, a.2.2.1)) (i, (j, k)) * (if a.2.2.2 = l then 1 else 0)) *
        (B (i, (j, k)) (b.1, (b.2.1, b.2.2.1)) * (if l = b.2.2.2 then 1 else 0)))
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_eq_single a.2.2.2]
  · simp
  · intro l hl hne
    have h' : a.2.2.2 ≠ l := fun h => hne h.symm
    simp [h']
  · intro h
    exact False.elim (h (Finset.mem_univ a.2.2.2))

/-- `G''_α⊗1 = (G4⊗1)·(G1⊗1)`. -/
lemma quraGDoublePrimeTensor_eq (d : ℕ) [NeZero d] (α θ : ℝ) :
    quraGDoublePrimeTensor d α θ = quraG4Tensor d (quraAlphaT α θ) * quraG1Tensor d := by
  rw [quraGDoublePrimeTensor, quraG4Tensor, quraG1Tensor]
  rw [quraGDoublePrime]
  exact quraTensor4_mul d (quraG4 d (quraAlphaT α θ)) (quraG1 d)

/-- `(G1⊗I)` maps the `(X₂⊗D(U))` output to the state with `|1⟩⊗Λ0`. -/
lemma quraG1Tensor_mul_step2 (d : ℕ) [NeZero d] (hd : 2 ≤ d) (α θ : ℝ)
    (U : Matrix (Fin d) (Fin d) ℂ) :
    quraG1Tensor d * quraS9State2 d U α θ = quraS9State3 d U α θ := by
  rw [quraS9State2, quraS9State3]
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
  rw [quraG1Tensor_mul_ket0 d
    (((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) • quraLambda0 d + (α : ℂ) • quraLambdaPerp d U)]
  rw [quraG1Tensor_mul_ket1_ket00perp_I d hd]

/-- `(G4⊗I)` rotates the ancilla and kills the `|1⟩` component. -/
lemma quraG4Tensor_mul_state4 (d : ℕ) [NeZero d] (α θ : ℝ)
    (U : Matrix (Fin d) (Fin d) ℂ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ : 0 < Real.sin θ) :
    quraG4Tensor d (quraAlphaT α θ) * quraS9State3 d U α θ = quraS9State4 d U α θ := by
  rw [quraS9State3, quraS9State4]
  have hsplit : (Real.sin θ : ℂ) •
      quraKet0Mat d (((Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) • quraLambda0 d +
        (α : ℂ) • quraLambdaPerp d U) =
      ((Real.sin θ * Real.sqrt (1 - α ^ 2) : ℝ) : ℂ) • quraKet0Mat d (quraLambda0 d) +
        ((Real.sin θ * α : ℝ) : ℂ) • quraKet0Mat d (quraLambdaPerp d U) := by
    ext a s
    simp [quraKet0Mat, smul_eq_mul]
    ring
  rw [hsplit]
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul]
  rw [quraG4Tensor_mul_ket0_lambda0 d (quraAlphaT α θ)]
  rw [quraG4Tensor_mul_ket0_lambdaPerp d (quraAlphaT α θ) U]
  rw [quraG4Tensor_mul_ket1_lambda0 d (quraAlphaT α θ)]
  rw [show (Real.sin θ * Real.sqrt (1 - α ^ 2) : ℝ) = Real.sqrt (1 - α ^ 2) * Real.sin θ by ring]
  rw [show ((Real.sin θ * α : ℝ) : ℂ) • quraKet0Mat d (quraLambdaPerp d U) =
      ((α * Real.sin θ : ℝ) : ℂ) • quraKet0Mat d (quraLambdaPerp d U) by
    congr 1
    norm_cast
    ring]
  have hx : 0 < Real.sqrt (1 - α ^ 2) * Real.sin θ := by
    have hs0 : 0 < Real.sin θ := hθ
    have hsq : 0 < Real.sqrt (1 - α ^ 2) := by
      exact Real.sqrt_pos.mpr (by nlinarith [hα0, hα1])
    exact mul_pos hsq hs0
  have hry := quraRyState_align (Real.sqrt (1 - α ^ 2) * Real.sin θ) (Real.cos θ) hx (quraLambda0 d)
  rw [← quraAlphaT] at hry
  have hαsq : α ^ 2 ≤ 1 := by nlinarith [hα0, hα1]
  rw [quraS9_sqrt_sq α θ hαsq] at hry
  have hcomb := congrArg (fun X : Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin d) ℂ =>
      X + ((α * Real.sin θ : ℝ) : ℂ) • quraKet0Mat d (quraLambdaPerp d U)) hry
  rw [← hcomb]
  abel

/-- `(G''_α⊗I)` maps the `(X₂⊗D(U))` output to the rotated state. -/
lemma quraGDoublePrimeTensor_mul_step2 (d : ℕ) [NeZero d] (hd : 2 ≤ d) (α θ : ℝ)
    (U : Matrix (Fin d) (Fin d) ℂ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ : 0 < Real.sin θ) :
    quraGDoublePrimeTensor d α θ * quraS9State2 d U α θ = quraS9State4 d U α θ := by
  rw [quraGDoublePrimeTensor_eq d α θ]
  rw [Matrix.mul_assoc]
  rw [quraG1Tensor_mul_step2 d hd α θ U]
  rw [quraG4Tensor_mul_state4 d α θ U hα0 hα1 hθ]

/-- `(G'_α⊗I)` maps the input span state to the `(X₂⊗D(U))` input. -/
lemma quraGPrimeTensor_mul_ket0_psi0 (d : ℕ) [NeZero d] (hd : 2 ≤ d) (α : ℝ)
    (U : Matrix (Fin d) (Fin d) ℂ) :
    quraGPrimeTensor d α * quraKet0Mat d (quraPsi0 d U) = quraKet1Mat d (quraFαImage d α U) := by
  change quraGPrimeTensor d α *
      (Matrix.of fun (a : Fin 2 × (Fin d × (Fin d × Fin d))) (s : Fin d) =>
      k₀ a.1 * (quraKet00 d (a.2.1, a.2.2.1) * U.conjTranspose a.2.2.2 s)) =
    quraKet1Mat d (quraFαImage d α U)
  rw [quraGPrimeTensor_mul_ket0_ket00_U d hd α U]
  simp [quraKet1Mat, quraFαImage, mul_assoc]

/-- `(G'_α⊗I)·(|0⟩⊗M) = |0⟩⊗M` for a `|00⟩`-free `M`. -/
lemma quraGPrimeTensor_mul_ket0_of_perp (d : ℕ) [NeZero d]
    (α : ℝ) (M : Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ)
    (hM : ∀ s t, M (0, (0, t)) s = 0) :
    quraGPrimeTensor d α * quraKet0Mat d M = quraKet0Mat d M := by
  ext a s
  rw [Matrix.mul_apply]
  change (∑ b : Fin 2 × (Fin d × (Fin d × Fin d)),
      quraGPrime d α (a.1, (a.2.1, a.2.2.1)) (b.1, (b.2.1, b.2.2.1)) *
          (if a.2.2.2 = b.2.2.2 then 1 else 0) *
        (k₀ b.1 * M (b.2.1, (b.2.2.1, b.2.2.2)) s)) =
      k₀ a.1 * M (a.2.1, (a.2.2.1, a.2.2.2)) s
  rw [quraGPrime_collapse_t d α a (fun b => k₀ b.1 * M (b.2.1, (b.2.2.1, b.2.2.2)) s)]
  change (Matrix.mulVec (quraGPrime d α)
      (fun bb => k₀ bb.1 * M (bb.2.1, (bb.2.2, a.2.2.2)) s))
      (a.1, (a.2.1, a.2.2.1)) = k₀ a.1 * M (a.2.1, (a.2.2.1, a.2.2.2)) s
  rw [quraGPrime_mulVec_ket0_of_perp d α
    (fun c : Fin d × Fin d => M (c.1, (c.2, a.2.2.2)) s) (hM s a.2.2.2)]

/-- `(G'_α⊗I)` maps the input span state to the `(X₂⊗D(U))` input. -/
lemma quraGPrimeTensor_mul_span (d : ℕ) [NeZero d] (hd : 2 ≤ d) (α θ : ℝ)
    (U : Matrix (Fin d) (Fin d) ℂ) :
    quraGPrimeTensor d α * ((Real.sin θ : ℂ) • quraKet0Mat d (quraPsi0 d U) +
        (Real.cos θ : ℂ) • quraKet0Mat d (quraPsiPerp d U)) =
      (Real.sin θ : ℂ) • quraKet1Mat d (quraFαImage d α U) +
        (Real.cos θ : ℂ) • quraKet0Mat d (quraPsiPerp d U) := by
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
  rw [quraGPrimeTensor_mul_ket0_psi0 d hd α U]
  rw [quraGPrimeTensor_mul_ket0_of_perp d α (quraPsiPerp d U)
    (by intro s t; exact quraPsiPerp_00_zero d U s t)]

/-- Step 1+2: `(X₂⊗D(U))·(G'_α⊗I)` on the input span state. -/
lemma quraStep12 (d : ℕ) [NeZero d] (hd : 2 ≤ d) (α θ : ℝ)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quraX2D d U * (quraGPrimeTensor d α * ((Real.sin θ : ℂ) • quraKet0Mat d (quraPsi0 d U) +
        (Real.cos θ : ℂ) • quraKet0Mat d (quraPsiPerp d U))) = quraS9State2 d U α θ := by
  rw [quraS9State2]
  rw [quraGPrimeTensor_mul_span d hd α θ U]
  exact quraX2D_mul_GPrimeOut d α θ U hU

/-- `(1₂⊗E(U))·(|0⟩⊗Λ⊥) = cosΔ_d·|0⟩⊗Ψ0 − sinΔ_d·|0⟩⊗Ψ⊥`. -/
lemma quraI2E_mul_ket0_lambdaPerp (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quraI2E d U * quraKet0Mat d (quraLambdaPerp d U) =
      quraCosDelta d • quraKet0Mat d (quraPsi0 d U) -
        (1 / (d : ℂ)) • quraKet0Mat d (quraPsiPerp d U) := by
  rw [show quraKet0Mat d (quraLambdaPerp d U) =
      Matrix.of fun (a : Fin 2 × (Fin d × (Fin d × Fin d))) (s : Fin d) =>
        k₀ a.1 * (quraLambdaPerp d U (a.2.1, (a.2.2.1, a.2.2.2)) s) by rfl]
  rw [quraI2E_mul_ket0]
  rw [E_LambdaPerp_decompose hd U hU]
  ext a s
  simp [quraKet0Mat, smul_eq_mul, sub_eq_add_neg, mul_add]
  ring

/-- Step 4: `(1₂⊗E(U))` on the rotated state (paper Eqs. A.96–A.98). -/
lemma quraStep4 (d : ℕ) [NeZero d] (hd : 2 ≤ d) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (α θ : ℝ) :
    quraI2E d U * quraS9State4 d U α θ =
      ((Real.sqrt (1 - (α * Real.sin θ) ^ 2) : ℝ) : ℂ) •
          ((1 / (d : ℂ)) • quraKet0Mat d (quraPsi0 d U) +
            quraCosDelta d • quraKet0Mat d (quraPsiPerp d U)) +
        ((α * Real.sin θ : ℝ) : ℂ) •
          (quraCosDelta d • quraKet0Mat d (quraPsi0 d U) -
            (1 / (d : ℂ)) • quraKet0Mat d (quraPsiPerp d U)) := by
  rw [quraS9State4]
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
  rw [quraI2E_mul_ket0_lambda0 d hd U]
  rw [quraI2E_mul_ket0_lambdaPerp d hd U hU]
  rw [quraEncodedState]

/-- Lemma S9: the modified amplifier `A_α,θ(U)` rotates the `{Ψ0, Ψ⊥}` span by
`θ′ = arcsin(α·sinθ) + Δ_d`. -/
lemma quraModifiedAmplifier_mul_ket0_span (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (α θ : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ : 0 < Real.sin θ) :
    quraModifiedAmplifier d U α θ *
        ((Real.sin θ : ℂ) • quraKet0Mat d (quraPsi0 d U) +
          (Real.cos θ : ℂ) • quraKet0Mat d (quraPsiPerp d U)) =
      Complex.sin ((Real.arcsin (α * Real.sin θ) : ℂ) + quraTheta (by omega : 1 ≤ d)) •
          quraKet0Mat d (quraPsi0 d U) +
        Complex.cos ((Real.arcsin (α * Real.sin θ) : ℂ) + quraTheta (by omega : 1 ≤ d)) •
          quraKet0Mat d (quraPsiPerp d U) := by
  calc
    quraModifiedAmplifier d U α θ *
        ((Real.sin θ : ℂ) • quraKet0Mat d (quraPsi0 d U) +
          (Real.cos θ : ℂ) • quraKet0Mat d (quraPsiPerp d U))
        = quraI2E d U * (quraGDoublePrimeTensor d α θ *
            (quraX2D d U * (quraGPrimeTensor d α *
              ((Real.sin θ : ℂ) • quraKet0Mat d (quraPsi0 d U) +
                (Real.cos θ : ℂ) • quraKet0Mat d (quraPsiPerp d U))))) := by
          rw [quraModifiedAmplifier]
          simp only [Matrix.mul_assoc]
    _ = quraI2E d U * (quraGDoublePrimeTensor d α θ * quraS9State2 d U α θ) := by
          rw [quraStep12 d hd α θ U hU]
    _ = quraI2E d U * quraS9State4 d U α θ := by
          rw [quraGDoublePrimeTensor_mul_step2 d hd α θ U hα0 hα1 hθ]
    _ = ((Real.sqrt (1 - (α * Real.sin θ) ^ 2) : ℝ) : ℂ) •
            ((1 / (d : ℂ)) • quraKet0Mat d (quraPsi0 d U) +
              quraCosDelta d • quraKet0Mat d (quraPsiPerp d U)) +
          ((α * Real.sin θ : ℝ) : ℂ) •
            (quraCosDelta d • quraKet0Mat d (quraPsi0 d U) -
              (1 / (d : ℂ)) • quraKet0Mat d (quraPsiPerp d U)) := by
          rw [quraStep4 d hd U hU α θ]
    _ = (((Real.sqrt (1 - (α * Real.sin θ) ^ 2) : ℝ) : ℂ) * (1 / (d : ℂ)) +
            ((α * Real.sin θ : ℝ) : ℂ) * quraCosDelta d) •
          quraKet0Mat d (quraPsi0 d U) +
        ((((Real.sqrt (1 - (α * Real.sin θ) ^ 2) : ℝ) : ℂ) * quraCosDelta d -
            ((α * Real.sin θ : ℝ) : ℂ) * (1 / (d : ℂ)))) •
          quraKet0Mat d (quraPsiPerp d U) := by
          rw [quraSmul_group ((Real.sqrt (1 - (α * Real.sin θ) ^ 2) : ℝ) : ℂ) (1 / (d : ℂ))
              (quraCosDelta d) ((α * Real.sin θ : ℝ) : ℂ) (quraCosDelta d) (1 / (d : ℂ))
              (quraKet0Mat d (quraPsi0 d U)) (quraKet0Mat d (quraPsiPerp d U))]
    _ = Complex.sin ((Real.arcsin (α * Real.sin θ) : ℂ) + quraTheta (by omega : 1 ≤ d)) •
          quraKet0Mat d (quraPsi0 d U) +
        Complex.cos ((Real.arcsin (α * Real.sin θ) : ℂ) + quraTheta (by omega : 1 ≤ d)) •
          quraKet0Mat d (quraPsiPerp d U) := by
          rw [quraS9_sin d (by omega : 1 ≤ d) α θ hα0 hα1]
          rw [quraS9_cos d (by omega : 1 ≤ d) α θ hα0 hα1]
end

end QuantumAlg.UnitaryReversal
