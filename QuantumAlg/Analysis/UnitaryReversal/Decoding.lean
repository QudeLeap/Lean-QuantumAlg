/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.State.Normalized

public import QuantumAlg.Analysis.UnitaryReversal.Ancilla

/-!
# Decoder action on the amplification subspaces

The tensor decoder sends the two distinguished subspaces to their claimed
images [CML+24, main.tex:960]. These are matrix-action identities.
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


local notation "X₂" => (quraX2 : Matrix (Fin 2) (Fin 2) ℂ)

/-- `G ⊗ I` on the ancilla-plus-two-qudits register and the target qudit. -/
def quraGTensor (d : ℕ) :
    Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin 2 × (Fin d × (Fin d × Fin d))) ℂ :=
  Matrix.of fun a b =>
    quraG d (a.1, (a.2.1, a.2.2.1)) (b.1, (b.2.1, b.2.2.1)) * (if a.2.2.2 = b.2.2.2 then 1 else 0)

/-- `G† ⊗ I` on the ancilla-plus-two-qudits register and the target qudit. -/
def quraGConjTensor (d : ℕ) :
    Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin 2 × (Fin d × (Fin d × Fin d))) ℂ :=
  Matrix.of fun a b =>
    (quraG d).conjTranspose (a.1, (a.2.1, a.2.2.1)) (b.1, (b.2.1, b.2.2.1)) *
      (if a.2.2.2 = b.2.2.2 then 1 else 0)

/-- `X₂ ⊗ D(U)` on the ancilla qubit and the three-qudit register. -/
def quraX2D (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin 2 × (Fin d × (Fin d × Fin d))) ℂ :=
  Matrix.of fun a b =>
    X₂ a.1 b.1 * quraDecoder U (a.2.1, (a.2.2.1, a.2.2.2)) (b.2.1, (b.2.2.1, b.2.2.2))

/-- The dual decoder `D̃(U) = (G†⊗I)·(X₂⊗D(U))·(G⊗I)` (paper Eq. `eqn:G and D`). -/
def quraTildeD (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin 2 × (Fin d × (Fin d × Fin d))) ℂ :=
  quraGConjTensor d * quraX2D d U * quraGTensor d

/-- The matrix state `|00⊥⟩⊗U†`. -/
def quraKet00PerpU (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ :=
  Matrix.of fun a s => quraKet00Perp d (a.1, a.2.1) * U.conjTranspose a.2.2 s

/-- `X₂|0⟩ = |1⟩` in sum form. -/
lemma quraX2_sum_ket0 (a1 : Fin 2) :
    (∑ i : Fin 2, X₂ a1 i * k₀ i) = k₁ a1 := by
  fin_cases a1 <;> simp [quraX2, NormalizedVector.ket_apply]

/-- `X₂|1⟩ = |0⟩` in sum form. -/
lemma quraX2_sum_ket1 (a1 : Fin 2) :
    (∑ i : Fin 2, X₂ a1 i * k₁ i) = k₀ a1 := by
  fin_cases a1 <;> simp [quraX2, NormalizedVector.ket_apply]

/-- `(G⊗I)·(|0⟩⊗(|00⟩⊗U†)) = |1⟩⊗(|00⊥⟩⊗U†)`. -/
lemma quraGTensor_mul_ket0_ket00_U (d : ℕ) [NeZero d] (U : Matrix (Fin d) (Fin d) ℂ) :
    quraGTensor d * (Matrix.of fun a s =>
        k₀ a.1 * (quraKet00 d (a.2.1, a.2.2.1) * U.conjTranspose a.2.2.2 s)) =
      Matrix.of fun a s =>
        k₁ a.1 * (quraKet00Perp d (a.2.1, a.2.2.1) * U.conjTranspose a.2.2.2 s) := by
  ext a s
  rw [Matrix.mul_apply]
  change (∑ b : Fin 2 × (Fin d × (Fin d × Fin d)),
      quraG d (a.1, (a.2.1, a.2.2.1)) (b.1, (b.2.1, b.2.2.1)) * (if a.2.2.2 = b.2.2.2 then 1 else
      0) *
        (k₀ b.1 * (quraKet00 d (b.2.1, b.2.2.1) * U.conjTranspose b.2.2.2 s))) =
      k₁ a.1 * (quraKet00Perp d (a.2.1, a.2.2.1) * U.conjTranspose a.2.2.2 s)
  have hG00 : quraG d (a.1, (a.2.1, a.2.2.1)) (0, (0, 0)) * k₀ 0 * quraKet00 d (0, 0) =
      quraV1perp d (a.1, (a.2.1, a.2.2.1)) := by
    have hcol : (Matrix.mulVec (quraG d) (quraV00 d)) (a.1, (a.2.1, a.2.2.1)) =
        quraG d (a.1, (a.2.1, a.2.2.1)) (0, (0, 0)) * quraV00 d (0, (0, 0)) := by
      rw [Matrix.mulVec]
      change (∑ b : Fin 2 × (Fin d × Fin d), quraG d (a.1, (a.2.1, a.2.2.1)) b * quraV00 d b) =
        quraG d (a.1, (a.2.1, a.2.2.1)) (0, (0, 0)) * quraV00 d (0, (0, 0))
      rw [Finset.sum_eq_single (0, (0, 0))]
      · -- h₀: b ≠ (0,(0,0)) → summand = 0
        intro b hb hne
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
      · -- h₁: (0,(0,0)) ∈ univ
        intro h
        exact False.elim (h (Finset.mem_univ (0, (0, 0))))
    calc
      quraG d (a.1, (a.2.1, a.2.2.1)) (0, (0, 0)) * k₀ 0 * quraKet00 d (0, 0)
          = quraG d (a.1, (a.2.1, a.2.2.1)) (0, (0, 0)) * quraV00 d (0, (0, 0)) := by
            rw [show quraV00 d (0, (0, 0)) = k₀ 0 * quraKet00 d (0, 0) by rfl]
            ring
      _ = (Matrix.mulVec (quraG d) (quraV00 d)) (a.1, (a.2.1, a.2.2.1)) := by
            rw [← hcol]
      _ = quraV1perp d (a.1, (a.2.1, a.2.2.1)) := by
            rw [quraG_mulVec_ket0_ket00]
  rw [Finset.sum_eq_single (0, (0, (0, a.2.2.2)))]
  · -- main
    calc
      quraG d (a.1, (a.2.1, a.2.2.1)) (0, (0, 0)) *
            (if a.2.2.2 = a.2.2.2 then 1 else 0) *
            (k₀ 0 * (quraKet00 d (0, 0) * U.conjTranspose a.2.2.2 s))
          = quraG d (a.1, (a.2.1, a.2.2.1)) (0, (0, 0)) * 1 *
            (k₀ 0 * (quraKet00 d (0, 0) * U.conjTranspose a.2.2.2 s)) := by
            rw [if_pos rfl]
      _ = (quraG d (a.1, (a.2.1, a.2.2.1)) (0, (0, 0)) * k₀ 0 * quraKet00 d (0, 0)) *
            U.conjTranspose a.2.2.2 s := by
            ring
      _ = quraV1perp d (a.1, (a.2.1, a.2.2.1)) * U.conjTranspose a.2.2.2 s := by
            rw [hG00]
      _ = k₁ a.1 * (quraKet00Perp d (a.2.1, a.2.2.1) * U.conjTranspose a.2.2.2 s) := by
            rw [show quraV1perp d (a.1, (a.2.1, a.2.2.1)) =
              k₁ a.1 * quraKet00Perp d (a.2.1, a.2.2.1) by rfl]
            ring
  · -- h₀: b ≠ (0,(0,(0,a.2.2.2))) → summand = 0
    intro b hb hne
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
  · -- h₁: the singleton is in univ
    intro h
    exact False.elim (h (Finset.mem_univ (0, (0, (0, a.2.2.2)))))

/-- `(X₂⊗D(U))·(|0⟩⊗M) = |1⟩⊗(D(U)·M)`. -/
lemma quraX2D_mul_ket0 (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ)
    (M : Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ) :
    quraX2D d U * (Matrix.of fun a s => k₀ a.1 * M (a.2.1, (a.2.2.1, a.2.2.2)) s) =
      Matrix.of fun a s => k₁ a.1 * (quraDecoder U * M) (a.2.1, (a.2.2.1, a.2.2.2)) s := by
  ext a s
  rw [Matrix.mul_apply]
  change (∑ b : Fin 2 × (Fin d × (Fin d × Fin d)),
      X₂ a.1 b.1 * quraDecoder U (a.2.1, (a.2.2.1, a.2.2.2)) b.2 *
        (k₀ b.1 * M b.2 s)) =
      k₁ a.1 * (quraDecoder U * M) (a.2.1, (a.2.2.1, a.2.2.2)) s
  calc
    (∑ b : Fin 2 × (Fin d × (Fin d × Fin d)),
        X₂ a.1 b.1 * quraDecoder U (a.2.1, (a.2.2.1, a.2.2.2)) b.2 *
          (k₀ b.1 * M b.2 s))
        = ∑ i : Fin 2, ∑ c : Fin d × (Fin d × Fin d),
            X₂ a.1 i * quraDecoder U (a.2.1, (a.2.2.1, a.2.2.2)) c *
              (k₀ i * M c s) := by
          rw [Fintype.sum_prod_type]
    _ = ∑ i : Fin 2, ∑ c : Fin d × (Fin d × Fin d),
            (X₂ a.1 i * k₀ i) * (quraDecoder U (a.2.1, (a.2.2.1, a.2.2.2)) c * M c s) :=
            by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro c hc
          ring
    _ = ∑ i : Fin 2, (X₂ a.1 i * k₀ i) *
            (∑ c : Fin d × (Fin d × Fin d), quraDecoder U (a.2.1, (a.2.2.1, a.2.2.2)) c * M c s) :=
            by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← Finset.mul_sum]
    _ = (∑ i : Fin 2, X₂ a.1 i * k₀ i) *
            (∑ c : Fin d × (Fin d × Fin d), quraDecoder U (a.2.1, (a.2.2.1, a.2.2.2)) c * M c s) :=
            by
          rw [← Finset.sum_mul]
    _ = k₁ a.1 * (∑ c : Fin d × (Fin d × Fin d),
            quraDecoder U (a.2.1, (a.2.2.1, a.2.2.2)) c * M c s) := by
          rw [quraX2_sum_ket0]
    _ = k₁ a.1 * (quraDecoder U * M) (a.2.1, (a.2.2.1, a.2.2.2)) s := by
          rw [Matrix.mul_apply]

/-- `(X₂⊗D(U))·(|1⟩⊗M) = |0⟩⊗(D(U)·M)`. -/
lemma quraX2D_mul_ket1 (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ)
    (M : Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ) :
    quraX2D d U * (Matrix.of fun a s => k₁ a.1 * M (a.2.1, (a.2.2.1, a.2.2.2)) s) =
      Matrix.of fun a s => k₀ a.1 * (quraDecoder U * M) (a.2.1, (a.2.2.1, a.2.2.2)) s := by
  ext a s
  rw [Matrix.mul_apply]
  change (∑ b : Fin 2 × (Fin d × (Fin d × Fin d)),
      X₂ a.1 b.1 * quraDecoder U (a.2.1, (a.2.2.1, a.2.2.2)) b.2 *
        (k₁ b.1 * M b.2 s)) =
      k₀ a.1 * (quraDecoder U * M) (a.2.1, (a.2.2.1, a.2.2.2)) s
  calc
    (∑ b : Fin 2 × (Fin d × (Fin d × Fin d)),
        X₂ a.1 b.1 * quraDecoder U (a.2.1, (a.2.2.1, a.2.2.2)) b.2 *
          (k₁ b.1 * M b.2 s))
        = ∑ i : Fin 2, ∑ c : Fin d × (Fin d × Fin d),
            X₂ a.1 i * quraDecoder U (a.2.1, (a.2.2.1, a.2.2.2)) c *
              (k₁ i * M c s) := by
          rw [Fintype.sum_prod_type]
    _ = ∑ i : Fin 2, ∑ c : Fin d × (Fin d × Fin d),
            (X₂ a.1 i * k₁ i) * (quraDecoder U (a.2.1, (a.2.2.1, a.2.2.2)) c * M c s) :=
            by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro c hc
          ring
    _ = ∑ i : Fin 2, (X₂ a.1 i * k₁ i) *
            (∑ c : Fin d × (Fin d × Fin d), quraDecoder U (a.2.1, (a.2.2.1, a.2.2.2)) c * M c s) :=
            by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← Finset.mul_sum]
    _ = (∑ i : Fin 2, X₂ a.1 i * k₁ i) *
            (∑ c : Fin d × (Fin d × Fin d), quraDecoder U (a.2.1, (a.2.2.1, a.2.2.2)) c * M c s) :=
            by
          rw [← Finset.sum_mul]
    _ = k₀ a.1 * (∑ c : Fin d × (Fin d × Fin d),
            quraDecoder U (a.2.1, (a.2.2.1, a.2.2.2)) c * M c s) := by
          rw [quraX2_sum_ket1]
    _ = k₀ a.1 * (quraDecoder U * M) (a.2.1, (a.2.2.1, a.2.2.2)) s := by
          rw [Matrix.mul_apply]

/-- Collapse the target-qudit sum in `G⊗I`: only `b.2.2.2 = a.2.2.2` survives. -/
lemma quraG_collapse_t (d : ℕ) (a : Fin 2 × (Fin d × (Fin d × Fin d)))
    (v : Fin 2 × (Fin d × (Fin d × Fin d)) → ℂ) :
    (∑ b : Fin 2 × (Fin d × (Fin d × Fin d)),
        quraG d (a.1, (a.2.1, a.2.2.1)) (b.1, (b.2.1, b.2.2.1)) * (if a.2.2.2 = b.2.2.2 then 1 else
        0) * v b) =
      ∑ b : Fin 2 × (Fin d × Fin d),
        quraG d (a.1, (a.2.1, a.2.2.1)) b * v (b.1, (b.2.1, (b.2.2, a.2.2.2))) := by
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

/-- Collapse the target-qudit sum in `G†⊗I`: only `b.2.2.2 = a.2.2.2` survives. -/
lemma quraGConj_collapse_t (d : ℕ) (a : Fin 2 × (Fin d × (Fin d × Fin d)))
    (v : Fin 2 × (Fin d × (Fin d × Fin d)) → ℂ) :
    (∑ b : Fin 2 × (Fin d × (Fin d × Fin d)),
        (quraG d).conjTranspose (a.1, (a.2.1, a.2.2.1)) (b.1, (b.2.1, b.2.2.1)) *
          (if a.2.2.2 = b.2.2.2 then 1 else 0) * v b) =
      ∑ b : Fin 2 × (Fin d × Fin d),
        (quraG d).conjTranspose (a.1, (a.2.1, a.2.2.1)) b * v (b.1, (b.2.1, (b.2.2, a.2.2.2))) := by
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

/-- `(G⊗I)·(|0⟩⊗M) = |0⟩⊗M` when each column of `M` has no `|00⟩` component. -/
lemma quraGTensor_mul_ket0_of_perp (d : ℕ) [NeZero d]
    (M : Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ)
    (hM : ∀ s t, M (0, (0, t)) s = 0) :
    quraGTensor d * (Matrix.of fun a s => k₀ a.1 * M (a.2.1, (a.2.2.1, a.2.2.2)) s) =
      Matrix.of fun a s => k₀ a.1 * M (a.2.1, (a.2.2.1, a.2.2.2)) s := by
  ext a s
  rw [Matrix.mul_apply]
  change (∑ b : Fin 2 × (Fin d × (Fin d × Fin d)),
      quraG d (a.1, (a.2.1, a.2.2.1)) (b.1, (b.2.1, b.2.2.1)) * (if a.2.2.2 = b.2.2.2 then 1 else
      0) *
        (k₀ b.1 * M (b.2.1, (b.2.2.1, b.2.2.2)) s)) =
      k₀ a.1 * M (a.2.1, (a.2.2.1, a.2.2.2)) s
  rw [quraG_collapse_t d a (fun b => k₀ b.1 * M (b.2.1, (b.2.2.1, b.2.2.2)) s)]
  change (Matrix.mulVec (quraG d) (fun bb => k₀ bb.1 * M (bb.2.1, (bb.2.2, a.2.2.2)) s))
      (a.1, (a.2.1, a.2.2.1)) = k₀ a.1 * M (a.2.1, (a.2.2.1, a.2.2.2)) s
  rw [quraG_mulVec_ket0_of_perp d (fun c : Fin d × Fin d => M (c.1, (c.2, a.2.2.2)) s)]
  · dsimp
    exact hM s a.2.2.2

/-- `(G†⊗I)·(|0⟩⊗M) = |0⟩⊗M` when each column of `M` has no `|00⟩` component. -/
lemma quraGConjTensor_mul_ket0_of_perp (d : ℕ) [NeZero d]
    (M : Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ)
    (hM : ∀ s t, M (0, (0, t)) s = 0) :
    quraGConjTensor d * (Matrix.of fun a s => k₀ a.1 * M (a.2.1, (a.2.2.1, a.2.2.2)) s) =
      Matrix.of fun a s => k₀ a.1 * M (a.2.1, (a.2.2.1, a.2.2.2)) s := by
  ext a s
  rw [Matrix.mul_apply]
  change (∑ b : Fin 2 × (Fin d × (Fin d × Fin d)),
      (quraG d).conjTranspose (a.1, (a.2.1, a.2.2.1)) (b.1, (b.2.1, b.2.2.1)) *
        (if a.2.2.2 = b.2.2.2 then 1 else 0) *
        (k₀ b.1 * M (b.2.1, (b.2.2.1, b.2.2.2)) s)) =
      k₀ a.1 * M (a.2.1, (a.2.2.1, a.2.2.2)) s
  rw [quraGConj_collapse_t d a (fun b => k₀ b.1 * M (b.2.1, (b.2.2.1, b.2.2.2)) s)]
  change (Matrix.mulVec (quraG d).conjTranspose (fun bb => k₀ bb.1 * M (bb.2.1, (bb.2.2,
  a.2.2.2)) s))
      (a.1, (a.2.1, a.2.2.1)) = k₀ a.1 * M (a.2.1, (a.2.2.1, a.2.2.2)) s
  rw [quraG_conjTranspose_ket0_of_perp d (fun c : Fin d × Fin d => M (c.1, (c.2, a.2.2.2)) s)]
  · dsimp
    exact hM s a.2.2.2

/-- `(G†⊗I)·(|1⟩⊗(|00⊥⟩⊗I)) = |0⟩⊗(|00⟩⊗I)`. -/
lemma quraGConjTensor_mul_ket1_ket00perp_I (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    quraGConjTensor d * (Matrix.of fun a s =>
        k₁ a.1 * (quraKet00Perp d (a.2.1, a.2.2.1) * (if a.2.2.2 = s then 1 else 0))) =
      ((Matrix.of fun a s =>
        k₀ a.1 * (quraKet00 d (a.2.1, a.2.2.1) * (if a.2.2.2 = s then 1 else 0))) :
          Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin d) ℂ) := by
  ext a s
  rw [Matrix.mul_apply]
  change (∑ b : Fin 2 × (Fin d × (Fin d × Fin d)),
      (quraG d).conjTranspose (a.1, (a.2.1, a.2.2.1)) (b.1, (b.2.1, b.2.2.1)) *
        (if a.2.2.2 = b.2.2.2 then 1 else 0) *
        (k₁ b.1 * (quraKet00Perp d (b.2.1, b.2.2.1) * (if b.2.2.2 = s then 1 else 0)))) =
      k₀ a.1 * (quraKet00 d (a.2.1, a.2.2.1) * (if a.2.2.2 = s then 1 else 0))
  rw [quraGConj_collapse_t d a
    (fun b => k₁ b.1 * (quraKet00Perp d (b.2.1, b.2.2.1) * (if b.2.2.2 = s then 1 else 0)))]
  calc
    (∑ b : Fin 2 × (Fin d × Fin d),
        (quraG d).conjTranspose (a.1, (a.2.1, a.2.2.1)) b *
          (k₁ b.1 * (quraKet00Perp d (b.2.1, b.2.2) * (if a.2.2.2 = s then 1 else 0))))
        = ∑ b : Fin 2 × (Fin d × Fin d),
            (quraG d).conjTranspose (a.1, (a.2.1, a.2.2.1)) b *
              (k₁ b.1 * quraKet00Perp d (b.2.1, b.2.2)) * (if a.2.2.2 = s then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro b hb
          ring
    _ = (∑ b : Fin 2 × (Fin d × Fin d),
            (quraG d).conjTranspose (a.1, (a.2.1, a.2.2.1)) b *
              (k₁ b.1 * quraKet00Perp d (b.2.1, b.2.2))) *
            (if a.2.2.2 = s then 1 else 0) := by
          rw [← Finset.sum_mul]
    _ = (Matrix.mulVec (quraG d).conjTranspose (quraV1perp d)) (a.1, (a.2.1, a.2.2.1)) *
            (if a.2.2.2 = s then 1 else 0) := by
          change (∑ b : Fin 2 × (Fin d × Fin d),
              (quraG d).conjTranspose (a.1, (a.2.1, a.2.2.1)) b * (quraV1perp d b)) *
                (if a.2.2.2 = s then 1 else 0) =
              (Matrix.mulVec (quraG d).conjTranspose (quraV1perp d)) (a.1, (a.2.1, a.2.2.1)) *
                (if a.2.2.2 = s then 1 else 0)
          rfl
    _ = k₀ a.1 * (quraKet00 d (a.2.1, a.2.2.1) * (if a.2.2.2 = s then 1 else 0)) := by
          rw [quraG_conjTranspose_ket1_ket00Perp d hd]
          change k₀ a.1 * quraKet00 d (a.2.1, a.2.2.1) * (if a.2.2.2 = s then 1 else 0) =
            k₀ a.1 * (quraKet00 d (a.2.1, a.2.2.1) * (if a.2.2.2 = s then 1 else 0))
          ring

/-- `Λ⊥` has no `|00⟩` component in any column. -/
lemma quraLambdaPerp_00_zero (d : ℕ) [NeZero d] (U : Matrix (Fin d) (Fin d) ℂ) (s t : Fin d) :
    quraLambdaPerp d U (0, (0, t)) s = 0 := by
  rw [quraLambdaPerp]
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro c hc
  by_cases hc00 : c.1 = 0 ∧ c.2.1 = 0
  · have hp : quraKet00Perp d (c.1, c.2.1) = 0 := by
      have hc1 : c.1.val = 0 := congrArg Fin.val hc00.1
      have hc2 : c.2.1.val = 0 := congrArg Fin.val hc00.2
      simp [quraKet00Perp, hc1, hc2]
    change quraDecoder U (0, (0, t)) c * (quraKet00Perp d (c.1, c.2.1) * U.conjTranspose c.2.2 s) =
    0
    rw [hp]
    simp
  · have hD : quraDecoder U (0, (0, t)) c = 0 := by
      have hnot : ¬ (0 = c.1 ∧ 0 = c.2.1) := by
        intro h
        apply hc00
        exact ⟨h.1.symm, h.2.symm⟩
      simp [quraDecoder, hnot]
    rw [hD]
    simp

/-- `Ψ⊥` has no `|00⟩` component in any column. -/
lemma quraPsiPerp_00_zero (d : ℕ) [NeZero d] (U : Matrix (Fin d) (Fin d) ℂ) (s t : Fin d) :
    quraPsiPerp d U (0, (0, t)) s = 0 := by
  rw [quraPsiPerp]
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro c hc
  by_cases hc00 : c.1 = 0 ∧ c.2.1 = 0
  · have hp : quraKet00Perp d (c.1, c.2.1) = 0 := by
      have hc1 : c.1.val = 0 := congrArg Fin.val hc00.1
      have hc2 : c.2.1.val = 0 := congrArg Fin.val hc00.2
      simp [quraKet00Perp, hc1, hc2]
    change (quraDecoder U).conjTranspose (0, (0, t)) c *
      (quraKet00Perp d (c.1, c.2.1) * (if c.2.2 = s then 1 else 0)) = 0
    rw [hp]
    simp
  · have hD : (quraDecoder U).conjTranspose (0, (0, t)) c = 0 := by
      rw [Matrix.conjTranspose_apply]
      have hD' : quraDecoder U c (0, (0, t)) = 0 := by
        simp [quraDecoder, hc00]
      rw [hD']
      simp
    rw [hD]
    simp

/-- `D(U)·D(U)† = I` when `U` is unitary. -/
lemma quraDecoder_mul_conjTranspose (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quraDecoder U * (quraDecoder U).conjTranspose = 1 := by
  have hmem : quraDecoder U ∈ Matrix.unitaryGroup (Fin d × (Fin d × Fin d)) ℂ :=
    (decoderOperator ⟨U, hU⟩).property
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hmem

/-- `D(U)·(D(U)†·V) = V` when `U` is unitary. -/
lemma quraDecoder_mul_conjTranspose_mul (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (V : Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ) :
    quraDecoder U * ((quraDecoder U).conjTranspose * V) = V := by
  calc
    quraDecoder U * ((quraDecoder U).conjTranspose * V)
        = (quraDecoder U * (quraDecoder U).conjTranspose) * V := by
          rw [← Matrix.mul_assoc]
    _ = V := by
          rw [quraDecoder_mul_conjTranspose d U hU]
          simp

/-- `D̃(U)·(|0⟩⊗Ψ₀) = |0⟩⊗Λ⊥` (paper `lem:tilde_D`, first statement). -/
lemma quraTildeD_mul_ket0_psi0 (d : ℕ) [NeZero d] (U : Matrix (Fin d) (Fin d) ℂ) :
    quraTildeD d U * (Matrix.of fun a s =>
        k₀ a.1 * quraPsi0 d U (a.2.1, (a.2.2.1, a.2.2.2)) s) =
      Matrix.of fun a s =>
        k₀ a.1 * quraLambdaPerp d U (a.2.1, (a.2.2.1, a.2.2.2)) s := by
  rw [quraTildeD]
  simp only [Matrix.mul_assoc]
  change quraGConjTensor d * (quraX2D d U * (quraGTensor d * ((Matrix.of fun a s =>
      k₀ a.1 * (quraKet00 d (a.2.1, a.2.2.1) * U.conjTranspose a.2.2.2 s)) :
        Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin d) ℂ))) =
    Matrix.of fun a s => k₀ a.1 * quraLambdaPerp d U (a.2.1, (a.2.2.1, a.2.2.2)) s
  rw [quraGTensor_mul_ket0_ket00_U]
  change quraGConjTensor d * (quraX2D d U * (Matrix.of fun a s =>
      k₁ a.1 * (quraKet00PerpU d U (a.2.1, (a.2.2.1, a.2.2.2)) s))) =
    Matrix.of fun a s => k₀ a.1 * quraLambdaPerp d U (a.2.1, (a.2.2.1, a.2.2.2)) s
  rw [quraX2D_mul_ket1]
  rw [quraGConjTensor_mul_ket0_of_perp]
  · rfl
  · intro s t
    exact quraLambdaPerp_00_zero d U s t

/-- `D̃(U)·(|0⟩⊗Ψ⊥) = |0⟩⊗Λ₀` (paper `lem:tilde_D`, second statement). -/
lemma quraTildeD_mul_ket0_psiPerp (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quraTildeD d U * (Matrix.of fun a s =>
        k₀ a.1 * quraPsiPerp d U (a.2.1, (a.2.2.1, a.2.2.2)) s) =
      Matrix.of fun a s =>
        k₀ a.1 * quraLambda0 d (a.2.1, (a.2.2.1, a.2.2.2)) s := by
  rw [quraTildeD]
  simp only [Matrix.mul_assoc]
  rw [quraGTensor_mul_ket0_of_perp]
  · rw [quraX2D_mul_ket0]
    change quraGConjTensor d * (Matrix.of fun a s =>
        k₁ a.1 * (quraDecoder U * ((quraDecoder U).conjTranspose * quraVecState d
        (quraKet00Perp d)))
          (a.2.1, (a.2.2.1, a.2.2.2)) s) =
      Matrix.of fun a s => k₀ a.1 * quraLambda0 d (a.2.1, (a.2.2.1, a.2.2.2)) s
    rw [quraDecoder_mul_conjTranspose_mul d U hU (quraVecState d (quraKet00Perp d))]
    change quraGConjTensor d * (Matrix.of fun a s =>
        k₁ a.1 * (quraKet00Perp d (a.2.1, a.2.2.1) * (if a.2.2.2 = s then 1 else 0))) =
      Matrix.of fun a s => k₀ a.1 * quraLambda0 d (a.2.1, (a.2.2.1, a.2.2.2)) s
    rw [quraGConjTensor_mul_ket1_ket00perp_I d hd]
    rfl
  · intro s t
    exact quraPsiPerp_00_zero d U s t

end

end QuantumAlg.UnitaryReversal
