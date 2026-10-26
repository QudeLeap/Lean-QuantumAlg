/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Pauli.JordanWigner.Permutations
import all QuantumAlg.Components.Pauli.JordanWigner.Permutations
import Mathlib.Tactic

/-!
# Nested commutators of complete matchings

The cancellation is an identity between complete fermionic hopping operators,
not termwise commutation of their Pauli expansions. It applies to the two
coordinate matchings used by the plaquette split [Cam22, main.tex:1291-1317].
-/

@[expose] public section

namespace QuantumAlg.JordanWigner

open HilbertOperator

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

private lemma matching_symm {n : ℕ} (e : Equiv.Perm (Fin n))
    (he : ∀ p, e (e p) = p) : e.symm = e := by
  apply Equiv.ext
  intro p
  apply e.injective
  simp [he]

lemma permutationBilinear_commute {n : ℕ} (e f : Equiv.Perm (Fin n))
    (h : ∀ p, e (f p) = f (e p)) :
    Commute (permutationBilinear e) (permutationBilinear f) := by
  apply sub_eq_zero.mp
  change ⁅permutationBilinear e, permutationBilinear f⁆ = 0
  rw [permutationBilinear_lie]
  have heq : e.trans f = f.trans e := by
    apply Equiv.ext
    intro p
    exact (h p).symm
  rw [heq, sub_self]

/-- The exact cancellation when the outer permutation is an involution. -/
lemma matching_nested_eq {n : ℕ} (e f : Equiv.Perm (Fin n))
    (hf : ∀ p, f (f p) = p) :
    ⁅permutationBilinear f, ⁅permutationBilinear f, permutationBilinear e⁆⁆ =
      (2 : ℂ) •
        (permutationBilinear e - permutationBilinear ((f.trans e).trans f)) := by
  rw [permutationBilinear_lie, lie_sub, permutationBilinear_lie,
    permutationBilinear_lie]
  have h₁ : f.trans (f.trans e) = e := by ext p; simp [Equiv.trans_apply, hf]
  have h₂ : (e.trans f).trans f = e := by ext p; simp [Equiv.trans_apply, hf]
  have h₃ : f.trans (e.trans f) = (f.trans e).trans f := by ext p; rfl
  rw [h₁, h₂, h₃]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Each single-coordinate nested commutator is bounded by twice the mode count. -/
lemma matching_nested_opNorm_le {n : ℕ} (e f : Equiv.Perm (Fin n))
    (he : ∀ p, e (e p) = p) (hf : ∀ p, f (f p) = p)
    (hne : ∀ p, p ≠ e p) :
    opNorm ⁅permutationBilinear f, ⁅permutationBilinear f, permutationBilinear e⁆⁆ ≤
      2 * (n : ℝ) := by
  let c := (f.trans e).trans f
  have hc : ∀ p, c (c p) = p := by
    intro p
    simp [c, Equiv.trans_apply, hf, he]
  have hcn : ∀ p, p ≠ c p := by
    intro p hp
    have h := congrArg f hp
    simp only [c, Equiv.trans_apply, hf] at h
    exact hne (f p) h
  have h₁ := permutationBilinear_opNorm_le e hne (matching_symm e he)
  have h₂ := permutationBilinear_opNorm_le c hcn (matching_symm c hc)
  rw [matching_nested_eq e f hf, opNorm_smul]
  have hs := opNorm_sub_le (permutationBilinear e) (permutationBilinear c)
  rw [Complex.norm_ofNat]
  have hn : opNorm (permutationBilinear e - permutationBilinear c) ≤ (n : ℝ) :=
    hs.trans (by linarith)
  exact mul_le_mul_of_nonneg_left hn (by norm_num)

private lemma lie_zero_of_commute {R : Register} {A B : HilbertOperator R}
    (h : Commute A B) : ⁅A, B⁆ = 0 := sub_eq_zero.mpr h.eq

/-- Cross-coordinate commutation removes every mixed-coordinate nested term. -/
lemma independent_directions_nested {R : Register} (P₁ P₂ G₁ G₂ : HilbertOperator R)
    (h₁ : Commute G₁ P₂) (h₂ : Commute G₂ P₁) (h₃ : Commute G₁ G₂) :
    ⁅G₁ + G₂, ⁅G₁ + G₂, P₁ + P₂⁆⁆ =
      ⁅G₁, ⁅G₁, P₁⁆⁆ + ⁅G₂, ⁅G₂, P₂⁆⁆ := by
  have h₄ : Commute G₁ ⁅G₂, P₂⁆ :=
    (h₃.mul_right h₁).sub_right (h₁.mul_right h₃)
  have h₅ : Commute G₂ ⁅G₁, P₁⁆ :=
    (h₃.symm.mul_right h₂).sub_right (h₂.mul_right h₃.symm)
  simp only [add_lie, lie_add, lie_zero_of_commute h₁, lie_zero_of_commute h₂,
    lie_zero_of_commute h₄, lie_zero_of_commute h₅, add_zero, zero_add]

/-- Two independent coordinate directions give an extensive nested bound. -/
lemma two_matchings_nested_opNorm_le {n : ℕ}
    (P₁ P₂ G₁ G₂ : Equiv.Perm (Fin n))
    (hp₁ : ∀ p, P₁ (P₁ p) = p) (hp₂ : ∀ p, P₂ (P₂ p) = p)
    (hg₁ : ∀ p, G₁ (G₁ p) = p) (hg₂ : ∀ p, G₂ (G₂ p) = p)
    (hn₁ : ∀ p, p ≠ P₁ p) (hn₂ : ∀ p, p ≠ P₂ p)
    (h₁ : ∀ p, G₁ (P₂ p) = P₂ (G₁ p))
    (h₂ : ∀ p, G₂ (P₁ p) = P₁ (G₂ p))
    (h₃ : ∀ p, G₁ (G₂ p) = G₂ (G₁ p)) :
    opNorm ⁅permutationBilinear G₁ + permutationBilinear G₂,
      ⁅permutationBilinear G₁ + permutationBilinear G₂,
        permutationBilinear P₁ + permutationBilinear P₂⁆⁆ ≤ 4 * (n : ℝ) := by
  rw [independent_directions_nested _ _ _ _
    (permutationBilinear_commute _ _ h₁)
    (permutationBilinear_commute _ _ h₂)
    (permutationBilinear_commute _ _ h₃)]
  have hleft := matching_nested_opNorm_le P₁ G₁ hp₁ hg₁ hn₁
  have hright := matching_nested_opNorm_le P₂ G₂ hp₂ hg₂ hn₂
  exact (opNorm_add_le _ _).trans (by linarith)

end

end QuantumAlg.JordanWigner
