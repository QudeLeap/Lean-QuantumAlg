/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Finite subgroup averages

A unitary representation averaged over a finite subgroup gives the orthogonal
projector onto its invariant vectors. Its trace is the averaged character.
The final conditional normalization and rank-functional identities assume the
stated idempotent-trace and nonzero-scalar laws; they do not identify an arbitrary
function with the actual matrix rank or prove a Fourier-sampling execution.
-/

@[expose] public section

namespace Matrix.SubgroupAverage

noncomputable section

open scoped BigOperators

variable {G V : Type*} [Group G] [Finite G] [Fintype V] [DecidableEq V]

/-- Enumerate a subgroup of a finite ambient group without an extra public instance. -/
local instance subgroupFintype (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- Definition: σ(H) = Σ_{h ∈ H} σ(h). -/
def sigmaSum (H : Subgroup G) (σ : G → Matrix V V ℂ) : Matrix V V ℂ := by
  classical
  let : Fintype H := Fintype.ofFinite H
  exact ∑ h : H, σ h.1

/-- Definition: character sum Σ_{h ∈ H} χ(h). -/
def charSum (H : Subgroup G) (χ : G → ℂ) : ℂ := by
  classical
  let : Fintype H := Fintype.ofFinite H
  exact ∑ h : H, χ h.1

/-- Definition: conjugated character sum Σ_{h ∈ H} χ(h)*. -/
def charSumStar (H : Subgroup G) (χ : G → ℂ) : ℂ := by
  classical
  let : Fintype H := Fintype.ofFinite H
  exact ∑ h : H, star (χ h.1)

/-- Definition: averaging projector P_{H,σ} = (1/|H|) σ(H). -/
def subgroupProjector (H : Subgroup G) (σ : G → Matrix V V ℂ) : Matrix V V ℂ :=
  (1 / (Nat.card H : ℂ)) • sigmaSum H σ

/-- Definition: conditional state ρ̂ = σ(H)* / Σ χ(h)*. -/
def rhoHat (H : Subgroup G) (σ : G → Matrix V V ℂ) (χ : G → ℂ) :
    Matrix V V ℂ :=
  (charSumStar H χ)⁻¹ • (sigmaSum H σ).conjTranspose

/-- Definition: H-invariance of a vector. -/
def IsHInvariant (H : Subgroup G) (σ : G → Matrix V V ℂ) (v : V → ℂ) : Prop :=
  ∀ h : H, (σ h.1).mulVec v = v

/-- Definition: orthogonal projector onto a set of vectors. -/
def IsOrthogonalProjectorOnto
    (P : Matrix V V ℂ) (S : (V → ℂ) → Prop) : Prop :=
  P.conjTranspose = P ∧ P * P = P ∧ ∀ v : V → ℂ, S v ↔ P.mulVec v = v

/-- `|H| ≠ 0` as a complex number. -/
lemma hcard_ne_zero (H : Subgroup G) : (Nat.card H : ℂ) ≠ 0 := by
  have : Nonempty H := ⟨⟨(1 : G), H.one_mem⟩⟩
  have hpos : 0 < Fintype.card H := Fintype.card_pos
  have hne : Nat.card H ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact ne_of_gt hpos
  exact_mod_cast hne

omit [Finite G] in
/-- Reindexing `h ↦ h⁻¹` leaves a sum over `H` unchanged. -/
lemma sum_inv {β : Type*} [AddCommMonoid β] (H : Subgroup G) [Fintype H]
    (f : G → β) :
    (∑ h : H, f (h.1⁻¹)) = ∑ h : H, f h.1 := by
  classical
  rw [← Equiv.sum_comp (Equiv.inv H) (fun h : H => f h.1)]
  simp

omit [Finite G] in
/-- Reindexing `k ↦ h·k` leaves a sum over `H` unchanged. -/
lemma sum_mul_right {β : Type*} [AddCommMonoid β] (H : Subgroup G) [Fintype H]
    (h : H) (f : G → β) :
    (∑ k : H, f (h.1 * k.1)) = ∑ k : H, f k.1 := by
  classical
  let e : H ≃ H :=
    { toFun := fun k => ⟨h.1 * k.1, H.mul_mem h.2 k.2⟩
      invFun := fun g => ⟨h.1⁻¹ * g.1, H.mul_mem (H.inv_mem h.2) g.2⟩
      left_inv := by
        intro k
        ext
        simp
      right_inv := by
        intro k
        ext
        simp }
  rw [← Equiv.sum_comp e (fun g : H => f g.1)]
  rfl

omit [Finite G] in
/-- In a unitary representation the inverse is the adjoint: σ(h⁻¹) = σ(h)†. -/
lemma sigma_inv (σ : G → Matrix V V ℂ)
    (h_unitary : ∀ g : G,
      (σ g).conjTranspose * σ g = 1 ∧ σ g * (σ g).conjTranspose = 1)
    (h_rep_one : σ 1 = 1)
    (h_rep_mul : ∀ g h : G, σ (g * h) = σ g * σ h)
    (h : G) : σ h⁻¹ = (σ h).conjTranspose := by
  calc
    σ h⁻¹ = σ h⁻¹ * 1 := by rw [Matrix.mul_one]
    _ = σ h⁻¹ * (σ h * (σ h).conjTranspose) := by rw [(h_unitary h).2]
    _ = (σ h⁻¹ * σ h) * (σ h).conjTranspose := by rw [← Matrix.mul_assoc]
    _ = σ (h⁻¹ * h) * (σ h).conjTranspose := by rw [h_rep_mul h⁻¹ h]
    _ = σ 1 * (σ h).conjTranspose := by rw [inv_mul_cancel h]
    _ = 1 * (σ h).conjTranspose := by rw [h_rep_one]
    _ = (σ h).conjTranspose := by rw [Matrix.one_mul]

omit [Finite G] in
/-- The character value at `h⁻¹` is the conjugate of the value at `h`. -/
lemma trace_char_inv (σ : G → Matrix V V ℂ) (χ : G → ℂ)
    (h_char : ∀ g : G, χ g = Matrix.trace (σ g))
    (h_unitary : ∀ g : G,
      (σ g).conjTranspose * σ g = 1 ∧ σ g * (σ g).conjTranspose = 1)
    (h_rep_one : σ 1 = 1)
    (h_rep_mul : ∀ g h : G, σ (g * h) = σ g * σ h)
    (h : G) : star (χ h) = χ h⁻¹ := by
  calc
    star (χ h) = star (Matrix.trace (σ h)) := by rw [h_char h]
    _ = Matrix.trace ((σ h).conjTranspose) := by rw [← Matrix.trace_conjTranspose]
    _ = Matrix.trace (σ h⁻¹) := by rw [sigma_inv σ h_unitary h_rep_one h_rep_mul h]
    _ = χ h⁻¹ := by rw [h_char h⁻¹]

section

variable (H : Subgroup G)

/-- The conjugated and plain character sums coincide. -/
lemma charSumStar_eq_charSum (σ : G → Matrix V V ℂ) (χ : G → ℂ)
    (h_unitary : ∀ g : G,
      (σ g).conjTranspose * σ g = 1 ∧ σ g * (σ g).conjTranspose = 1)
    (h_rep_one : σ 1 = 1)
    (h_rep_mul : ∀ g h : G, σ (g * h) = σ g * σ h)
    (h_char : ∀ g : G, χ g = Matrix.trace (σ g)) :
    charSumStar H χ = charSum H χ := by
  classical
  let : Fintype H := Fintype.ofFinite H
  calc
    charSumStar H χ = ∑ h : H, star (χ h.1) := rfl
    _ = ∑ h : H, χ (h.1⁻¹) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [trace_char_inv σ χ h_char h_unitary h_rep_one h_rep_mul h.1]
    _ = ∑ h : H, χ h.1 := sum_inv H (fun g => χ g)
    _ = charSum H χ := by simp [charSum]

/-- σ(H) is self-adjoint. -/
lemma sigmaSum_conjTranspose (σ : G → Matrix V V ℂ)
    (h_unitary : ∀ g : G,
      (σ g).conjTranspose * σ g = 1 ∧ σ g * (σ g).conjTranspose = 1)
    (h_rep_one : σ 1 = 1)
    (h_rep_mul : ∀ g h : G, σ (g * h) = σ g * σ h) :
    (sigmaSum H σ).conjTranspose = sigmaSum H σ := by
  classical
  let : Fintype H := Fintype.ofFinite H
  calc
    (sigmaSum H σ).conjTranspose = (∑ h : H, σ h.1).conjTranspose := rfl
    _ = ∑ h : H, (σ h.1).conjTranspose := by
      rw [Matrix.conjTranspose_sum Finset.univ (fun h : H => σ h.1)]
    _ = ∑ h : H, σ (h.1⁻¹) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [sigma_inv σ h_unitary h_rep_one h_rep_mul h.1]
    _ = ∑ h : H, σ h.1 := sum_inv H (fun g => σ g)
    _ = sigmaSum H σ := by simp [sigmaSum]

/-- The averaging operator P is self-adjoint. -/
lemma P_self_adjoint (σ : G → Matrix V V ℂ)
    (h_unitary : ∀ g : G,
      (σ g).conjTranspose * σ g = 1 ∧ σ g * (σ g).conjTranspose = 1)
    (h_rep_one : σ 1 = 1)
    (h_rep_mul : ∀ g h : G, σ (g * h) = σ g * σ h) :
    (subgroupProjector H σ).conjTranspose = subgroupProjector H σ := by
  calc
    (subgroupProjector H σ).conjTranspose
        = ((1 / (Nat.card H : ℂ)) • sigmaSum H σ).conjTranspose := rfl
    _ = star (1 / (Nat.card H : ℂ)) • (sigmaSum H σ).conjTranspose := by
      rw [Matrix.conjTranspose_smul]
    _ = (1 / (Nat.card H : ℂ)) • sigmaSum H σ := by
      rw [sigmaSum_conjTranspose H σ h_unitary h_rep_one h_rep_mul]
      congr 1
      simp
    _ = subgroupProjector H σ := rfl

omit [DecidableEq V] in
/-- σ(H)² = |H| · σ(H). -/
lemma sigmaSum_mul_sigmaSum (σ : G → Matrix V V ℂ)
    (h_rep_mul : ∀ g h : G, σ (g * h) = σ g * σ h) :
    sigmaSum H σ * sigmaSum H σ = (Nat.card H : ℂ) • sigmaSum H σ := by
  classical
  let : Fintype H := Fintype.ofFinite H
  calc
    sigmaSum H σ * sigmaSum H σ
        = (∑ h : H, σ h.1) * (∑ k : H, σ k.1) := rfl
    _ = ∑ h : H, σ h.1 * (∑ k : H, σ k.1) := by
      rw [Matrix.sum_mul Finset.univ (fun h : H => σ h.1) (∑ k : H, σ k.1)]
    _ = ∑ h : H, ∑ k : H, σ h.1 * σ k.1 := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [Matrix.mul_sum Finset.univ (fun k : H => σ k.1) (σ h.1)]
    _ = ∑ h : H, ∑ k : H, σ (h.1 * k.1) := by
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro k kk
      rw [h_rep_mul h.1 k.1]
    _ = ∑ h : H, ∑ g : H, σ g.1 := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [sum_mul_right H h (fun g => σ g)]
    _ = (Nat.card H : ℂ) • sigmaSum H σ := by
      rw [Finset.sum_const, sigmaSum, Nat.card_eq_fintype_card]
      ext i j
      simp

omit [DecidableEq V] in
/-- P is idempotent. -/
lemma P_idempotent (σ : G → Matrix V V ℂ)
    (h_rep_mul : ∀ g h : G, σ (g * h) = σ g * σ h) :
    subgroupProjector H σ * subgroupProjector H σ = subgroupProjector H σ := by
  calc
    subgroupProjector H σ * subgroupProjector H σ
        = ((1 / (Nat.card H : ℂ)) • sigmaSum H σ) *
            ((1 / (Nat.card H : ℂ)) • sigmaSum H σ) := rfl
    _ = ((1 / (Nat.card H : ℂ)) * (1 / (Nat.card H : ℂ))) •
          (sigmaSum H σ * sigmaSum H σ) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    _ = ((1 / (Nat.card H : ℂ)) * (1 / (Nat.card H : ℂ))) •
          ((Nat.card H : ℂ) • sigmaSum H σ) := by
      rw [sigmaSum_mul_sigmaSum H σ h_rep_mul]
    _ = ((1 / (Nat.card H : ℂ)) * (1 / (Nat.card H : ℂ)) *
          (Nat.card H : ℂ)) • sigmaSum H σ := by
      rw [smul_smul]
    _ = (1 / (Nat.card H : ℂ)) • sigmaSum H σ := by
      congr 1
      field_simp [hcard_ne_zero H]
    _ = subgroupProjector H σ := rfl

omit [DecidableEq V] in
/-- Each σ(h) fixes the projector: σ(h) · P = P. -/
lemma sigma_mul_P (σ : G → Matrix V V ℂ)
    (h_rep_mul : ∀ g h : G, σ (g * h) = σ g * σ h)
    (h : H) : σ h.1 * subgroupProjector H σ = subgroupProjector H σ := by
  classical
  let : Fintype H := Fintype.ofFinite H
  calc
    σ h.1 * subgroupProjector H σ
        = σ h.1 * ((1 / (Nat.card H : ℂ)) • sigmaSum H σ) := rfl
    _ = (1 / (Nat.card H : ℂ)) • (σ h.1 * sigmaSum H σ) := by
      rw [Matrix.mul_smul]
    _ = (1 / (Nat.card H : ℂ)) • (σ h.1 * (∑ k : H, σ k.1)) := rfl
    _ = (1 / (Nat.card H : ℂ)) • (∑ k : H, σ h.1 * σ k.1) := by
      congr 1
      rw [Matrix.mul_sum Finset.univ (fun k : H => σ k.1) (σ h.1)]
    _ = (1 / (Nat.card H : ℂ)) • (∑ k : H, σ (h.1 * k.1)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro k kk
      rw [h_rep_mul h.1 k.1]
    _ = (1 / (Nat.card H : ℂ)) • sigmaSum H σ := by
      congr 1
      rw [sum_mul_right H h (fun g => σ g), sigmaSum]
    _ = subgroupProjector H σ := rfl

omit [DecidableEq V] in
/-- The image of P is exactly the H-invariant subspace. -/
lemma P_mulVec_iff (σ : G → Matrix V V ℂ)
    (h_rep_mul : ∀ g h : G, σ (g * h) = σ g * σ h)
    (v : V → ℂ) :
    IsHInvariant H σ v ↔ (subgroupProjector H σ).mulVec v = v := by
  classical
  let : Fintype H := Fintype.ofFinite H
  constructor
  · intro hv
    calc
      (subgroupProjector H σ).mulVec v
          = ((1 / (Nat.card H : ℂ)) • sigmaSum H σ).mulVec v := rfl
      _ = (1 / (Nat.card H : ℂ)) • (sigmaSum H σ).mulVec v := by
            rw [Matrix.smul_mulVec]
      _ = (1 / (Nat.card H : ℂ)) • ((∑ h : H, σ h.1).mulVec v) := rfl
      _ = (1 / (Nat.card H : ℂ)) • (∑ h : H, (σ h.1).mulVec v) := by
            rw [Matrix.sum_mulVec Finset.univ (fun h : H => σ h.1) v]
      _ = (1 / (Nat.card H : ℂ)) • (∑ h : H, v) := by
            congr 1
            apply Finset.sum_congr rfl
            intro h hh
            rw [hv h]
      _ = (1 / (Nat.card H : ℂ)) • ((Nat.card H : ℂ) • v) := by
            congr 1
            rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
            ext i
            simp
      _ = v := by
            rw [smul_smul]
            have hcoef : (1 / (Nat.card H : ℂ)) * (Nat.card H : ℂ) = 1 := by
              field_simp [hcard_ne_zero H]
            rw [hcoef, one_smul]
  · intro hp h
    calc
      (σ h.1).mulVec v = (σ h.1).mulVec ((subgroupProjector H σ).mulVec v) := by
            rw [hp]
      _ = (σ h.1 * subgroupProjector H σ).mulVec v := by
            rw [← Matrix.mulVec_mulVec]
      _ = (subgroupProjector H σ).mulVec v := by
            rw [sigma_mul_P H σ h_rep_mul h]
      _ = v := hp

omit [DecidableEq V] in
/-- trace P = (1/|H|) Σ χ(h). -/
lemma P_trace (σ : G → Matrix V V ℂ) (χ : G → ℂ)
    (h_char : ∀ g : G, χ g = Matrix.trace (σ g)) :
    Matrix.trace (subgroupProjector H σ) = (1 / (Nat.card H : ℂ)) * charSum H χ := by
  classical
  let : Fintype H := Fintype.ofFinite H
  calc
    Matrix.trace (subgroupProjector H σ)
        = Matrix.trace ((1 / (Nat.card H : ℂ)) • sigmaSum H σ) := rfl
    _ = (1 / (Nat.card H : ℂ)) * Matrix.trace (sigmaSum H σ) := by
      rw [Matrix.trace_smul]
      simp
    _ = (1 / (Nat.card H : ℂ)) * (∑ h : H, Matrix.trace (σ h.1)) := by
      congr 1
      rw [sigmaSum]
      rw [Matrix.trace_sum Finset.univ (fun h : H => σ h.1)]
    _ = (1 / (Nat.card H : ℂ)) * (∑ h : H, χ h.1) := by
      congr 1
      apply Finset.sum_congr rfl
      intro h hh
      rw [h_char h.1]
    _ = (1 / (Nat.card H : ℂ)) * charSum H χ := rfl

omit [Fintype V] [DecidableEq V] in
/-- σ(H) = |H| · P. -/
lemma sigmaSum_eq_smul_P (σ : G → Matrix V V ℂ) :
    sigmaSum H σ = (Nat.card H : ℂ) • subgroupProjector H σ := by
  calc
    sigmaSum H σ = (1 : ℂ) • sigmaSum H σ := by simp
    _ = ((Nat.card H : ℂ) * (1 / (Nat.card H : ℂ))) • sigmaSum H σ := by
      congr 1
      field_simp [hcard_ne_zero H]
    _ = (Nat.card H : ℂ) • ((1 / (Nat.card H : ℂ)) • sigmaSum H σ) := by
      rw [← smul_smul]
    _ = (Nat.card H : ℂ) • subgroupProjector H σ := rfl

/-- ρ̂ = (|H| / Σ χ(h)*) · P. -/
lemma rhoHat_eq_smul_P (σ : G → Matrix V V ℂ) (χ : G → ℂ)
    (h_unitary : ∀ g : G,
      (σ g).conjTranspose * σ g = 1 ∧ σ g * (σ g).conjTranspose = 1)
    (h_rep_one : σ 1 = 1)
    (h_rep_mul : ∀ g h : G, σ (g * h) = σ g * σ h) :
    rhoHat H σ χ = ((Nat.card H : ℂ) / charSumStar H χ) • subgroupProjector H σ := by
  calc
    rhoHat H σ χ
        = (charSumStar H χ)⁻¹ • (sigmaSum H σ).conjTranspose := rfl
    _ = (charSumStar H χ)⁻¹ • sigmaSum H σ := by
      rw [sigmaSum_conjTranspose H σ h_unitary h_rep_one h_rep_mul]
    _ = (charSumStar H χ)⁻¹ • ((Nat.card H : ℂ) • subgroupProjector H σ) := by
      rw [sigmaSum_eq_smul_P H σ]
    _ = ((charSumStar H χ)⁻¹ * (Nat.card H : ℂ)) • subgroupProjector H σ := by
      rw [smul_smul]
    _ = ((Nat.card H : ℂ) / charSumStar H χ) • subgroupProjector H σ := by
      congr 1
      rw [div_eq_mul_inv, mul_comm]

omit [DecidableEq V] in
/-- rank P = (1/|H|) Σ χ(h) from idempotence and the trace. -/
lemma rank_P (σ : G → Matrix V V ℂ) (χ : G → ℂ)
    (h_rep_mul : ∀ g h : G, σ (g * h) = σ g * σ h)
    (h_char : ∀ g : G, χ g = Matrix.trace (σ g))
    (rank : Matrix V V ℂ → ℂ)
    (h_rank_idem : ∀ P : Matrix V V ℂ, P * P = P → rank P = Matrix.trace P) :
    rank (subgroupProjector H σ) = (1 / (Nat.card H : ℂ)) * charSum H χ := by
  rw [h_rank_idem (subgroupProjector H σ) (P_idempotent H σ h_rep_mul)]
  exact P_trace H σ χ h_char

/-- ρ̂ = P* / rank P. -/
lemma rhoHat_eq_rank (σ : G → Matrix V V ℂ) (χ : G → ℂ)
    (h_unitary : ∀ g : G,
      (σ g).conjTranspose * σ g = 1 ∧ σ g * (σ g).conjTranspose = 1)
    (h_rep_one : σ 1 = 1)
    (h_rep_mul : ∀ g h : G, σ (g * h) = σ g * σ h)
    (h_char : ∀ g : G, χ g = Matrix.trace (σ g))
    (rank : Matrix V V ℂ → ℂ)
    (h_rank_idem : ∀ P : Matrix V V ℂ, P * P = P → rank P = Matrix.trace P)
    (h_char_sum_ne : charSumStar H χ ≠ 0) :
    rhoHat H σ χ = (rank (subgroupProjector H σ))⁻¹ • (subgroupProjector H σ).conjTranspose := by
  calc
    rhoHat H σ χ
        = ((Nat.card H : ℂ) / charSumStar H χ) • subgroupProjector H σ :=
          rhoHat_eq_smul_P H σ χ h_unitary h_rep_one h_rep_mul
    _ = ((Nat.card H : ℂ) / charSumStar H χ) • (subgroupProjector H σ).conjTranspose := by
      rw [P_self_adjoint H σ h_unitary h_rep_one h_rep_mul]
    _ = (rank (subgroupProjector H σ))⁻¹ • (subgroupProjector H σ).conjTranspose := by
      congr 1
      have hrank : rank (subgroupProjector H σ) = charSumStar H χ / (Nat.card H : ℂ) := by
        rw [rank_P H σ χ h_rep_mul h_char rank h_rank_idem]
        rw [charSumStar_eq_charSum H σ χ h_unitary h_rep_one h_rep_mul h_char]
        ring
      rw [hrank]
      field_simp [hcard_ne_zero H, h_char_sum_ne]

/-- rank ρ̂ = rank P. -/
lemma rank_rhoHat (σ : G → Matrix V V ℂ) (χ : G → ℂ)
    (h_unitary : ∀ g : G,
      (σ g).conjTranspose * σ g = 1 ∧ σ g * (σ g).conjTranspose = 1)
    (h_rep_one : σ 1 = 1)
    (h_rep_mul : ∀ g h : G, σ (g * h) = σ g * σ h)
    (rank : Matrix V V ℂ → ℂ)
    (h_rank_smul : ∀ (c : ℂ) (A : Matrix V V ℂ), c ≠ 0 → rank (c • A) = rank A)
    (h_char_sum_ne : charSumStar H χ ≠ 0) :
    rank (rhoHat H σ χ) = rank (subgroupProjector H σ) := by
  rw [rhoHat_eq_smul_P H σ χ h_unitary h_rep_one h_rep_mul]
  apply h_rank_smul ((Nat.card H : ℂ) / charSumStar H χ) (subgroupProjector H σ)
  exact div_ne_zero (hcard_ne_zero H) h_char_sum_ne

/-- rank ρ̂ = (1/|H|) Σ χ(h)*. -/
lemma rank_rhoHat_star (σ : G → Matrix V V ℂ) (χ : G → ℂ)
    (h_unitary : ∀ g : G,
      (σ g).conjTranspose * σ g = 1 ∧ σ g * (σ g).conjTranspose = 1)
    (h_rep_one : σ 1 = 1)
    (h_rep_mul : ∀ g h : G, σ (g * h) = σ g * σ h)
    (h_char : ∀ g : G, χ g = Matrix.trace (σ g))
    (rank : Matrix V V ℂ → ℂ)
    (h_rank_idem : ∀ P : Matrix V V ℂ, P * P = P → rank P = Matrix.trace P)
    (h_rank_smul : ∀ (c : ℂ) (A : Matrix V V ℂ), c ≠ 0 → rank (c • A) = rank A)
    (h_char_sum_ne : charSumStar H χ ≠ 0) :
    rank (rhoHat H σ χ) = (1 / (Nat.card H : ℂ)) * charSumStar H χ := by
  calc
    rank (rhoHat H σ χ) = rank (subgroupProjector H σ) :=
      rank_rhoHat H σ χ h_unitary h_rep_one h_rep_mul rank
        h_rank_smul h_char_sum_ne
    _ = (1 / (Nat.card H : ℂ)) * charSum H χ :=
      rank_P H σ χ h_rep_mul h_char rank h_rank_idem
    _ = (1 / (Nat.card H : ℂ)) * charSumStar H χ := by
      rw [charSumStar_eq_charSum H σ χ h_unitary h_rep_one h_rep_mul h_char]

end

/-- Projector, normalization and conditional rank-functional identities. -/
theorem subgroupAverage_normalization_and_rankFunctional
    (H : Subgroup G)
    (σ : G → Matrix V V ℂ)
    (χ : G → ℂ)
    (rank : Matrix V V ℂ → ℂ)
    (h_rank_idem : ∀ P : Matrix V V ℂ, P * P = P → rank P = Matrix.trace P)
    (h_rank_smul : ∀ (c : ℂ) (A : Matrix V V ℂ), c ≠ 0 → rank (c • A) = rank A)
    (h_unitary : ∀ g : G,
      (σ g).conjTranspose * σ g = 1 ∧ σ g * (σ g).conjTranspose = 1)
    (h_rep_one : σ 1 = 1)
    (h_rep_mul : ∀ g h : G, σ (g * h) = σ g * σ h)
    (h_char : ∀ g : G, χ g = Matrix.trace (σ g))
    (h_char_sum_ne : charSumStar H χ ≠ 0) :
    IsOrthogonalProjectorOnto (subgroupProjector H σ) (IsHInvariant H σ) ∧
      rhoHat H σ χ =
        (rank (subgroupProjector H σ))⁻¹ • (subgroupProjector H σ).conjTranspose ∧
      rank (rhoHat H σ χ) = rank (subgroupProjector H σ) ∧
      rank (subgroupProjector H σ) =
        (1 / (Nat.card H : ℂ)) * charSum H χ ∧
      rank (rhoHat H σ χ) =
        (1 / (Nat.card H : ℂ)) * charSumStar H χ := by
  classical
  let : Fintype H := Fintype.ofFinite H
  have hproj : IsOrthogonalProjectorOnto (subgroupProjector H σ) (IsHInvariant H σ) := by
    refine ⟨P_self_adjoint H σ h_unitary h_rep_one h_rep_mul,
      P_idempotent H σ h_rep_mul, ?_⟩
    intro v
    exact P_mulVec_iff H σ h_rep_mul v
  refine ⟨hproj, ?_, ?_, ?_, ?_⟩
  · exact rhoHat_eq_rank H σ χ h_unitary h_rep_one h_rep_mul h_char rank
      h_rank_idem h_char_sum_ne
  · exact rank_rhoHat H σ χ h_unitary h_rep_one h_rep_mul rank
      h_rank_smul h_char_sum_ne
  · exact rank_P H σ χ h_rep_mul h_char rank h_rank_idem
  · exact rank_rhoHat_star H σ χ h_unitary h_rep_one h_rep_mul h_char rank
      h_rank_idem h_rank_smul h_char_sum_ne

end

end Matrix.SubgroupAverage
