/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Tensor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Linear combination of unitaries (LCU)

The LCU primitive block-encodes a linear combination `T = ∑ᵢ αᵢ Uᵢ` of
unitaries into a larger operator acting on an ancilla "control" register
tensored with the system [Lin22, hermfunc.tex:531].

Given coefficients `αᵢ ≥ 0` on a `2 ^ a`-dimensional control register and
gates `Uᵢ` on `n` qubits, the construction uses two oracles
[Lin22, hermfunc.tex:492]:

- `SELECT = ∑ᵢ |i⟩⟨i| ⊗ Uᵢ` applies `Uᵢ` conditioned on the control label `i`;
- `PREPARE` is any `V` with `V|0⟩ = (1/√‖α‖₁) ∑ᵢ √αᵢ |i⟩`, where
  `‖α‖₁ = ∑ᵢ αᵢ` is the coefficient 1-norm [Lin22, hermfunc.tex:501].

The walk operator `W = (V† ⊗ I) · SELECT · (V ⊗ I)` then block-encodes
`T/‖α‖₁`: its `⟨0|·|0⟩` control block equals `(1/‖α‖₁) ∑ᵢ αᵢ Uᵢ`
[Lin22, hermfunc.tex:534].

## Conventions

- The control register holds the most significant qubits of the joint basis
  label (big-endian, `prodEquiv`); `|0⟩` is the all-zeros control state.
- `PREPARE` enters only through its defining first column `V i 0 = √(αᵢ/‖α‖₁)`
  (an explicit hypothesis), matching the "prepare oracle" assumption; no
  particular circuit for `V` is fixed.
- Each `Uᵢ` is an arbitrary gate: the block-encoding identity is purely
  algebraic and needs no unitarity of `Uᵢ`.

## Main definitions

- `QuantumAlg.lcuProj` — control-basis projector `|i⟩⟨i|`.
- `QuantumAlg.lcuSelect` — the select oracle `∑ᵢ |i⟩⟨i| ⊗ Uᵢ`.
- `QuantumAlg.lcuNorm` — the coefficient 1-norm `∑ᵢ αᵢ`.
- `QuantumAlg.lcuWalk` — the walk operator `(V† ⊗ I) · SELECT · (V ⊗ I)`.

## Main results

- `QuantumAlg.lcuWalk_eq_sum` — `W = ∑ᵢ (V† |i⟩⟨i| V) ⊗ Uᵢ`.
- `QuantumAlg.lcu_block_encoding` — the all-zeros control block of `W` is
  `(1/‖α‖₁) ∑ᵢ αᵢ Uᵢ` [Lin22, hermfunc.tex:531].

Pinned Mathlib API: `Matrix.mul_apply`, `Matrix.sum_apply`,
`Matrix.conjTranspose_apply`, `Matrix.conjTranspose_one`, `Matrix.of_apply`,
`Finset.mul_sum`, `Finset.sum_mul`, `Fintype.sum_ite_eq'`,
`Real.mul_self_sqrt`, `Complex.star_def`, `Complex.conj_ofReal`,
`Complex.ofReal_mul`, `Complex.ofReal_div`.
-/

@[expose] public section

namespace QuantumAlg

noncomputable section

variable {a n : ℕ}

/-- The control-basis projector `|i⟩⟨i|` on the `a`-qubit control register. -/
def lcuProj (i : Fin (2 ^ a)) : Gate a :=
  Matrix.of fun r c => (if r = i then (1 : ℂ) else 0) * (if c = i then (1 : ℂ) else 0)

/-- The select oracle `SELECT = ∑ᵢ |i⟩⟨i| ⊗ Uᵢ` [Lin22, hermfunc.tex:492]. -/
def lcuSelect (U : Fin (2 ^ a) → Gate n) : Gate (a + n) :=
  ∑ i, (lcuProj i).tensor (U i)

/-- The coefficient 1-norm `‖α‖₁ = ∑ᵢ αᵢ` for nonnegative coefficients
[Lin22, hermfunc.tex:506]. -/
def lcuNorm (α : Fin (2 ^ a) → ℝ) : ℝ := ∑ i, α i

/-- The LCU walk operator `W = (V† ⊗ I) · SELECT · (V ⊗ I)`
[Lin22, hermfunc.tex:534]. `V` is the prepare oracle, `U` the family selected
by `SELECT`. -/
def lcuWalk (V : Gate a) (U : Fin (2 ^ a) → Gate n) : Gate (a + n) :=
  (V.tensor (1 : Gate n)).conjTranspose * lcuSelect U * V.tensor (1 : Gate n)

/-- Sandwiching the control projector between `V†` and `V` and reading the
`(0, 0)` entry leaves the squared first-column amplitude
(`star (V i 0) * V i 0`). -/
private theorem lcuProj_sandwich (V : Gate a) (i : Fin (2 ^ a)) :
    (V.conjTranspose * lcuProj i * V) 0 0 = star (V i 0) * V i 0 := by
  have hsum : (∑ k, star (V k 0) * (if k = i then (1 : ℂ) else 0)) = star (V i 0) := by
    simp only [mul_ite, mul_one, mul_zero]
    exact Fintype.sum_ite_eq' i (fun k => star (V k 0))
  have hsum2 : (∑ c, (if c = i then (1 : ℂ) else 0) * V c 0) = V i 0 := by
    simp only [ite_mul, one_mul, zero_mul]
    exact Fintype.sum_ite_eq' i (fun c => V c 0)
  have key : ∀ c, (V.conjTranspose * lcuProj i) 0 c
      = star (V i 0) * (if c = i then (1 : ℂ) else 0) := by
    intro c
    rw [Matrix.mul_apply]
    simp only [lcuProj, Matrix.of_apply, Matrix.conjTranspose_apply, ← mul_assoc]
    rw [← Finset.sum_mul, hsum]
  rw [Matrix.mul_apply]
  simp only [key, mul_assoc]
  rw [← Finset.mul_sum, hsum2]

/-- The LCU walk operator expands into a control-block sum
`W = ∑ᵢ (V† |i⟩⟨i| V) ⊗ Uᵢ`. -/
theorem lcuWalk_eq_sum (V : Gate a) (U : Fin (2 ^ a) → Gate n) :
    lcuWalk V U = ∑ i, Gate.tensor (V.conjTranspose * lcuProj i * V) (U i) := by
  unfold lcuWalk lcuSelect
  rw [Gate.conjTranspose_tensor, Matrix.conjTranspose_one, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Gate.tensor_mul_tensor, one_mul, Gate.tensor_mul_tensor, mul_one]

/-- **LCU block encoding** [Lin22, hermfunc.tex:531]. For nonnegative
coefficients `α` with positive 1-norm and a prepare oracle `V` satisfying
`V i 0 = √(αᵢ/‖α‖₁)`, the all-zeros control block of the walk operator is the
normalized linear combination: for all system labels `s t`,
`⟨0,s| W |0,t⟩ = (1/‖α‖₁) ∑ᵢ αᵢ ⟨s| Uᵢ |t⟩`. -/
theorem LinearCombinationOfUnitaries.main (V : Gate a) (U : Fin (2 ^ a) → Gate n)
    (α : Fin (2 ^ a) → ℝ) (hα : ∀ i, 0 ≤ α i) (hlam : 0 < lcuNorm α)
    (hV : ∀ i, V i 0 = ((Real.sqrt (α i / lcuNorm α) : ℝ) : ℂ))
    (s t : Fin (2 ^ n)) :
    lcuWalk V U (prodEquiv (0, s)) (prodEquiv (0, t))
      = (↑(lcuNorm α))⁻¹ * ∑ i, (↑(α i) : ℂ) * U i s t := by
  have tprod : ∀ (G : Gate a) (K : Gate n) (x x' : Fin (2 ^ a))
      (y y' : Fin (2 ^ n)),
      (G.tensor K) (prodEquiv (x, y)) (prodEquiv (x', y')) = G x x' * K y y' := by
    intro G K x x' y y'
    rw [Gate.tensor_apply]
    simp only [Equiv.symm_apply_apply]
  rw [lcuWalk_eq_sum, Matrix.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tprod, lcuProj_sandwich]
  have hnn : (0 : ℝ) ≤ α i / lcuNorm α := div_nonneg (hα i) hlam.le
  rw [hV i, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt hnn, Complex.ofReal_div]
  ring


end

end QuantumAlg
