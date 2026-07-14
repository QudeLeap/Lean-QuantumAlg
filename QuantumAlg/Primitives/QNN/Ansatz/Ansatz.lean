/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.MatrixExpInvolution
public import QuantumAlg.Util.QuantumFisher
public import QuantumAlg.Primitives.ParameterShift
public import QuantumAlg.Primitives.QNN.Algebras.PauliAlgebra
public import QuantumAlg.Primitives.QNN.Algebras.SymplecticDLA
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Multi-gate variational ansatz and the algebraic parameter-shift rule

A variational quantum model uses a parameterized unitary `U(θ) = ∏ₖ exp(-i(θₖ/2)Hₖ)` built from
single Pauli-rotation gates whose generators `Hₖ` are Hermitian involutions (`Hₖ² = 1`, spectrum
`±1`). The loss `C(θ) = ⟨ψ| U(θ)† O U(θ) |ψ⟩`, as a function of any one coordinate `θₖ` (the others
fixed), is a frequency-1 trigonometric polynomial `a + b cos θₖ + c sin θₖ`. This is *proved* from
the closed form of the gate exponential (`rotGen_eq`), not posited — it is the genuine quantum
substrate underneath the (otherwise assumed) trigonometric form of the parameter-shift rule.

The single rotation gate is `rotGen H θ = exp(-i(θ/2)H)`; for an involution `H` it has the closed
form `cos(θ/2)·1 - i sin(θ/2)·H` (`rotGen_eq`), hence is unitary (`rotGen_unitary`).

Convention: the half-angle generator `exp(-i(θ/2)H)` (the physics rotation gate `R_H(θ)`) makes the
single-coordinate cost frequency 1, matching `ParamShiftModel` and `varCost_ket0_Z = cos θ`.
-/

@[expose] public section

namespace QuantumAlg

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {m : Type*} [Fintype m] [DecidableEq m]

/-! ### The single Pauli-rotation gate `exp(-i(θ/2)H)` -/

/-- The single Pauli-rotation gate `R_H(θ) = exp(-i(θ/2)H)` on `Matrix m m ℂ`. -/
noncomputable def rotGen (H : Matrix m m ℂ) (θ : ℝ) : Matrix m m ℂ :=
  NormedSpace.exp ((-(Complex.I * (θ / 2 : ℂ))) • H)

/-- **Closed form of the rotation gate for an involution.** If `H * H = 1` then
`rotGen H θ = cos(θ/2)·1 - i sin(θ/2)·H`. Proved from the Banach-algebra involution exponential. -/
theorem rotGen_eq {H : Matrix m m ℂ} (hH : H * H = 1) (θ : ℝ) :
    rotGen H θ
      = (Real.cos (θ / 2) : ℂ) • (1 : Matrix m m ℂ)
        + (-(Complex.I * (Real.sin (θ / 2) : ℂ))) • H := by
  have hcosh : Complex.cosh (-(Complex.I * (θ / 2 : ℂ))) = (Real.cos (θ / 2) : ℂ) := by
    rw [Complex.cosh_neg,
      show Complex.I * (θ / 2 : ℂ) = ((θ / 2 : ℝ) : ℂ) * Complex.I from by push_cast; ring,
      Complex.cosh_mul_I, ← Complex.ofReal_cos]
  have hsinh : Complex.sinh (-(Complex.I * (θ / 2 : ℂ)))
      = -(Complex.I * (Real.sin (θ / 2) : ℂ)) := by
    rw [Complex.sinh_neg,
      show Complex.I * (θ / 2 : ℂ) = ((θ / 2 : ℝ) : ℂ) * Complex.I from by push_cast; ring,
      Complex.sinh_mul_I, ← Complex.ofReal_sin]
    ring
  rw [rotGen, hcosh.symm, hsinh.symm]
  exact exp_smul_of_mul_self_eq_one (-(Complex.I * (θ / 2 : ℂ))) hH

/-- **The rotation gate is unitary** (for any Hermitian `H`): `R_H(θ)† R_H(θ) = 1`.
Proved by the exponential group law: `(exp(-i(θ/2)H))† = exp(i(θ/2)H)`, and the two factors
commute (both are scalar multiples of `H`), so the product is `exp(0) = 1`. -/
theorem rotGen_unitary {H : Matrix m m ℂ} (hHerm : Hᴴ = H) (θ : ℝ) :
    (rotGen H θ)ᴴ * rotGen H θ = 1 := by
  simp only [rotGen]
  rw [← Matrix.exp_conjTranspose, conjTranspose_smul, hHerm]
  have hcomm : Commute (star (-(Complex.I * (θ / 2 : ℂ))) • H)
      ((-(Complex.I * (θ / 2 : ℂ))) • H) := ((Commute.refl H).smul_left _).smul_right _
  rw [← Matrix.exp_add_of_commute _ _ hcomm, ← add_smul]
  have hzero : star (-(Complex.I * (θ / 2 : ℂ))) + (-(Complex.I * (θ / 2 : ℂ))) = 0 := by
    rw [show (θ / 2 : ℂ) = ((θ / 2 : ℝ) : ℂ) from by push_cast; ring]
    simp only [Complex.star_def, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hzero, zero_smul, NormedSpace.exp_zero]

/-! ### Expectation-value helpers (ℂ-linearity and conjugation by a matrix)

`expval` from `QuantumFisher` is reused; we only need its ℂ-linearity (`expval_add`, `expval_smul`
already live in `QuantumFisher`) plus the conjugation-by-a-matrix identity below. -/

omit [DecidableEq m] in
/-- **Conjugation of the state by a matrix.** `⟨ψ| Aᴴ X A |ψ⟩ = ⟨Aψ| X |Aψ⟩`. The right-hand side is
`expval` of `X` in the transformed state `A *ᵥ ψ`. Used to peel the gates after coordinate `k` off a
multi-gate cost. -/
theorem expval_sandwich (ψ : m → ℂ) (A X : Matrix m m ℂ) :
    expval ψ (Aᴴ * X * A) = expval (A *ᵥ ψ) X := by
  rw [expval_def, expval_def, star_mulVec, mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
    Matrix.mul_assoc]

/-! ### Task B — the single-gate sandwich cost is a frequency-1 trigonometric polynomial -/

/-- The **single-gate sandwich cost** `C(θ) = ⟨ψ| R_H(θ)† O R_H(θ) |ψ⟩` for an observable `O`,
generator `H` and input `ψ`. -/
noncomputable def sandwichCost (ψ : m → ℂ) (O H : Matrix m m ℂ) (θ : ℝ) : ℝ :=
  (expval ψ ((rotGen H θ)ᴴ * O * rotGen H θ)).re

/-- **The conjugate (transpose) of the rotation gate for a Hermitian involution.** For Hermitian `H`
with `H * H = 1`, `R_H(θ)† = cos(θ/2)·1 + i sin(θ/2)·H` (the sign on the `H`-term flips). -/
theorem rotGen_conjTranspose_eq {H : Matrix m m ℂ} (hH : H * H = 1) (hHerm : Hᴴ = H) (θ : ℝ) :
    (rotGen H θ)ᴴ
      = (Real.cos (θ / 2) : ℂ) • (1 : Matrix m m ℂ)
        + (Complex.I * (Real.sin (θ / 2) : ℂ)) • H := by
  rw [rotGen_eq hH, conjTranspose_add, conjTranspose_smul, conjTranspose_smul,
    conjTranspose_one, hHerm]
  congr 1
  · rw [Complex.star_def, Complex.conj_ofReal]
  · congr 1
    rw [Complex.star_def, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring

/-- **The closed form of the sandwiched observable.** For a Hermitian involution `H`,
`R_H(θ)† O R_H(θ) = cos²(θ/2)·O + sin²(θ/2)·(H O H) + i·cos(θ/2)·sin(θ/2)·(H O − O H)`. -/
theorem rotGen_sandwich_expand {O H : Matrix m m ℂ} (hH : H * H = 1) (hHerm : Hᴴ = H) (θ : ℝ) :
    (rotGen H θ)ᴴ * O * rotGen H θ
      = ((Real.cos (θ / 2) : ℂ) ^ 2) • O
        + ((Real.sin (θ / 2) : ℂ) ^ 2) • (H * O * H)
        + (Complex.I * (Real.cos (θ / 2) : ℂ) * (Real.sin (θ / 2) : ℂ)) • (H * O - O * H) := by
  rw [rotGen_conjTranspose_eq hH hHerm, rotGen_eq hH]
  set c : ℂ := (Real.cos (θ / 2) : ℂ)
  set s : ℂ := (Real.sin (θ / 2) : ℂ)
  -- Expand the triple product of the two binomials with `O` in the middle.
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one]
  -- The four terms: c²·O ; (c·(-(I·s)))·(O*H) ; (I·s·c)·(H*O) ; (I·s·(-(I·s)))·(H*O*H).
  -- Collect them into the claimed three terms via the ℂ-module structure (`I² = -1`).
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  match_scalars <;> first | linear_combination (-(s ^ 2) : ℂ) * hI | ring

/-- **Task B: the single-gate sandwich cost is a frequency-1 trigonometric polynomial.** For a
Hermitian involution generator `H` and a Hermitian observable `O`,
`⟨ψ| R_H(θ)† O R_H(θ) |ψ⟩ = a + b cos θ + c sin θ` with explicit `(a,b,c)`. Proved from the closed
form of the gate (`rotGen_eq`) and the reality of the relevant expectation values. -/
theorem sandwichCost_trig {ψ : m → ℂ} {O H : Matrix m m ℂ} (hH : H * H = 1) (hHerm : Hᴴ = H)
    (hO : Oᴴ = O) :
    ∃ a b c : ℝ, ∀ θ, sandwichCost ψ O H θ = a + b * Real.cos θ + c * Real.sin θ := by
  -- The three real expectation values that appear.
  set rO : ℝ := (expval ψ O).re with hrO
  set rHOH : ℝ := (expval ψ (H * O * H)).re with hrHOH
  set rComm : ℝ := (Complex.I * expval ψ (H * O - O * H)).re with hrComm
  refine ⟨(rO + rHOH) / 2, (rO - rHOH) / 2, rComm / 2, fun θ => ?_⟩
  -- `H * O * H` is Hermitian, so its expectation value is real.
  have hHOHherm : (H * O * H)ᴴ = H * O * H := by
    rw [conjTranspose_mul, conjTranspose_mul, hHerm, hO]; rw [Matrix.mul_assoc]
  -- Push `(·).re` through the expansion of the sandwiched observable.
  rw [sandwichCost, rotGen_sandwich_expand hH hHerm, expval_add, expval_add, expval_smul,
    expval_smul, expval_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul, Complex.add_re, Complex.add_re]
  -- Real-coefficient `smul`s contribute `coeff * (·).re` to the real part.
  have hsplit : ∀ (r : ℝ) (z : ℂ), ((r : ℂ) ^ 2 * z).re = r ^ 2 * z.re := by
    intro r z
    simp [Complex.mul_re, pow_two]
  rw [show ((Real.cos (θ / 2) : ℂ) ^ 2 * expval ψ O).re = Real.cos (θ / 2) ^ 2 * rO from by
        rw [hsplit],
    show ((Real.sin (θ / 2) : ℂ) ^ 2 * expval ψ (H * O * H)).re
        = Real.sin (θ / 2) ^ 2 * rHOH from by rw [hsplit]]
  -- The commutator term: `I · cos · sin · ⟨HO−OH⟩`, whose real part is `cos·sin·Re(I·⟨HO−OH⟩)`.
  have hcomm : ((Complex.I * (Real.cos (θ / 2) : ℂ) * (Real.sin (θ / 2) : ℂ))
      * expval ψ (H * O - O * H)).re
      = Real.cos (θ / 2) * Real.sin (θ / 2) * rComm := by
    rw [hrComm]
    rw [show Complex.I * (Real.cos (θ / 2) : ℂ) * (Real.sin (θ / 2) : ℂ) * expval ψ (H * O - O * H)
          = ((Real.cos (θ / 2) : ℂ) * (Real.sin (θ / 2) : ℂ))
            * (Complex.I * expval ψ (H * O - O * H)) from by ring]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_zero,
      Complex.mul_im, add_zero]
  rw [hcomm]
  -- Double-angle: with `α = θ/2` and `θ = 2α`, rewrite
  -- `cos²α, sin²α, cosα·sinα` via `cos θ, sin θ`.
  have hcos2 : Real.cos (θ / 2) ^ 2 = 1 / 2 + Real.cos θ / 2 := by
    rw [Real.cos_sq]; rw [show 2 * (θ / 2) = θ from by ring]
  have hsin2 : Real.sin (θ / 2) ^ 2 = 1 / 2 - Real.cos θ / 2 := by
    rw [Real.sin_sq, hcos2]; ring
  have hcossin : Real.cos (θ / 2) * Real.sin (θ / 2) = Real.sin θ / 2 := by
    have h := Real.sin_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ from by ring] at h
    rw [h]; ring
  rw [hcos2, hsin2, hcossin]
  ring

/-- The **`ParamShiftModel` of the single-gate sandwich cost**: its cost is
`sandwichCost ψ O H`, and
its frequency-1 trigonometric form is witnessed by `sandwichCost_trig`. Feeding this into
`ParamShiftModel.parameter_shift` yields the single-gate parameter-shift rule. -/
noncomputable def sandwichModel (ψ : m → ℂ) (O H : Matrix m m ℂ) (hH : H * H = 1) (hHerm : Hᴴ = H)
    (hO : Oᴴ = O) : ParamShiftModel where
  cost := sandwichCost ψ O H
  a := Classical.choose (sandwichCost_trig (ψ := ψ) hH hHerm hO)
  b := Classical.choose (Classical.choose_spec (sandwichCost_trig (ψ := ψ) hH hHerm hO))
  c := Classical.choose (Classical.choose_spec
    (Classical.choose_spec (sandwichCost_trig (ψ := ψ) hH hHerm hO)))
  trig := Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (sandwichCost_trig (ψ := ψ) hH hHerm hO)))

/-! ### Task C — the multi-gate ansatz and the per-coordinate reduction

Matrices are *not* commutative under `*`, so the ordered product is taken over `List.ofFn`, never
`Finset.prod`. The per-coordinate reduction `cost_update_eq_sandwich` shows that, with all other
coordinates fixed, the dependence of the cost on the `k`-th angle is exactly a single-gate sandwich
cost — which `sandwichCost_trig` already proved to be frequency-1. -/

/-- The **multi-gate variational ansatz** `U(θ) = R_{H₀}(θ₀) · R_{H₁}(θ₁) ⋯ R_{H_{M-1}}(θ_{M-1})`,
the ordered product of the single Pauli-rotation gates. -/
noncomputable def ansatz {M : ℕ} (H : Fin M → Matrix m m ℂ) (θ : Fin M → ℝ) : Matrix m m ℂ :=
  (List.ofFn (fun k : Fin M => rotGen (H k) (θ k))).prod

/-- The **multi-gate variational cost** `C(θ) = ⟨ψ| U(θ)† O U(θ) |ψ⟩`. -/
noncomputable def cost {M : ℕ} (ψ : m → ℂ) (O : Matrix m m ℂ) (H : Fin M → Matrix m m ℂ)
    (θ : Fin M → ℝ) : ℝ := (expval ψ ((ansatz H θ)ᴴ * O * ansatz H θ)).re

/-- The ordered product of the gates **strictly before** coordinate `k` (independent of `θ k`). -/
noncomputable def ansatzL {M : ℕ} (H : Fin M → Matrix m m ℂ) (θ : Fin M → ℝ) (k : Fin M) :
    Matrix m m ℂ :=
  ((List.ofFn (fun j : Fin M => rotGen (H j) (θ j))).take (k : ℕ)).prod

/-- The ordered product of the gates **strictly after** coordinate `k` (independent of `θ k`). -/
noncomputable def ansatzR {M : ℕ} (H : Fin M → Matrix m m ℂ) (θ : Fin M → ℝ) (k : Fin M) :
    Matrix m m ℂ :=
  ((List.ofFn (fun j : Fin M => rotGen (H j) (θ j))).drop ((k : ℕ) + 1)).prod

/-- **Updating only coordinate `k` is `List.set` on the gate list.** The gate list of
`update θ k t` agrees with that of `θ` except at position `k`, where the gate is `rotGen (H k) t`.
-/
theorem ofFn_rotGen_update {M : ℕ} (H : Fin M → Matrix m m ℂ) (θ : Fin M → ℝ) (k : Fin M) (t : ℝ) :
    List.ofFn (fun j : Fin M => rotGen (H j) ((Function.update θ k t) j))
      = (List.ofFn (fun j : Fin M => rotGen (H j) (θ j))).set (k : ℕ) (rotGen (H k) t) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    rw [List.getElem_ofFn]
    rw [List.length_ofFn] at h₁
    rw [List.getElem_set]
    by_cases hik : (k : ℕ) = i
    · have hik' : (⟨i, h₁⟩ : Fin M) = k := Fin.ext hik.symm
      rw [if_pos hik, hik', Function.update_self]
    · rw [if_neg hik, List.getElem_ofFn]
      have hne : (⟨i, h₁⟩ : Fin M) ≠ k := by
        intro h; exact hik (by rw [← h])
      rw [Function.update_of_ne hne]

/-- **The cost depends on the `k`-th gate only through `t`, and that dependence is a single-gate
sandwich cost.** Splitting the ordered gate product at index `k`, the gates before/after `k` form
`t`-independent factors `Lmat = ansatzL`, `Rmat = ansatzR`; peeling `Rmat` onto
the state and folding
`Lmatᴴ O Lmat` into the observable gives exactly `sandwichCost` of the `k`-th gate. -/
theorem cost_update_eq_sandwich {M : ℕ} {ψ : m → ℂ} {O : Matrix m m ℂ} {H : Fin M → Matrix m m ℂ}
    (θ : Fin M → ℝ) (k : Fin M) (t : ℝ) :
    cost ψ O H (Function.update θ k t)
      = sandwichCost (ansatzR H θ k *ᵥ ψ)
          ((ansatzL H θ k)ᴴ * O * ansatzL H θ k) (H k) t := by
  -- The gate list of the updated parameters, with the `k`-th entry singled out.
  have hk : (k : ℕ) < (List.ofFn (fun j : Fin M => rotGen (H j) (θ j))).length := by
    rw [List.length_ofFn]; exact k.2
  -- Split the ordered product `U = Lmat * R_{H_k}(t) * Rmat`.
  have hsplit : ansatz H (Function.update θ k t)
      = ansatzL H θ k * (rotGen (H k) t * ansatzR H θ k) := by
    rw [ansatz, ofFn_rotGen_update]
    rw [List.prod_set]
    rw [List.length_ofFn, if_pos k.isLt]
    -- `(take k).prod * (rotGen (H k) t) * (drop (k+1)).prod`, regrouped.
    rw [ansatzL, ansatzR, mul_assoc]
  -- Substitute the split into the cost and peel off `Rmat` via `expval_sandwich`.
  rw [cost, hsplit, sandwichCost]
  -- Group `Uᴴ O U` as `Rmatᴴ * X * Rmat` with `X = (rotGen t)ᴴ * (Lmatᴴ O Lmat) * rotGen t`,
  -- then `expval_sandwich` peels the `Rmat` factors onto the state.
  rw [show (ansatzL H θ k * (rotGen (H k) t * ansatzR H θ k))ᴴ * O
        * (ansatzL H θ k * (rotGen (H k) t * ansatzR H θ k))
      = (ansatzR H θ k)ᴴ
          * ((rotGen (H k) t)ᴴ * ((ansatzL H θ k)ᴴ * O * ansatzL H θ k) * rotGen (H k) t)
          * ansatzR H θ k from by
    simp only [conjTranspose_mul]
    noncomm_ring]
  rw [expval_sandwich]

/-- **Task C: the multi-gate cost is frequency-1 in each coordinate.** Fixing
all coordinates but the
`k`-th, the cost `t ↦ C(update θ k t)` is a frequency-1 trigonometric polynomial. This is the
per-coordinate reduction `cost_update_eq_sandwich` fed into the single-gate result
`sandwichCost_trig`, using that `Lmatᴴ O Lmat` is Hermitian when `O` is. -/
theorem cost_trig {M : ℕ} {ψ : m → ℂ} {O : Matrix m m ℂ} {H : Fin M → Matrix m m ℂ}
    (hH : ∀ k, (H k) * (H k) = 1) (hHerm : ∀ k, (H k)ᴴ = H k) (hO : Oᴴ = O) (θ : Fin M → ℝ)
    (k : Fin M) :
    ∃ a b c : ℝ, ∀ t, cost ψ O H (Function.update θ k t) = a + b * Real.cos t + c * Real.sin t := by
  -- `Lmatᴴ O Lmat` is Hermitian since `O` is.
  have hOconj : ((ansatzL H θ k)ᴴ * O * ansatzL H θ k)ᴴ
      = (ansatzL H θ k)ᴴ * O * ansatzL H θ k := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hO, Matrix.mul_assoc]
  obtain ⟨a, b, c, htrig⟩ :=
    sandwichCost_trig (ψ := ansatzR H θ k *ᵥ ψ)
      (O := (ansatzL H θ k)ᴴ * O * ansatzL H θ k) (H := H k) (hH k) (hHerm k) hOconj
  refine ⟨a, b, c, fun t => ?_⟩
  rw [cost_update_eq_sandwich, htrig]

/-! ### Task D — the algebraic parameter-shift rule for the multi-gate ansatz

The single-coordinate cost is frequency-1 (Task C), so the *existing* frequency-1 parameter-shift
rule (`ParamShiftModel.parameter_shift`) computes its exact derivative as a
symmetric two-point finite
difference. The `deriv` here is of the genuine `ℝ → ℝ` trigonometric cost — never
a Fréchet derivative
of the matrix exponential. -/

/-- The **parameter-shift estimate** of the `k`-th partial derivative: the
symmetric finite difference
of the cost at shift `±π/2` in coordinate `k`. -/
noncomputable def psrEstimate {M : ℕ} (ψ : m → ℂ) (O : Matrix m m ℂ) (H : Fin M → Matrix m m ℂ)
    (θ : Fin M → ℝ) (k : Fin M) : ℝ :=
  (cost ψ O H (Function.update θ k (θ k + Real.pi / 2))
    - cost ψ O H (Function.update θ k (θ k - Real.pi / 2))) / 2

/-- The **`ParamShiftModel` of the `k`-th single-coordinate cost** of the multi-gate ansatz. Its
trigonometric form is supplied by Task C (`cost_trig`). -/
noncomputable def costModel {M : ℕ} (ψ : m → ℂ) (O : Matrix m m ℂ) (H : Fin M → Matrix m m ℂ)
    (hH : ∀ k, (H k) * (H k) = 1) (hHerm : ∀ k, (H k)ᴴ = H k) (hO : Oᴴ = O) (θ : Fin M → ℝ)
    (k : Fin M) : ParamShiftModel where
  cost t := cost ψ O H (Function.update θ k t)
  a := Classical.choose (cost_trig hH hHerm hO θ k)
  b := Classical.choose (Classical.choose_spec (cost_trig hH hHerm hO θ k))
  c := Classical.choose (Classical.choose_spec (Classical.choose_spec (cost_trig hH hHerm hO θ k)))
  trig := Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (cost_trig hH hHerm hO θ k)))

/-- **Task D: the algebraic parameter-shift rule for the multi-gate ansatz.** The
exact `k`-th partial
derivative of the multi-gate cost equals the parameter-shift estimate
`psrEstimate`. Proved by feeding
the Task-C frequency-1 form into the existing `ParamShiftModel.parameter_shift`;
the derivative is of
the `ℝ → ℝ` trigonometric cost, *not* a Fréchet derivative of the matrix exponential. -/
theorem parameter_shift {M : ℕ} {ψ : m → ℂ} {O : Matrix m m ℂ} {H : Fin M → Matrix m m ℂ}
    (hH : ∀ k, (H k) * (H k) = 1) (hHerm : ∀ k, (H k)ᴴ = H k) (hO : Oᴴ = O) (θ : Fin M → ℝ)
    (k : Fin M) :
    deriv (fun t => cost ψ O H (Function.update θ k t)) (θ k) = psrEstimate ψ O H θ k :=
  (costModel ψ O H hH hHerm hO θ k).parameter_shift (θ k)

namespace MultiGateAnsatz

/-- Main theorem: the algebraic parameter-shift rule for the multi-gate variational ansatz. -/
theorem main {M : ℕ} {ψ : m → ℂ} {O : Matrix m m ℂ} {H : Fin M → Matrix m m ℂ}
    (hH : ∀ k, (H k) * (H k) = 1) (hHerm : ∀ k, (H k)ᴴ = H k) (hO : Oᴴ = O) (θ : Fin M → ℝ)
    (k : Fin M) :
    deriv (fun t => cost ψ O H (Function.update θ k t)) (θ k) = psrEstimate ψ O H θ k :=
  parameter_shift hH hHerm hO θ k

end MultiGateAnsatz

/-! ### Task E — the n-qubit Pauli-string witness and the DLA interface

The abstract generator hypotheses (`Hₖ² = 1`, Hermitian) are realized by the genuine `n`-qubit Pauli
strings `pauliMat s` of `PauliStringDLA`: each is Hermitian
(`pauliMat_isHermitian`) and squares to `1`
(`pauliMat_sq`, from `PauliAlgebra`). The skew-Hermitian
generators `i·pauliMat s` are exactly the generators of an `su(2ⁿ)`-type dynamical Lie algebra — so
this is the ansatz substrate whose QFIM (`QuantumAlg.qfim`) the
overparametrization analysis consumes.
-/

/-- **Witness: the multi-gate parameter-shift rule on a genuine `n`-qubit Pauli-string ansatz.**
For any Pauli-string generators `s : Fin M → (Fin n → Fin 4)` — whose `i·pauliMat (s j)` are the
skew-Hermitian generators of an `su(2ⁿ)`-type dynamical Lie algebra — any state `ψ` and Hermitian
observable `O`, the exact `k`-th partial derivative of the variational cost
equals the parameter-shift
estimate. Non-vacuous instantiation of `MultiGateAnsatz.main` on real quantum generators. -/
theorem pauliAnsatz_parameter_shift {n M : ℕ} (ψ : Fin (2 ^ n) → ℂ)
    (O : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (hO : Oᴴ = O)
    (s : Fin M → (Fin n → Fin 4)) (θ : Fin M → ℝ) (k : Fin M) :
    deriv (fun t => cost ψ O (fun j => pauliMat (s j)) (Function.update θ k t)) (θ k)
      = psrEstimate ψ O (fun j => pauliMat (s j)) θ k :=
  MultiGateAnsatz.main (fun j => pauliMat_sq (s j)) (fun j => pauliMat_isHermitian (s j)) hO θ k

end QuantumAlg
