/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.Polynomial.Laurent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# Chebyshev-Fourier polynomial bridge

Quantum-free coefficient and normalization maps connecting Chebyshev-basis
polynomials with the Fourier/Laurent representation used by QSP.
-/

@[expose] public section

namespace QuantumAlg

noncomputable section

open Polynomial Complex
open scoped BigOperators

namespace ChebyshevFourierBridge

/-- The Fourier representative of the Chebyshev basis element `T_k`, padded to
degree budget `d`.  Under `lEval (2*d)`, this is
`(z^k + z^{-k}) / 2 = cos(k θ)` for `k > 0`, and `1` for `k = 0`. -/
def chebyshevModeToFourier (d k : ℕ) : ℂ[X] :=
  if k = 0 then X ^ d else C ((2 : ℂ)⁻¹) * (X ^ (d + k) + X ^ (d - k))

/-- A Chebyshev-basis coefficient family translated into the padded
Fourier/Laurent representative at budget `d`. -/
def chebyshevBasisToFourier (d : ℕ) (coeff : ℕ → ℂ) : ℂ[X] :=
  ∑ k ∈ Finset.range (d + 1), C (coeff k) * chebyshevModeToFourier d k

/-- The Fourier representative of `sin θ · T_k(cos θ)`, padded to degree
budget `d`.  This is the off-diagonal Chebyshev `Q` mode; the `k < d`
constraint is supplied by the caller through the summation range. -/
def chebyshevSineModeToFourier (d k : ℕ) : ℂ[X] :=
  C (((4 : ℂ) * Complex.I)⁻¹) *
    (X ^ (d + k + 1) + X ^ (d - k + 1) -
      X ^ (d + k - 1) - X ^ (d - k - 1))

/-- A Chebyshev-basis coefficient family translated into the padded
Fourier/Laurent representative of `sin θ · ∑ coeff k · T_k(cos θ)`. -/
def chebyshevSineBasisToFourier (d : ℕ) (coeff : ℕ → ℂ) : ℂ[X] :=
  ∑ k ∈ Finset.range d, C (coeff k) * chebyshevSineModeToFourier d k

/-- Extract the coefficient of `T_k` from a padded Fourier representative whose
support is centered at `d`.  The zero mode is read once, while nonzero modes are
the sum of the symmetric Fourier coefficients. -/
def fourierChebyshevCoeff (d : ℕ) (A : ℂ[X]) (k : ℕ) : ℂ :=
  if k = 0 then A.coeff d else A.coeff (d + k) + A.coeff (d - k)

/-- Fourier/Laurent representative translated back to a Chebyshev-basis
polynomial by reading symmetric coefficients around the center `d`. -/
def fourierToChebyshevBasis (d : ℕ) (A : ℂ[X]) : ℂ[X] :=
  ∑ k ∈ Finset.range (d + 1),
    C (fourierChebyshevCoeff d A k) * Polynomial.Chebyshev.T ℂ (k : ℤ)

@[simp]
theorem chebyshevModeToFourier_zero (d : ℕ) :
    chebyshevModeToFourier d 0 = X ^ d := by
  simp [chebyshevModeToFourier]

theorem chebyshevModeToFourier_pos {d k : ℕ} (hk : k ≠ 0) :
    chebyshevModeToFourier d k =
      C ((2 : ℂ)⁻¹) * (X ^ (d + k) + X ^ (d - k)) := by
  simp [chebyshevModeToFourier, hk]

end ChebyshevFourierBridge

/-- Chebyshev-to-Fourier translation map.  The input is a Chebyshev-basis
coefficient family `coeff`, representing `∑ coeff k · T_k`. -/
def chebyshevToFourierPoly (d : ℕ) (coeff : ℕ → ℂ) : ℂ[X] :=
  ChebyshevFourierBridge.chebyshevBasisToFourier d coeff

/-- Chebyshev-to-Fourier translation map for the off-diagonal QSP polynomial.
The input represents `∑ coeff k · T_k`; the output represents the Laurent
function `sin θ · ∑ coeff k · T_k(cos θ)` under `lEval (2*d)`. -/
def chebyshevSineToFourierPoly (d : ℕ) (coeff : ℕ → ℂ) : ℂ[X] :=
  ChebyshevFourierBridge.chebyshevSineBasisToFourier d coeff

/-- Fourier-to-Chebyshev translation map, reading symmetric Laurent coefficients
around the center `d` and returning a Chebyshev-basis polynomial. -/
def fourierToChebyshevPoly (d : ℕ) (A : ℂ[X]) : ℂ[X] :=
  ChebyshevFourierBridge.fourierToChebyshevBasis d A

/-- Pointwise Chebyshev normalization after the explicit substitution
`x = cos θ`. -/
def ChebyshevCosNormalization (P Q : ℂ[X]) : Prop :=
  ∀ θ : ℝ,
    P.eval (Real.cos θ : ℂ) * starRingEnd ℂ (P.eval (Real.cos θ : ℂ))
      + (1 - (Real.cos θ : ℂ) ^ 2) *
        (Q.eval (Real.cos θ : ℂ) * starRingEnd ℂ (Q.eval (Real.cos θ : ℂ))) = 1

/-- Pointwise Fourier/Laurent normalization on the unit circle. -/
def FourierCircleNormalization (L : ℕ) (A B : ℂ[X]) : Prop :=
  ∀ θ : ℝ,
    lEval L A θ * starRingEnd ℂ (lEval L A θ)
      + lEval L B θ * starRingEnd ℂ (lEval L B θ) = 1

/-- Data carried by a Chebyshev-Fourier translation candidate. -/
structure ChebyshevFourierTranslationData (d : ℕ)
    (P Q A B : ℂ[X]) where
  /-- Global phase shift used by the translation candidate. -/
  phaseShift : ℝ
  phaseShiftZero : phaseShift = 0
  variableSubstitution :
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → x = Real.cos (Real.arccos x)
  parityP : HasParity P d
  parityQ : HasParity Q (d + 1)
  /-- Chebyshev coefficients for the diagonal polynomial `P`. -/
  chebyshevCoeffP : ℕ → ℂ
  /-- Chebyshev coefficients for the off-diagonal polynomial `Q`. -/
  chebyshevCoeffQ : ℕ → ℂ
  chebyshevToFourierP : A = chebyshevToFourierPoly d chebyshevCoeffP
  chebyshevToFourierQ : B = chebyshevSineToFourierPoly d chebyshevCoeffQ
  fourierToChebyshevP : P = fourierToChebyshevPoly d A
  evalP :
    ∀ θ : ℝ, lEval (2 * d) A θ = P.eval (Real.cos θ : ℂ)
  evalQ :
    ∀ θ : ℝ, lEval (2 * d) B θ =
      (Real.sin θ : ℂ) * Q.eval (Real.cos θ : ℂ)

attribute [-simp] ChebyshevFourierTranslationData.mk.injEq
attribute [-simp] ChebyshevFourierTranslationData.mk.sizeOf_spec
-- Generated structure lemmas are intentionally not simp-normal forms; keep the
-- exception declaration-scoped instead of suppressing `simpNF` for the file.
attribute [nolint simpNF] ChebyshevFourierTranslationData.mk.injEq
attribute [nolint simpNF] ChebyshevFourierTranslationData.mk.sizeOf_spec

/-- The explicit Chebyshev-Fourier pointwise normalization equivalence. -/
theorem chebyshev_fourier_pointwise_normalization_iff {d : ℕ}
    {P Q A B : ℂ[X]}
    (hP : ∀ θ : ℝ, lEval (2 * d) A θ = P.eval (Real.cos θ : ℂ))
    (hQ : ∀ θ : ℝ, lEval (2 * d) B θ =
      (Real.sin θ : ℂ) * Q.eval (Real.cos θ : ℂ)) :
    FourierCircleNormalization (2 * d) A B ↔ ChebyshevCosNormalization P Q := by
  constructor
  · intro h θ
    have hs :
        (Real.sin θ : ℂ) * (Real.sin θ : ℂ) = 1 - (Real.cos θ : ℂ) ^ 2 := by
      have htrig := ofReal_sin_sq_add_cos_sq θ
      linear_combination htrig
    have hterm :
        (Real.sin θ : ℂ) * Q.eval (Real.cos θ : ℂ) *
            ((Real.sin θ : ℂ) *
              starRingEnd ℂ (Q.eval (Real.cos θ : ℂ))) =
          (1 - (Real.cos θ : ℂ) ^ 2) *
            (Q.eval (Real.cos θ : ℂ) *
              starRingEnd ℂ (Q.eval (Real.cos θ : ℂ))) := by
      rw [← hs]
      ring
    have hθ := h θ
    rw [hP θ, hQ θ, map_mul, Complex.conj_ofReal] at hθ
    rw [hterm] at hθ
    exact hθ
  · intro h θ
    have hs :
        (Real.sin θ : ℂ) * (Real.sin θ : ℂ) = 1 - (Real.cos θ : ℂ) ^ 2 := by
      have htrig := ofReal_sin_sq_add_cos_sq θ
      linear_combination htrig
    have hterm :
        (Real.sin θ : ℂ) * Q.eval (Real.cos θ : ℂ) *
            ((Real.sin θ : ℂ) *
              starRingEnd ℂ (Q.eval (Real.cos θ : ℂ))) =
          (1 - (Real.cos θ : ℂ) ^ 2) *
            (Q.eval (Real.cos θ : ℂ) *
              starRingEnd ℂ (Q.eval (Real.cos θ : ℂ))) := by
      rw [← hs]
      ring
    have hθ := h θ
    rw [hP θ, hQ θ, map_mul, Complex.conj_ofReal]
    rw [hterm]
    exact hθ

/-- Projection from translation data to the proved normalization equivalence. -/
theorem ChebyshevFourierTranslationData.normalization_equiv {d : ℕ}
    {P Q A B : ℂ[X]} (h : ChebyshevFourierTranslationData d P Q A B) :
    FourierCircleNormalization (2 * d) A B ↔ ChebyshevCosNormalization P Q :=
  chebyshev_fourier_pointwise_normalization_iff h.evalP h.evalQ

/-- Projection for the concrete Chebyshev-to-Fourier translation map. -/
theorem chebyshevToFourierPoly_eval (d : ℕ) (coeff : ℕ → ℂ) :
    chebyshevToFourierPoly d coeff =
      ∑ k ∈ Finset.range (d + 1),
        C (coeff k) * ChebyshevFourierBridge.chebyshevModeToFourier d k :=
  rfl

/-- Projection for the sine-weighted off-diagonal Chebyshev-to-Fourier map. -/
theorem chebyshevSineToFourierPoly_eval (d : ℕ) (coeff : ℕ → ℂ) :
    chebyshevSineToFourierPoly d coeff =
      ∑ k ∈ Finset.range d,
        C (coeff k) * ChebyshevFourierBridge.chebyshevSineModeToFourier d k :=
  rfl

/-- Projection for the concrete Fourier-to-Chebyshev coefficient extraction. -/
theorem fourierToChebyshevPoly_eval (d : ℕ) (A : ℂ[X]) :
    fourierToChebyshevPoly d A =
      ∑ k ∈ Finset.range (d + 1),
        C (ChebyshevFourierBridge.fourierChebyshevCoeff d A k) *
          Polynomial.Chebyshev.T ℂ (k : ℤ) :=
  rfl

end

end QuantumAlg
