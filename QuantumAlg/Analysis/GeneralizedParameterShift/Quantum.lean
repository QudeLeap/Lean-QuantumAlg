/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.GeneralizedParameterShift.Trigonometric
import all QuantumAlg.Analysis.GeneralizedParameterShift.Trigonometric
import all QuantumAlg.Util.DirichletKernel
public import QuantumAlg.Core.Base.Hamiltonian
public import QuantumAlg.Util.Matrix.SpectralFourier
import QuantumAlg.Util.Polynomial.FiniteFourier
import Mathlib.Tactic

/-!
# Generalized parameter shifts for a quantum expectation

For Hermitian `G` and `O`, the loss is the actual expectation
`⟨ψ| exp(ixG)† O exp(ixG) |ψ⟩`, not supplied trigonometric data.
The matrix spectral theorem proves its finite Fourier expansion; if the distinct
positive eigenvalue gaps are exactly `1, …, R`, this gives the trigonometric form
needed by both generalized parameter-shift identities.

The zero-frequency part includes all pairs of equal eigenvalues, so no
nondegeneracy assumption is imposed [WIWL22, main.tex:302-330].
The first- and second-derivative weights are those of
[WIWL22, main.tex:483-484].
-/

@[expose] public section

namespace QuantumAlg.GeneralizedParamShift

open Matrix
open scoped BigOperators

noncomputable section

variable {Q : Register}

/-- The real expectation of the observable after the actual matrix exponential `exp(ixG)`. -/
def quantumLoss (G O : Hamiltonian Q) (ψ : NormalizedVector Q) (x : ℝ) : ℝ :=
  let U := NormedSpace.exp (((x : ℂ) * Complex.I) • (G : HilbertOperator Q))
  (star ψ.vec.ofLp ⬝ᵥ
    ((Uᴴ * (O : HilbertOperator Q) * U) *ᵥ ψ.vec.ofLp)).re

/-- The distinct positive eigenvalue gaps are exactly the integers `1, …, R`.
This fixes the normalized parameter used by the displayed shift formulas. -/
def NormalizedGaps (G : Hamiltonian Q) (R : ℕ) : Prop :=
  ∀ ω : ℝ,
    (∃ i j : Q.Index, G.eigenvalues i < G.eigenvalues j ∧
      ω = G.eigenvalues j - G.eigenvalues i) ↔
    ∃ p ∈ Finset.Icc 1 R, ω = (p : ℝ)

/-- The complex expectation equals the real-valued loss, because the observable is Hermitian. -/
lemma quantumLoss_complex (G O : Hamiltonian Q) (ψ : NormalizedVector Q) (x : ℝ) :
    let U := NormedSpace.exp (((x : ℂ) * Complex.I) • (G : HilbertOperator Q))
    star ψ.vec.ofLp ⬝ᵥ
        ((Uᴴ * (O : HilbertOperator Q) * U) *ᵥ ψ.vec.ofLp) =
      (quantumLoss G O ψ x : ℂ) := by
  dsimp only [quantumLoss]
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using
      Matrix.hermitian_exponential_expectation_real (G := (G : HilbertOperator Q))
        O.isHermitian ψ.vec.ofLp x

/-- Finite Fourier representation for every Hermitian generator, with arbitrary real spectrum.
The coefficients are computed in its orthonormal eigenbasis. All zero-frequency
cross terms remain in the double sum. -/
lemma quantumLoss_fourier (G O : Hamiltonian Q) (ψ : NormalizedVector Q) (x : ℝ) :
    quantumLoss G O ψ x =
      ∑ i, ∑ j,
        (Matrix.spectralExpectationCoeff G.isHermitian (O : HilbertOperator Q)
          ψ.vec.ofLp i j *
          Complex.exp ((((G.eigenvalues j - G.eigenvalues i) * x : ℝ) : ℂ) *
            Complex.I)).re := by
  have h := congrArg Complex.re
    (Matrix.hermitian_exponential_expectation_fourier G.isHermitian
      (O : HilbertOperator Q) ψ.vec.ofLp x)
  simpa only [quantumLoss, Hamiltonian.eigenvalues, Complex.re_sum] using h

/-- Real cosine-sine form for an arbitrary Hermitian spectrum. Repeated frequencies
are permitted; in particular, every equal-eigenvalue pair contributes its real coefficient. -/
lemma quantumLoss_spectral_trigonometric (G O : Hamiltonian Q)
    (ψ : NormalizedVector Q) (x : ℝ) :
    quantumLoss G O ψ x =
      ∑ i, ∑ j,
        ((Matrix.spectralExpectationCoeff G.isHermitian (O : HilbertOperator Q)
            ψ.vec.ofLp i j).re *
          Real.cos ((G.eigenvalues j - G.eigenvalues i) * x) -
        (Matrix.spectralExpectationCoeff G.isHermitian (O : HilbertOperator Q)
            ψ.vec.ofLp i j).im *
          Real.sin ((G.eigenvalues j - G.eigenvalues i) * x)) := by
  rw [quantumLoss_fourier]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact Complex.re_mul_exp_real_phase _ _

/-- The actual quantum loss is a real trigonometric polynomial in the normalized gap domain.
The representation is proved from the generator and observable, not assumed by the caller. -/
lemma quantumLoss_trigonometric (G O : Hamiltonian Q) (ψ : NormalizedVector Q)
    (R : ℕ) (hgap : NormalizedGaps G R) :
    ∃ a b : ℕ → ℝ, quantumLoss G O ψ = genTrigCost a b R := by
  let c : Q.Index × Q.Index → ℂ := fun ij =>
    Matrix.spectralExpectationCoeff G.isHermitian (O : HilbertOperator Q)
      ψ.vec.ofLp ij.1 ij.2
  let γ : Q.Index × Q.Index → ℝ := fun ij =>
    G.eigenvalues ij.2 - G.eigenvalues ij.1
  have hγ : ∀ ij ∈ (Finset.univ : Finset (Q.Index × Q.Index)),
      γ ij = 0 ∨ ∃ p ∈ Finset.Icc 1 R, γ ij = (p : ℝ) ∨ γ ij = -(p : ℝ) := by
    intro ij _
    rcases lt_trichotomy (G.eigenvalues ij.1) (G.eigenvalues ij.2) with hlt | heq | hgt
    · obtain ⟨p, hp, he⟩ := (hgap (γ ij)).mp ⟨ij.1, ij.2, hlt, rfl⟩
      exact Or.inr ⟨p, hp, Or.inl he⟩
    · exact Or.inl (sub_eq_zero.mpr heq.symm)
    · obtain ⟨p, hp, he⟩ := (hgap (G.eigenvalues ij.1 - G.eigenvalues ij.2)).mp
        ⟨ij.2, ij.1, hgt, rfl⟩
      refine Or.inr ⟨p, hp, Or.inr ?_⟩
      dsimp only [γ]
      linarith
  obtain ⟨a, b, hab⟩ := Complex.finite_integer_fourier_has_trig Finset.univ c γ R hγ
  refine ⟨a, b, funext fun x => ?_⟩
  rw [quantumLoss_fourier]
  simpa only [c, γ, genTrigCost, Fintype.sum_prod_type] using hab x

/-- Both generalized parameter-shift rules for the actual quantum expectation
[WIWL22, main.tex:483-484]. The parameter is normalized by `NormalizedGaps`;
no spectral simplicity or supplied Fourier-representation premise is required. -/
public theorem quantumMain (G O : Hamiltonian Q) (ψ : NormalizedVector Q)
    (R : ℕ) (hR : 1 ≤ R) (hgap : NormalizedGaps G R) :
    deriv (quantumLoss G O ψ) 0 =
        ∑ μ ∈ Finset.Icc 1 (2 * R),
          quantumLoss G O ψ ((2 * (μ : ℝ) - 1) * Real.pi / (2 * R)) *
            ((-1 : ℝ) ^ (μ - 1) /
              (4 * R * Real.sin ((2 * (μ : ℝ) - 1) * Real.pi / (4 * R)) ^ 2)) ∧
      deriv (deriv (quantumLoss G O ψ)) 0 =
        -quantumLoss G O ψ 0 * (2 * (R : ℝ) ^ 2 + 1) / 6 +
          ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
            quantumLoss G O ψ ((μ : ℝ) * Real.pi / R) *
              ((-1 : ℝ) ^ (μ - 1) / (2 * Real.sin ((μ : ℝ) * Real.pi / (2 * R)) ^ 2)) := by
  obtain ⟨a, b, hrepr⟩ := quantumLoss_trigonometric G O ψ R hgap
  let data : QuantumAlg.GeneralizedParamShift R := ⟨a, b, hR⟩
  rw [hrepr]
  constructor
  · simpa only [data, psPoint, psWeight] using data.firstDeriv
  · simpa only [data, psPoint2, psWeight2] using data.secondDeriv

end

end QuantumAlg.GeneralizedParamShift
