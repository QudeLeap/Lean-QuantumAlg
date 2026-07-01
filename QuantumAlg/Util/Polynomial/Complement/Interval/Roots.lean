/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.Polynomial.Complement.Interval.Problem
public import QuantumAlg.Util.Complex

/-!
# Interval complement root classes

Stage module for interval-complement root multiplicity and orbit facts.
-/

@[expose] public section

namespace QuantumAlg

open Polynomial

namespace Complement.Interval.Roots

/-- Root-class facts extracted from the source hypotheses in the proof of the
interval-square decomposition [GSLW19, BlockHam.tex:442-456].

The eventual product construction consumes this package rather than re-proving
sign-change or symmetry facts at each root class. -/
structure SourceRootClassFacts (A : ℝ[X]) where
  zero_multiplicity_even : Even (A.rootMultiplicity 0)
  interior_multiplicity_even :
    ∀ s : ℝ, s ∈ Set.Ioo (-1 : ℝ) 1 → Even (A.rootMultiplicity s)
  complex_ofReal_multiplicity :
    ∀ s : ℝ,
      (realPolynomialToComplex A).rootMultiplicity (s : ℂ) =
        A.rootMultiplicity s
  complex_neg_multiplicity :
    ∀ z : ℂ,
      (realPolynomialToComplex A).rootMultiplicity (-z) =
        (realPolynomialToComplex A).rootMultiplicity z
  complex_conj_multiplicity :
    ∀ z : ℂ,
      (realPolynomialToComplex A).rootMultiplicity (starRingEnd ℂ z) =
        (realPolynomialToComplex A).rootMultiplicity z

namespace SourceRootClassFacts

private theorem two_mul_half_of_even {n : ℕ} (h : Even n) : 2 * (n / 2) = n := by
  rcases h with ⟨m, rfl⟩
  have hdouble : m + m = 2 * m := by omega
  rw [hdouble, Nat.mul_div_right m (by norm_num : 0 < 2)]

/-- Zero-root evenness transported to the complexified polynomial. -/
theorem complex_zero_multiplicity_even {A : ℝ[X]} (facts : SourceRootClassFacts A) :
    Even ((realPolynomialToComplex A).rootMultiplicity (0 : ℂ)) := by
  change Even ((realPolynomialToComplex A).rootMultiplicity ((0 : ℝ) : ℂ))
  rw [facts.complex_ofReal_multiplicity 0]
  exact facts.zero_multiplicity_even

/-- Interior real-root evenness transported to the complexified polynomial. -/
theorem complex_ofReal_interior_multiplicity_even {A : ℝ[X]}
    (facts : SourceRootClassFacts A) {s : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 1) :
    Even ((realPolynomialToComplex A).rootMultiplicity (s : ℂ)) := by
  rw [facts.complex_ofReal_multiplicity s]
  exact facts.interior_multiplicity_even s hs

/-- Multiplicity of a real root after complexifying the source polynomial.
The receiver is retained so later source-root facts can use dot notation. -/
@[nolint unusedArguments]
noncomputable def complexRealRootMultiplicity {A : ℝ[X]} (_facts : SourceRootClassFacts A)
    (s : ℝ) : ℕ :=
  (realPolynomialToComplex A).rootMultiplicity (s : ℂ)

/-- Even-polynomial symmetry identifies the multiplicities of `s` and `-s`
after complexification. -/
theorem complexRealRootMultiplicity_neg {A : ℝ[X]} (facts : SourceRootClassFacts A)
    (s : ℝ) :
    facts.complexRealRootMultiplicity (-s) = facts.complexRealRootMultiplicity s := by
  unfold complexRealRootMultiplicity
  have hneg : ((-s : ℝ) : ℂ) = -(s : ℂ) := by norm_num
  rw [hneg, facts.complex_neg_multiplicity]

/-- Number of paired zero-root factors in the complexified source product.
The receiver is retained so later source-root facts can use dot notation. -/
@[nolint unusedArguments]
noncomputable def zeroRootPairCount {A : ℝ[X]} (_facts : SourceRootClassFacts A) : ℕ :=
  (realPolynomialToComplex A).rootMultiplicity (0 : ℂ) / 2

/-- The paired zero-root count accounts for all zero-root multiplicity. -/
theorem two_mul_zeroRootPairCount {A : ℝ[X]} (facts : SourceRootClassFacts A) :
    2 * facts.zeroRootPairCount =
      (realPolynomialToComplex A).rootMultiplicity (0 : ℂ) :=
  two_mul_half_of_even facts.complex_zero_multiplicity_even

/-- Number of paired real-root factors for a real root inside `(-1,1)`.
The receiver is retained so later source-root facts can use dot notation. -/
@[nolint unusedArguments]
noncomputable def interiorRealRootPairCount {A : ℝ[X]} (_facts : SourceRootClassFacts A)
    (s : ℝ) : ℕ :=
  (realPolynomialToComplex A).rootMultiplicity (s : ℂ) / 2

/-- Interior real-root pair counts are invariant under `s ↦ -s`. -/
theorem interiorRealRootPairCount_neg {A : ℝ[X]} (facts : SourceRootClassFacts A)
    (s : ℝ) :
    facts.interiorRealRootPairCount (-s) = facts.interiorRealRootPairCount s := by
  unfold interiorRealRootPairCount
  change facts.complexRealRootMultiplicity (-s) / 2 =
    facts.complexRealRootMultiplicity s / 2
  rw [facts.complexRealRootMultiplicity_neg s]

/-- The paired interior-root count accounts for full multiplicity at `s`. -/
theorem two_mul_interiorRealRootPairCount {A : ℝ[X]} (facts : SourceRootClassFacts A)
    {s : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 1) :
    2 * facts.interiorRealRootPairCount s =
      (realPolynomialToComplex A).rootMultiplicity (s : ℂ) :=
  two_mul_half_of_even (facts.complex_ofReal_interior_multiplicity_even hs)

end SourceRootClassFacts

end Complement.Interval.Roots

end QuantumAlg
