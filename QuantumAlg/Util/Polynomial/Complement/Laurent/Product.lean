/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.Polynomial.Complement.Laurent.Roots

/-!
# Laurent complement products

Stage module for selected reciprocal roots and scalar-quotient product data.
-/

@[expose] public section

namespace QuantumAlg

open Polynomial Complex

noncomputable section

namespace Complement.Laurent.Product

/-- Root-product polynomial used in Wang's constructive square-root proof. -/
def sourceRootProduct (scale : ℂ) (roots : Multiset ℂ) : ℂ[X] :=
  C scale * (roots.map fun z => X - C z).prod

/-- A selected half of the reciprocal-conjugate root pairs for a target
polynomial.  Producing this data is the remaining root-classification content
of Wang's Laurent complement proof; the algebraic conversion to a square-root
certificate is `SourceSquareRootCertificate` [WZYW23, arxiv_v3.tex:2241-2257]. -/
structure ReciprocalConjRootSelection (L : ℕ) (R : ℂ[X]) where
  /-- Source scalar multiplying the selected root product. -/
  scale : ℂ
  /-- Selected half of the reciprocal-conjugate root pairs. -/
  roots : Multiset ℂ
  roots_card_eq : roots.card = L
  roots_nonzero : ∀ z ∈ roots, z ≠ 0
  pair_factor_eq :
    sourceRootProduct
        (scale * starRingEnd ℂ scale *
          (roots.map fun z => -(starRingEnd ℂ z)).prod)
        (roots + roots.map Complement.Laurent.Roots.reciprocalConj) = R

/-- A selected nonzero part of the reciprocal-conjugate root pairs, allowing
the remaining budget to be supplied by zero-root padding. -/
structure PaddedReciprocalConjRootSelection (L : ℕ) (R : ℂ[X]) where
  /-- Source scalar multiplying the selected nonzero root product. -/
  scale : ℂ
  /-- Selected nonzero roots before zero-root padding. -/
  roots : Multiset ℂ
  roots_card_le : roots.card ≤ L
  roots_nonzero : ∀ z ∈ roots, z ≠ 0
  padded_pair_factor_eq :
    X ^ (L - roots.card) *
      sourceRootProduct
        (scale * starRingEnd ℂ scale *
          (roots.map fun z => -(starRingEnd ℂ z)).prod)
        (roots + roots.map Complement.Laurent.Roots.reciprocalConj) = R

/-- Wang's source-facing root-product square-root certificate: a selected half
of the reciprocal-conjugate root pairs, together with the source scalar,
constructs a Laurent polynomial whose reflected-conjugate norm is the target
residual [WZYW23, arxiv_v3.tex:2249-2257]. -/
structure SourceSquareRootCertificate (L : ℕ) (R : ℂ[X]) where
  /-- Source scalar multiplying the selected root product. -/
  scale : ℂ
  /-- Selected roots used to form the square-root polynomial. -/
  roots : Multiset ℂ
  roots_card_le : roots.card ≤ L
  factor_eq :
    Complement.Laurent.Problem.normPolynomial L (sourceRootProduct scale roots) = R

/-- Source-facing factorization of a complex polynomial into all of its roots.
This records the first step of Wang's Laurent-complement proof before the roots
are classified into reciprocal-conjugate pairs [WZYW23, arxiv_v3.tex:2241-2248]. -/
structure FullRootProductFactorization (R : ℂ[X]) where
  /-- Leading scalar for the full root product. -/
  scale : ℂ
  /-- Full multiset of roots in the source product factorization. -/
  roots : Multiset ℂ
  factor_eq : sourceRootProduct scale roots = R

end Complement.Laurent.Product

end

end QuantumAlg
