/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.Polynomial.Complement.Interval.Roots

/-!
# Interval complement products

Stage module for interval-complement grouped root-product data.
-/

@[expose] public section

namespace QuantumAlg

open Polynomial

namespace Complement.Interval.Product

/-- Source-root data before choosing one representative from each root class.
It combines the complex product factorization with the sign/parity facts that
justify the source's root grouping [GSLW19, BlockHam.tex:442-456]. -/
structure SourceRootProductData (A : ℝ[X]) where
  /-- Multiset of complex roots used by the source product factorization. -/
  roots : Multiset ℂ
  product_eq :
    realPolynomialToComplex A =
      Polynomial.C (realPolynomialToComplex A).leadingCoeff *
        (roots.map fun z => X - C z).prod
  facts : Complement.Interval.Roots.SourceRootClassFacts A

end Complement.Interval.Product

end QuantumAlg
