/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.Polynomial.Complement.Laurent.Product

/-!
# Laurent complement certificates

Stage module for Laurent square-root and source-root complement certificates.
-/

@[expose] public section

namespace QuantumAlg

open Polynomial Complex

noncomputable section

namespace Complement.Laurent.Certificate

/-- A Laurent square-root factorization at budget `L`: `B` is a square root of
`R` in the reflected-conjugate sense used by trigonometric QSP. -/
structure SquareRootCertificate (L : ℕ) (R : ℂ[X]) where
  /-- Laurent square-root polynomial for the residual target. -/
  root : ℂ[X]
  degree_root : root.degree ≤ L
  factor_eq : Complement.Laurent.Problem.normPolynomial L root = R

/-- A complementary Laurent polynomial for `A` at budget `L`. -/
structure ComplementCertificate (L : ℕ) (A : ℂ[X]) where
  /-- Complementary Laurent polynomial paired with `A`. -/
  complement : ℂ[X]
  degree_complement : complement.degree ≤ L
  normalization :
    Complement.Laurent.Problem.normPolynomial L A +
      Complement.Laurent.Problem.normPolynomial L complement = X ^ L

end Complement.Laurent.Certificate

end

end QuantumAlg
