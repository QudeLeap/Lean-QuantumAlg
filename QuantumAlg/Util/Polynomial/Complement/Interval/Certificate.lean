/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.Polynomial.Complement.Interval.Product

/-!
# Interval complement certificates

Stage module for interval-complement degree, parity, and product certificates.
-/

@[expose] public section

namespace QuantumAlg

open Polynomial

namespace Complement.Interval.Certificate

/-- The interval square decomposition promised by [GSLW19,
BlockHam.tex:436-480]:

`A = B^2 + (1 - X^2) * C^2`.

The source proof also tracks degree and parity bounds; they are fields here so
later QSP/QSVT modules can consume the certificate without re-reading the root
classification proof. -/
structure SquareCertificate (A : ℝ[X]) where
  /-- First real-polynomial square factor in the interval decomposition. -/
  B : ℝ[X]
  /-- Second real-polynomial square factor multiplied by `1 - X^2`. -/
  C : ℝ[X]
  eq_decomposition : A = B ^ 2 + (1 - X ^ 2) * C ^ 2

/-- The full degree/parity certificate promised by Gilyen--Su--Low--Wiebe
[GSLW19, BlockHam.tex:436-480].

The source writes `deg(C) <= k-1`; the Lean fields record the product-friendly
bound `deg(C) <= k` together with the opposite parity `k+1 (mod 2)`. Together
these exclude a top-degree `k` term except for the zero boundary case, while
avoiding partial subtraction in downstream code. -/
structure DegreeParityCertificate (A : ℝ[X]) (k : ℕ) where
  /-- First square factor with degree and parity bounded by `k`. -/
  B : ℝ[X]
  /-- Second square factor with opposite parity and interval endpoint factor. -/
  C : ℝ[X]
  eq_decomposition : A = B ^ 2 + (1 - X ^ 2) * C ^ 2
  degree_B : B.natDegree ≤ k
  degree_C : C.natDegree ≤ k
  parity_B : Complement.Interval.HasRealParity B k
  parity_C : Complement.Interval.HasRealParity C (k + 1)

end Complement.Interval.Certificate

end QuantumAlg
