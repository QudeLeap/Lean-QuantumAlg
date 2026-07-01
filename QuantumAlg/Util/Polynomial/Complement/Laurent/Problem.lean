/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.Complex
public import QuantumAlg.Util.Polynomial.Laurent

/-!
# Laurent complement problems

Stage module for Laurent norm, residual, and bounded-on-circle problems.
-/

@[expose] public section

namespace QuantumAlg

open Polynomial Complex

noncomputable section

namespace Complement.Laurent.Problem

/-- The reflected-conjugate product representing `|F(x)|^2` under the Laurent
encoding. -/
def normPolynomial (L : ℕ) (F : ℂ[X]) : ℂ[X] :=
  F * (conjP F).reflect L

/-- The residual Laurent polynomial `1-|F|²` at budget `L`, encoded as
`X^L - F·F*`.  This is the polynomial called `1-PP*` in Wang's Laurent
complement proof [WZYW23, arxiv_v3.tex:2260-2274]. -/
def residualPolynomial (L : ℕ) (F : ℂ[X]) : ℂ[X] :=
  X ^ L - normPolynomial L F

/-- Pointwise boundedness of a Laurent/Fourier polynomial on the unit circle,
in the `lEval` encoding used by trigonometric QSP. -/
def BoundedOnCircle (L : ℕ) (A : ℂ[X]) : Prop :=
  ∀ x : ℝ, ‖lEval L A x‖ ≤ 1

/-- Data package for the bounded Laurent complement theorem before choosing a
particular complement. -/
structure BoundedComplementProblem (L : ℕ) (A : ℂ[X]) where
  degree_A : A.degree ≤ L
  bounded : BoundedOnCircle L A

end Complement.Laurent.Problem

end

end QuantumAlg
