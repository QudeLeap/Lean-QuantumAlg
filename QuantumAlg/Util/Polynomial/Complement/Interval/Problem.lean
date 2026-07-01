/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.Polynomial.Basic
public import Mathlib.Data.Real.Basic

/-!
# Interval complement problems

Stage module for interval-complement source hypotheses.
-/

@[expose] public section

namespace QuantumAlg

open Polynomial

namespace Complement.Interval.Problem

/-- Parity predicate for real polynomials: all nonzero coefficients have degree
congruent to `p` modulo `2`. -/
def HasRealParity (P : ℝ[X]) (p : ℕ) : Prop :=
  ∀ k, P.coeff k ≠ 0 → k % 2 = p % 2

/-- A real polynomial is nonnegative on the source interval `[-1,1]`. -/
def NonnegativeOnUnitInterval (P : ℝ[X]) : Prop :=
  ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → 0 ≤ P.eval x

/-- A real polynomial is bounded in absolute value by one on `[-1,1]`. -/
def BoundedByOneOnUnitInterval (P : ℝ[X]) : Prop :=
  ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → |P.eval x| ≤ 1

/-- Input hypotheses of the interval-square decomposition theorem in
[GSLW19, BlockHam.tex:436-438]. -/
structure SourceHypotheses (A : ℝ[X]) (k : ℕ) : Prop where
  degree_le : A.natDegree ≤ 2 * k
  even : HasRealParity A 0
  nonnegative : NonnegativeOnUnitInterval A

end Complement.Interval.Problem

namespace Complement.Interval

/-- Public interval-stage alias for real-polynomial parity. -/
abbrev HasRealParity := Problem.HasRealParity

/-- Public interval-stage alias for nonnegativity on `[-1, 1]`. -/
abbrev NonnegativeOnUnitInterval :=
  Problem.NonnegativeOnUnitInterval

/-- Public interval-stage alias for boundedness by one on `[-1, 1]`. -/
abbrev BoundedByOneOnUnitInterval :=
  Problem.BoundedByOneOnUnitInterval

/-- Public interval-stage alias for source hypotheses. -/
abbrev SourceHypotheses := Problem.SourceHypotheses

end Complement.Interval

end QuantumAlg
