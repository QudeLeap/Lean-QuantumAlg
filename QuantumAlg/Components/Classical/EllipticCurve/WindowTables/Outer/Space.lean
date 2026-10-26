/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Tables
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Coefficient.Resources
import all QuantumAlg.Util.Classical.NumberTheory.Extended.Bounds

/-!
# Exact native storage components of the actual table lifetimes

The persistent ten-cell frame and five per-window arrays are read directly
from their real allocated shapes. The original coefficient routine retains
its true widened execution width and larger sequential scratch scope. A
proved quadratic bound is used for numeric display, without evaluating its
finite maximum or changing any executable width.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer

open ClassicalAlgorithms.NumberTheory.XGCD
open NumberTheory.XGCD.Native NumberTheory.Checked.SignedReduction
open NumberTheory.Checked.SignedReduction.Native Modular.Reduce.Native

attribute [local irreducible] executionCoefficientWidth

/-- Storage of the actual four-word/constants/two-small-array package. -/
def sharedSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  ((sharedShapes width).map SpacePool.ofShape).sum

/-- Storage of the five actual complete arrays simultaneously live in one window. -/
def tableSpace (kind : ProblemKind) (width length : Nat) : SpacePool kind :=
  ((tableShapes width length).map SpacePool.ofShape).sum

/-- The original coefficient cells coexist with the maximum actual sequential arithmetic scope. -/
def coefficientScratchSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  ((Field.Native.coefficientShapes width).map SpacePool.ofShape).sum +
    Field.Native.coefficientActiveSpace kind width

/-- The two original seventeen-row families and four scalar work words are fully charged. -/
lemma sharedSpace_classicalBits (kind : ProblemKind) (width : Nat) :
    sharedSpace kind width .classicalBits = 76 * width + 1 := by
  simp [sharedSpace, sharedShapes, SpacePool.ofShape]
  omega

/-- Every original row and every bit of all five physical arrays is included. -/
lemma tableSpace_classicalBits (kind : ProblemKind) (width length : Nat) :
    tableSpace kind width length .classicalBits = 5 * length * width := by
  simp [tableSpace, tableShapes, SpacePool.ofShape, Nat.mul_assoc]
  omega

/-- The existing widened coefficient engine keeps its original physical scratch formula. -/
lemma coefficientScratchSpace_classicalBits (kind : ProblemKind) (width : Nat) :
    coefficientScratchSpace kind width .classicalBits =
      9 * executionCoefficientWidth (width + 1) + 8 * width + 9 := by
  have smaller : max (executionCoefficientWidth (width + 1)) (width + 1 + (width + 1)) ≤
      6 * executionCoefficientWidth (width + 1) + 4 * width + 5 :=
    max_le (by omega) (by omega)
  have dominated :
      max (executionCoefficientWidth (width + 1)) (width + 1 + (width + 1)) +
          (width + 1) + width + 1 + executionCoefficientWidth (width + 1) ≤
        width + 1 + (5 * (width + 1) + 7 * executionCoefficientWidth (width + 1) + 1) := by
    omega
  suffices reduced : executionCoefficientWidth (width + 1) +
      (executionCoefficientWidth (width + 1) + (width + 1 + (width + 1))) +
        Nat.max (width + 1 + (5 * (width + 1) + 7 * executionCoefficientWidth (width + 1) + 1))
          (max (executionCoefficientWidth (width + 1)) (width + 1 + (width + 1)) +
            (width + 1) + width + 1 + executionCoefficientWidth (width + 1)) =
              9 * executionCoefficientWidth (width + 1) + 8 * width + 9 by
    simpa [coefficientScratchSpace, Field.Native.coefficientShapes,
      Field.Native.coefficientActiveSpace, signedReductionSpaceLimit,
      signedReductionScratchSpace, signedReductionArithmeticSpace,
      negativeCorrectionScratchSpace, divisionShape, SpacePool.ofShape, SpacePool.max,
      xgcdNativeRawScratch_classicalBits, signedWidth, xgcdWidth,
      NumberTheory.XGCD.PureXGCD.executionCoefficientWidth] using reduced
  rw [Nat.max_eq_max, Nat.max_eq_left dominated]
  omega

private lemma fixed_scratch_limit {coefficientWidth : Nat}
    (fitted : coefficientWidth ≤ 132358) :
    9 * coefficientWidth + 8 * 256 + 9 ≤ 1193279 := by omega

/-- The actual original 257-bit coefficient execution width has its proved numeric ceiling. -/
lemma coefficientScratchSpace256_classicalBits_le (kind : ProblemKind) :
    coefficientScratchSpace kind 256 .classicalBits ≤ 1193279 := by
  rw [coefficientScratchSpace_classicalBits]
  exact fixed_scratch_limit executionCoefficientWidth_257_le

/-- Allocating these actual classical cells adds no system of any quantum dimension. -/
lemma sharedSpace_quantumSystems (width : Nat) (dimension : ℕ+) :
    sharedSpace .quantum width (.quantumSystems dimension) = 0 := by
  simp [sharedSpace, sharedShapes, SpacePool.ofShape]

/-- All five complete arrays are classical storage rather than additional quantum systems. -/
lemma tableSpace_quantumSystems (width length : Nat) (dimension : ℕ+) :
    tableSpace .quantum width length (.quantumSystems dimension) = 0 := by
  simp [tableSpace, tableShapes, SpacePool.ofShape]

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer
