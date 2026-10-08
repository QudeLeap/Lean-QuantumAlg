/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.Resources.Scalar.Spec
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Scalar.Spec
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Space
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Spec
import all QuantumAlg.Util.Classical.NumberTheory.Extended.Bounds

/-! # Symbolic memory ceilings preserving the original widened XGCD execution -/

namespace QuantumAlg.EllipticCurve.LogicalResources

noncomputable section

open Execution PrimeFieldShortWeierstrass FiniteCyclicDLP
open ClassicalRoutines.NumberTheory.Checked.SignedReduction

attribute [local irreducible] ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth

/-- The actual original signed-word width is bounded without evaluating operand maxima. -/
theorem signedWidth_scalar_le (width : Nat) :
    signedWidth width ≤ Scalar.coefficientBits width :=
  ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth_le_quadratic (width + 1)

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (I : ECDLPInstance E) (count : Nat)

omit [Fact p.Prime] in
/-- The complete problem's resident classical allowance has a parameter-only ceiling. -/
theorem residentBits_scalar_le :
    (resourceBudget E I count).resident .classicalBits ≤
      Scalar.residentBits p.size (ECDLP.Canonical.Layout.fieldWidth E)
        (orderWidth (ECDLP.Canonical.problem I)) := by
  change SpacePool.count .classicalBits _ ≤ _
  unfold resourceBudget
  rw [residentAllowance_classicalBits]
  have field := signedWidth_scalar_le (ECDLP.Canonical.Layout.fieldWidth E)
  have sample := signedWidth_scalar_le (orderWidth (ECDLP.Canonical.problem I))
  unfold Scalar.residentBits Scalar.scratchBits
  have scratch :
      max (25 * orderWidth (ECDLP.Canonical.problem I) +
          9 * signedWidth (orderWidth (ECDLP.Canonical.problem I)) + 16)
        (27 * ECDLP.Canonical.Layout.fieldWidth E +
          9 * signedWidth (ECDLP.Canonical.Layout.fieldWidth E) + 15) ≤
      max (25 * orderWidth (ECDLP.Canonical.problem I) +
          9 * Scalar.coefficientBits (orderWidth (ECDLP.Canonical.problem I)) + 16)
        (27 * ECDLP.Canonical.Layout.fieldWidth E +
          9 * Scalar.coefficientBits (ECDLP.Canonical.Layout.fieldWidth E) + 15) :=
    max_le_max (by omega) (by omega)
  omega

omit [Fact p.Prime] in
/-- Repetition reuses the complete auxiliary classical bank at every count. -/
theorem auxiliaryBits_scalar_le :
    (resourceBudget E I count).auxiliary .classicalBits ≤
      Scalar.auxiliaryBits p.size (ECDLP.Canonical.Layout.fieldWidth E)
        (orderWidth (ECDLP.Canonical.problem I)) := by
  change SpacePool.count .classicalBits _ ≤ _
  unfold resourceBudget
  rw [auxiliaryAllowance_classicalBits]
  have field := signedWidth_scalar_le (ECDLP.Canonical.Layout.fieldWidth E)
  have sample := signedWidth_scalar_le (orderWidth (ECDLP.Canonical.problem I))
  unfold Scalar.auxiliaryBits Scalar.scratchBits
  have scratch :
      max (25 * orderWidth (ECDLP.Canonical.problem I) +
          9 * signedWidth (orderWidth (ECDLP.Canonical.problem I)) + 16)
        (27 * ECDLP.Canonical.Layout.fieldWidth E +
          9 * signedWidth (ECDLP.Canonical.Layout.fieldWidth E) + 15) ≤
      max (25 * orderWidth (ECDLP.Canonical.problem I) +
          9 * Scalar.coefficientBits (orderWidth (ECDLP.Canonical.problem I)) + 16)
        (27 * ECDLP.Canonical.Layout.fieldWidth E +
          9 * Scalar.coefficientBits (ECDLP.Canonical.Layout.fieldWidth E) + 15) :=
    max_le_max (by omega) (by omega)
  omega

omit [Fact p.Prime] in
/-- Actual physical dimensions are retained: only qubits have a nonzero allowance. -/
theorem quantumSystems_scalar_eq (dimension : ℕ+) :
    (resourceBudget E I count).resident (.quantumSystems dimension) =
      if 2 = dimension then Scalar.qubits p.size (orderWidth (ECDLP.Canonical.problem I))
        else 0 := by
  change SpacePool.count (.quantumSystems dimension) _ = _
  unfold resourceBudget
  rw [residentAllowance_quantumSystems]
  rfl

omit [Fact p.Prime] in
/-- The auxiliary quantum allowance has those same dimensions and reused wires. -/
theorem auxiliaryQuantumSystems_scalar_eq (dimension : ℕ+) :
    (resourceBudget E I count).auxiliary (.quantumSystems dimension) =
      if 2 = dimension then Scalar.qubits p.size (orderWidth (ECDLP.Canonical.problem I))
        else 0 := by
  change SpacePool.count (.quantumSystems dimension) _ = _
  unfold resourceBudget
  rw [auxiliaryAllowance_quantumSystems]
  rfl

end

end QuantumAlg.EllipticCurve.LogicalResources
