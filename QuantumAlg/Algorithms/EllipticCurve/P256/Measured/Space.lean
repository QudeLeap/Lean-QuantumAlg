/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Space

/-!
# Original P-256 coordinates of the actual independent space allowance

The original 256-bit physical field word and 260-bit sample words give 1336
qubits, with no other quantum dimension. If `C u = executionCoefficientWidth u`,
the successive classical scratch allowance is
`max (6516 + 9*C 261) (6927 + 9*C 257)` bits. The complete resident allowance
adds 2839 bits, and the auxiliary allowance adds 1813 bits.

`C 257` and `C 261` are the actual original widened XGCD widths, not substituted
public-coefficient widths or a former execution-space constant. These are
independent allowance identities; they neither define a second run nor assert
that every actual path reaches the allowance. Repetition does not multiply
any live space coordinate.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured

open PrimeFieldShortWeierstrass FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native
open ECDLP.Measured

attribute [local irreducible] ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth

private theorem signed_width (width : Nat) :
    ClassicalRoutines.NumberTheory.Checked.SignedReduction.signedWidth width =
      ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth (width + 1) := rfl

private theorem fixed_arithmetic (coefficient : Nat → Nat) (physical field sample : Nat)
    (copies extra total : Nat)
    (physicalValue : physical = 256) (fieldValue : field = 256) (sampleValue : sample = 260)
    (constantValue : copies * 256 + 4 * 260 + 256 + extra = total) :
    max (25 * sample + 9 * coefficient sample + 16)
        (27 * field + 9 * coefficient field + 15) +
      copies * field + 4 * sample + physical + extra =
      max (6516 + 9 * coefficient 260) (6927 + 9 * coefficient 256) + total := by
  subst physical field sample
  omega

private theorem fixed_widths (coefficient : Nat → Nat) (extra : Nat) :
    max (6516 + 9 * coefficient (260 + 1)) (6927 + 9 * coefficient (256 + 1)) + extra =
      max (6516 + 9 * coefficient 261) (6927 + 9 * coefficient 257) + extra := rfl

private theorem signed_coordinates (extra : Nat) :
    max (6516 + 9 * ClassicalRoutines.NumberTheory.Checked.SignedReduction.signedWidth 260)
        (6927 + 9 * ClassicalRoutines.NumberTheory.Checked.SignedReduction.signedWidth 256) +
        extra =
      max (6516 + 9 * ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth 261)
        (6927 + 9 * ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth 257) +
        extra :=
  (congrArg₂ (fun sample field => max (6516 + 9 * sample) (6927 + 9 * field) + extra)
    (signed_width 260) (signed_width 256)).trans
      (fixed_widths ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth extra)

/-- Complete classical resident bits, with the actual original XGCD widths retained. -/
theorem residentAllowance_classicalBits (I : DomainParameters.PublicKeyInstance) :
    let E := DomainParameters.curve I.curveCert
    let problem := ECDLP.Canonical.problem (Cascade.ecdlpInstance I)
    SpacePool.count .classicalBits
      (recoveryTailScratchSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
          (orderWidth problem) +
        persistentCellSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem) +
          (PublicInput.terminal E (orderWidth problem)).residentSpace) =
      max (6516 + 9 * ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth 261)
        (6927 + 9 * ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth 257) +
          2839 := by
  dsimp only
  exact (LogicalResources.residentAllowance_classicalBits _ _).trans
    ((fixed_arithmetic ClassicalRoutines.NumberTheory.Checked.SignedReduction.signedWidth
      _ _ _ 6 7 2839 fieldModulus_size (canonicalFieldWidth I.curveCert)
      (orderWidth_eq_260 I) rfl).trans (signed_coordinates _))

/-- Complete classical auxiliary bits omit precisely the two original borrowed point values. -/
theorem auxiliaryAllowance_classicalBits (I : DomainParameters.PublicKeyInstance) :
    let E := DomainParameters.curve I.curveCert
    let problem := ECDLP.Canonical.problem (Cascade.ecdlpInstance I)
    SpacePool.count .classicalBits
      (recoveryTailScratchSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
          (orderWidth problem) +
        persistentCellSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem) +
          (PublicInput.terminal E (orderWidth problem)).auxiliarySpace) =
      max (6516 + 9 * ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth 261)
        (6927 + 9 * ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth 257) +
          1813 := by
  dsimp only
  exact (LogicalResources.auxiliaryAllowance_classicalBits _ _).trans
    ((fixed_arithmetic ClassicalRoutines.NumberTheory.Checked.SignedReduction.signedWidth
      _ _ _ 2 5 1813 fieldModulus_size (canonicalFieldWidth I.curveCert)
      (orderWidth_eq_260 I) rfl).trans (signed_coordinates _))

/-- The original independent resident allowance has 1336 qubits and no other quantum systems. -/
theorem residentAllowance_quantumSystems (I : DomainParameters.PublicKeyInstance)
    (dimension : ℕ+) :
    let E := DomainParameters.curve I.curveCert
    let problem := ECDLP.Canonical.problem (Cascade.ecdlpInstance I)
    SpacePool.count (.quantumSystems dimension)
      (recoveryTailScratchSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
          (orderWidth problem) +
        persistentCellSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem) +
          (PublicInput.terminal E (orderWidth problem)).residentSpace) =
      if 2 = dimension then 1336 else 0 := by
  dsimp only
  rw [LogicalResources.residentAllowance_quantumSystems, orderWidth_eq_260, fieldModulus_size]
  rfl

/-- Auxiliary quantum coordinates equal the original resident quantum coordinates. -/
theorem auxiliaryAllowance_quantumSystems (I : DomainParameters.PublicKeyInstance)
    (dimension : ℕ+) :
    let E := DomainParameters.curve I.curveCert
    let problem := ECDLP.Canonical.problem (Cascade.ecdlpInstance I)
    SpacePool.count (.quantumSystems dimension)
      (recoveryTailScratchSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
          (orderWidth problem) +
        persistentCellSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem) +
          (PublicInput.terminal E (orderWidth problem)).auxiliarySpace) =
      if 2 = dimension then 1336 else 0 := by
  dsimp only
  rw [LogicalResources.auxiliaryAllowance_quantumSystems, orderWidth_eq_260, fieldModulus_size]
  rfl

end QuantumAlg.EllipticCurve.P256.Measured
