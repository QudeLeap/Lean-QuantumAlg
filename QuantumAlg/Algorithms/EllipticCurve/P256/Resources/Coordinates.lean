/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Problem
public import QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Problem
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Space
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Spec

/-!
# Explicit coordinates of the independent complete P-256 problem

These projections belong to the same independent problem solved by the one
actual fixed run. Original widened coefficient encodings remain intact.
The classical formulas are exact allowance coordinates; they do not claim
a tight reached peak. Every dimension other than qubits has zero allowance.
-/

namespace QuantumAlg.EllipticCurve.P256LogicalResources

noncomputable section

attribute [local irreducible] ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth

private theorem resident_pool (I : P256.DomainParameters.PublicKeyInstance) :
    (problem I).resources.resident =
      ClassicalRoutines.EllipticCurve.CandidateCheck.Native.recoveryTailScratchSpace .quantum
          (PrimeFieldShortWeierstrass.ECDLP.Canonical.Layout.fieldWidth
            (P256.DomainParameters.curve I.curveCert))
          (FiniteCyclicDLP.orderWidth
            (PrimeFieldShortWeierstrass.ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I))) +
        ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentCellSpace .quantum
          (PrimeFieldShortWeierstrass.ECDLP.Canonical.Layout.fieldWidth
            (P256.DomainParameters.curve I.curveCert))
          (FiniteCyclicDLP.orderWidth
            (PrimeFieldShortWeierstrass.ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I))) +
        (PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput.terminal
          (P256.DomainParameters.curve I.curveCert)
          (FiniteCyclicDLP.orderWidth
            (PrimeFieldShortWeierstrass.ECDLP.Canonical.problem
              (P256.Cascade.ecdlpInstance I)))).residentSpace := rfl

private theorem auxiliary_pool (I : P256.DomainParameters.PublicKeyInstance) :
    (problem I).resources.auxiliary =
      ClassicalRoutines.EllipticCurve.CandidateCheck.Native.recoveryTailScratchSpace .quantum
          (PrimeFieldShortWeierstrass.ECDLP.Canonical.Layout.fieldWidth
            (P256.DomainParameters.curve I.curveCert))
          (FiniteCyclicDLP.orderWidth
            (PrimeFieldShortWeierstrass.ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I))) +
        ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentCellSpace .quantum
          (PrimeFieldShortWeierstrass.ECDLP.Canonical.Layout.fieldWidth
            (P256.DomainParameters.curve I.curveCert))
          (FiniteCyclicDLP.orderWidth
            (PrimeFieldShortWeierstrass.ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I))) +
        (PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput.terminal
          (P256.DomainParameters.curve I.curveCert)
          (FiniteCyclicDLP.orderWidth
            (PrimeFieldShortWeierstrass.ECDLP.Canonical.problem
              (P256.Cascade.ecdlpInstance I)))).auxiliarySpace := rfl

private def classicalBitLimit (coefficient : Nat → Nat) (extra : Nat) : Nat :=
  max (6516 + 9 * coefficient 261) (6927 + 9 * coefficient 257) + extra

private theorem classicalBitLimit_eq (coefficient : Nat → Nat) (extra : Nat) :
    max (6516 + 9 * coefficient 261) (6927 + 9 * coefficient 257) + extra =
      classicalBitLimit coefficient extra := rfl

/-- Resident classical bits retain the original 261-bit and 257-bit XGCD input widths. -/
public def residentClassicalBitLimit : Nat :=
  classicalBitLimit ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth 2839

/-- Auxiliary classical bits exclude precisely the two original borrowed public point encodings. -/
public def auxiliaryClassicalBitLimit : Nat :=
  classicalBitLimit ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth 1813

/-- The independent complete problem has the explicit original resident classical allowance. -/
public theorem resident_classicalBits (I : P256.DomainParameters.PublicKeyInstance) :
    SpacePool.count .classicalBits (problem I).resources.resident =
      residentClassicalBitLimit :=
  ((congrArg (SpacePool.count .classicalBits) (resident_pool I)).trans
    (P256.Measured.residentAllowance_classicalBits I)).trans
      (classicalBitLimit_eq ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth 2839)

/-- The independent complete problem has the corresponding auxiliary classical allowance. -/
public theorem auxiliary_classicalBits (I : P256.DomainParameters.PublicKeyInstance) :
    SpacePool.count .classicalBits (problem I).resources.auxiliary =
      auxiliaryClassicalBitLimit :=
  ((congrArg (SpacePool.count .classicalBits) (auxiliary_pool I)).trans
    (P256.Measured.auxiliaryAllowance_classicalBits I)).trans
      (classicalBitLimit_eq ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth 1813)

/-- Exactly 1336 qubits, and no other quantum dimensions, occur in the resident allowance. -/
public theorem resident_quantumSystems (I : P256.DomainParameters.PublicKeyInstance)
    (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension) (problem I).resources.resident =
      if 2 = dimension then 1336 else 0 :=
  (congrArg (SpacePool.count (.quantumSystems dimension)) (resident_pool I)).trans
    (P256.Measured.residentAllowance_quantumSystems I dimension)

/-- Quantum systems are counted equally in the auxiliary and resident allowances. -/
public theorem auxiliary_quantumSystems (I : P256.DomainParameters.PublicKeyInstance)
    (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension) (problem I).resources.auxiliary =
      if 2 = dimension then 1336 else 0 :=
  (congrArg (SpacePool.count (.quantumSystems dimension)) (auxiliary_pool I)).trans
    (P256.Measured.auxiliaryAllowance_quantumSystems I dimension)

/-- The complete exceptional-error budget requires exactly ninety-nine-percent success. -/
public theorem successLowerBound_eq (I : P256.DomainParameters.PublicKeyInstance) :
    (problem I).successLB.value = ENNReal.ofReal ((99 : ℝ) / 100) := by
  change 1 - ENNReal.ofReal ((1 : ℝ) / 100) = ENNReal.ofReal ((99 : ℝ) / 100)
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
  norm_num

/-- Lossless IEC display of the same resident classical allowance. -/
public def residentClassicalMemoryIEC (unit : IECUnit) : Nat × Nat :=
  unit.decomposeBits residentClassicalBitLimit

end

end QuantumAlg.EllipticCurve.P256LogicalResources
