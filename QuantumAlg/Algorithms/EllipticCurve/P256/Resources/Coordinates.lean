/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.P256.ActualRun
public import QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Limits
import all QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Limits
public import QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Spec

import all QuantumAlg.Algorithms.EllipticCurve.P256.ActualRun
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Resources.Coordinates
import all QuantumAlg.Algorithms.EllipticCurve.P256.Cascade.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Seed

/-!
# Both actual P-256 storage roles in every quantum dimension

The same complete 4714-attempt Run3 uses at most 818 qubits in both storage
roles, with no other quantum dimension. The same 818 bound is used by the complete
seven-coordinate theorem.
The quantum-time comparison has its separate owner; these resource results
remain separate from the public existential Solves conclusion.


-/

namespace QuantumAlg.EllipticCurve.P256.StreamingResources.Coordinates

noncomputable section

open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.ExecutionContract

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.GenericPointAddition.InPlace

/-- Every quantum dimension retains both storage roles of the same complete actual Path. -/
lemma run_quantumSystems_le (I : P256.DomainParameters.PublicKeyInstance)
    (path : (P256.ActualRun.algorithm I).run.code.Path) (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension)
        ((P256.ActualRun.algorithm I).run.code.peakResidentSpace path) ≤
        (if 2 = dimension then 818 else 0) ∧
      SpacePool.count (.quantumSystems dimension)
        ((P256.ActualRun.algorithm I).run.code.peakAuxiliarySpace path) ≤
        (if 2 = dimension then 818 else 0) := by
  have : Fact P256.DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  have both := Coordinates.run_quantumSystems_both_le
    (P256.DomainParameters.curve I.curveCert) 255
    (ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I))
    (P256.Cascade.addend I) (P256.Measured.fixedSeed I) P256.DomainParameters.subgroupOrder
    (Semantics.radixUnit P256.DomainParameters.fieldModulus (Nat.succ 255)
      (P256.Measured.fieldModulus_odd I.curveCert)) I.subgroupCert.prime.two_le 4714 path dimension
  have arithmetic : 3 * (256 : Nat) + 4 * (256 : Nat).size + 14 = 818 :=
    P256LogicalResources.Limits.qubits_eq
  rw [P256.Measured.fieldModulus_size, arithmetic] at both
  exact both

end

end QuantumAlg.EllipticCurve.P256.StreamingResources.Coordinates

/-!
# Preserved independent classical allowances and lossless IEC display

These original pure formulas retain the execution coefficient widths and both
classical storage roles. The separate actual quantum bound above remains 818.
-/

namespace QuantumAlg.EllipticCurve.P256LogicalResources

noncomputable section

attribute [local irreducible] ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth

private def classicalBitLimit (coefficient : Nat → Nat) (extra : Nat) : Nat :=
  max (6516 + 9 * coefficient 261) (6927 + 9 * coefficient 257) + extra

private lemma classicalBitLimit_eq (coefficient : Nat → Nat) (extra : Nat) :
    max (6516 + 9 * coefficient 261) (6927 + 9 * coefficient 257) + extra =
      classicalBitLimit coefficient extra := rfl

/-- Resident classical bits retain the original 261-bit and 257-bit XGCD input widths. -/
public def residentClassicalBitLimit : Nat :=
  classicalBitLimit ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth 2839

/-- Auxiliary classical bits exclude precisely the two original borrowed public point encodings. -/
public def auxiliaryClassicalBitLimit : Nat :=
  classicalBitLimit ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth 1813

/-- Lossless IEC display of the same resident classical allowance. -/
public def residentClassicalMemoryIEC (unit : IECUnit) : Nat × Nat :=
  unit.decomposeBits residentClassicalBitLimit

end

end QuantumAlg.EllipticCurve.P256LogicalResources
