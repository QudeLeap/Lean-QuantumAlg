/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Coordinates
import all QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Coordinates
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Memory
import all QuantumAlg.Util.Classical.NumberTheory.Extended.Bounds
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# Numeric classical memory ceilings for the complete P-256 problem

The exact independent allowances retain the original execution coefficient
widths. Their proved quadratic ceilings bound resident and auxiliary classical
storage by 1,237,909 and 1,236,883 bits, respectively, for every original public
instance. These conservative ceilings do not replace either execution width
or assert a reached peak. The existing IEC quotient and residual bits retain
an exact lossless display of the resident allowance.
-/

namespace QuantumAlg.EllipticCurve.P256LogicalResources

open ClassicalAlgorithms.NumberTheory.XGCD

attribute [local irreducible] executionCoefficientWidth

private theorem classicalBitLimit_le (coefficient : Nat → Nat)
    (sample : coefficient 261 ≤ 136506) (field : coefficient 257 ≤ 132358) (extra : Nat) :
    classicalBitLimit coefficient extra ≤ 1235070 + extra :=
  (classicalBitLimit_eq coefficient extra).symm.le.trans
    (P256.Measured.coefficient_bits_le coefficient sample field extra)

/-- The exact resident classical allowance has a conservative instance-independent ceiling. -/
public theorem residentClassicalBitLimit_le : residentClassicalBitLimit ≤ 1237909 :=
  classicalBitLimit_le executionCoefficientWidth
    executionCoefficientWidth_261_le executionCoefficientWidth_257_le 2839

/-- The auxiliary ceiling excludes precisely the two borrowed public point encodings. -/
public theorem auxiliaryClassicalBitLimit_le : auxiliaryClassicalBitLimit ≤ 1236883 :=
  classicalBitLimit_le executionCoefficientWidth
    executionCoefficientWidth_261_le executionCoefficientWidth_257_le 1813

/-- The same complete public problem respects the resident classical bit ceiling. -/
public theorem resident_classicalBits_le (I : P256.DomainParameters.PublicKeyInstance) :
    SpacePool.count .classicalBits (problem I).resources.resident ≤ 1237909 :=
  (resident_classicalBits I).le.trans residentClassicalBitLimit_le

/-- The same complete public problem respects the auxiliary classical bit ceiling. -/
public theorem auxiliary_classicalBits_le (I : P256.DomainParameters.PublicKeyInstance) :
    SpacePool.count .classicalBits (problem I).resources.auxiliary ≤ 1236883 :=
  (auxiliary_classicalBits I).le.trans auxiliaryClassicalBitLimit_le

/-- The existing IEC display reconstructs every resident bit without rounding. -/
theorem residentClassicalMemoryIEC_reconstruct (unit : IECUnit) :
    (residentClassicalMemoryIEC unit).1 * unit.bitsPerUnit +
      (residentClassicalMemoryIEC unit).2 = residentClassicalBitLimit :=
  IECUnit.decomposeBits_reconstruct unit residentClassicalBitLimit

/-- The retained residual bits are strictly below one unit in the existing IEC display. -/
theorem residentClassicalMemoryIEC_remainder_lt (unit : IECUnit) :
    (residentClassicalMemoryIEC unit).2 < unit.bitsPerUnit :=
  IECUnit.decomposeBits_remainder_lt unit residentClassicalBitLimit

end QuantumAlg.EllipticCurve.P256LogicalResources
