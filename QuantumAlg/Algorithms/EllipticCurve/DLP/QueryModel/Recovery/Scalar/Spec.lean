/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Solves
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First.Schedule
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First.Schedule
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Solves
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First.Protocol
import all QuantumAlg.Core.Execution.Circuit.Weighted
public import QuantumAlg.Core.Base.Accounting.ClassicalWeight
public import QuantumAlg.Core.Base.Accounting.Weighted

/-!
# Parameter-only allowances for complete declared ECDLP execution

The formulas use the original fitted field and Fourier widths. Both complete
physical resets, the infinity-tag X, native peripherals, checked recovery and
sole terminal packing operation are charged. All formulas are scalar arithmetic;
none evaluates a concrete preparation table, operand maximum or event multiset.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

namespace Scalar

/-- The real point tag, two coordinates and two exponent registers. -/
public def qubits (fieldWidth sampleWidth : Nat) : Nat :=
  2 * sampleWidth + 1 + 2 * fieldWidth

/-- The original widened XGCD words, bounded by the generic quadratic theorem. -/
public def coefficientBits (width : Nat) : Nat :=
  (width + 1) * (2 * (width + 1) + 1) + 3

/-- Successive checked-recovery and complete curve-verification scratch scopes. -/
public def scratchBits (fieldWidth sampleWidth : Nat) : Nat :=
  max (25 * sampleWidth + 9 * coefficientBits sampleWidth + 16)
    (27 * fieldWidth + 9 * coefficientBits fieldWidth + 15)

/-- All borrowed inputs, measured exponents, reset bit and persistent destinations. -/
public def residentBits (fieldWidth sampleWidth : Nat) : Nat :=
  scratchBits fieldWidth sampleWidth + 6 * fieldWidth + 4 * sampleWidth + 8

/-- The original auxiliary roles retain every owned and intermediate cell. -/
public def auxiliaryBits (fieldWidth sampleWidth : Nat) : Nat :=
  scratchBits fieldWidth sampleWidth + 2 * fieldWidth + 4 * sampleWidth + 6

/-- The unchanged six-stage checked recovery and original first-success feedback. -/
public def recoveryEvents (fieldWidth sampleWidth : Nat) : Nat :=
  42 * sampleWidth + sampleWidth * (248 * fieldWidth + 644) + 119

/-- Two full resets, one actual tag X, two preparations and two native inverse transforms. -/
public def roundSingleQubit (fieldWidth sampleWidth : Nat) : Nat :=
  2 * qubits fieldWidth sampleWidth + 1 + 22 * sampleWidth +
    2 * (sampleWidth + 3 * Nat.choose sampleWidth 2)

/-- Both width-bounded preparations and the actual native inverse-transform decompositions. -/
public def roundCnot (sampleWidth : Nat) : Nat :=
  6 * sampleWidth + 2 * (2 * Nat.choose sampleWidth 2 + 3 * (sampleWidth / 2))

/-- The two complete physical resets and every measured exponent position. -/
public def roundMeasurements (fieldWidth sampleWidth : Nat) : Nat :=
  2 * qubits fieldWidth sampleWidth + 2 * sampleWidth

/-- The scalar sum of every actual quantum, query, measurement and checking coordinate. -/
public def roundEvents (fieldWidth sampleWidth : Nat) : Nat :=
  roundSingleQubit fieldWidth sampleWidth + roundCnot sampleWidth + 1 +
    roundMeasurements fieldWidth sampleWidth + recoveryEvents fieldWidth sampleWidth

/-- All real prescribed rounds, initial per-system preparation and one final paid pack. -/
public def wholeRunEvents (fieldWidth sampleWidth count : Nat) : Nat :=
  qubits fieldWidth sampleWidth + count * roundEvents fieldWidth sampleWidth + 1

end Scalar

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
