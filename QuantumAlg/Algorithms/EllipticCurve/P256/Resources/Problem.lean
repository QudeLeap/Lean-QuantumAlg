/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.P256.ActualRun
public import QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Algorithms.EllipticCurve.P256.ActualRun
import all QuantumAlg.Algorithms.EllipticCurve.P256.Cascade.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Seed
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Spec

/-! # Independent P-256 problem for the complete actual measured execution -/

namespace QuantumAlg.EllipticCurve.P256LogicalResources

noncomputable section

/-- The original certified P-256 problem with one-percent total failure allowance.

**Input.**
- The original certified P-256 curve, affine base point of known prime order,
  and affine public target in that subgroup. The borrowed classical point
  encodings are fixed; every normalized quantum input and external reference
  extension is admitted. The secret scalar is not executable input data.
**Output.**
- An optional scalar in the original subgroup range satisfying the original
  public group equation.
**Resource budget.**
- The independent generic native-event, resident, auxiliary and unit-duration
  depth formulas, with field width 256, exponent width 260 and 4714 rounds.
- The rounds reuse the same quantum wires, measured terminal cells and seven
  persistent first-success cells. Preparation, actual quantum reset, sampling,
  checked recovery and the final optional-result pack are all charged.
**Success.**
- At least 99 percent, including the original fixed-offset exceptional error.
- Borrowed data and all reference correlations must be restored jointly.
**Source.**
- [PZ03, ecc.tex:448-556], specialized by the original P-256 domain parameters.
- The original finite-cyclic DLP Fourier and recovery analysis calibrates the
  fixed 4714 repetitions.
-/
public def problem (I : P256.DomainParameters.PublicKeyInstance) :
    Problem (.quantum AlgorithmGate.model .empty BitWord.model)
      (P256.ActualRun.Pre I) (P256.ActualRun.Post I)
      (P256.ActualRun.OutputShape I) := by
  letI : Fact P256.DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  exact LogicalResources.problem (P256.DomainParameters.curve I.curveCert)
    (P256.Cascade.ecdlpInstance I) 4714 ((1 : ℝ) / 100)

end

end QuantumAlg.EllipticCurve.P256LogicalResources
