/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Solves

public import QuantumAlg.Algorithms.EllipticCurve.P256.DomainParameters
public import QuantumAlg.Algorithms.EllipticCurve.Resources
import all QuantumAlg.Algorithms.EllipticCurve.Resources

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Algorithm
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Input
public import QuantumAlg.Algorithms.EllipticCurve.P256.ActualRun
import all QuantumAlg.Algorithms.EllipticCurve.P256.ActualRun
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Repetition
import all QuantumAlg.Algorithms.EllipticCurve.P256.Cascade.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Seed

/-!
# Independent fixed P-256 problem and one actual streaming solver

The original certified instance supplies the two public points, their original
subgroup equation and the complete fixed-offset exceptional-error calibration.
The independent problem specializes the generic parameter budget to exactly
4714 attempts and one-percent failure. Its physical input is the public frame;
the bank is allocated and initialized by the same actual streaming run.

The conclusion is solely existence of an Algorithm satisfying every Solves
field for that problem. Numeric coordinate results belong to separate resource
modules. Both storage roles and full borrowed/reference restoration belong to that
same complete execution.
-/

namespace QuantumAlg.EllipticCurve.P256LogicalResources

noncomputable section

open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.ExecutionContract

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass

/-- Certified P-256 ECDLP with one-percent total failure allowance.

**Input.**
- The certified P-256 curve, affine base point of known prime order and affine
  public target in that subgroup. The two borrowed classical point encodings
  are fixed and every external reference extension is admitted. The secret
  scalar is not executable input data; the quantum bank is allocated internally.
**Output.**
- An optional scalar in the original subgroup range satisfying the public
  group equation.
**Resource budget.**
- The independent generic native-event, resident, auxiliary and quantum-time
  formulas at field width 256, Fourier width 260 and 4714 attempts.
- The attempts reuse the same 818 quantum wires, measured classical destinations
  and seven persistent first-success cells. The initial preparation, every
  measured reset and Fourier sample, complete checked recovery and final paid
  optional-result pack all remain in the native-event budget.
- Quantum time charges the independent reset/sampling gate and query allowance;
  preparation, measurement and classical checking carry zero quantum duration.
  Complete unit-duration event depth is a separate resource theorem.
**Success.**
- At least 99 percent, including the original fixed-offset exceptional error.
- All borrowed data and their external-reference correlations are restored jointly.
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

/-- The original instance discharges every mathematical boundary of the generic solver. -/
private lemma candidate_solves (I : P256.DomainParameters.PublicKeyInstance) :
    (P256.ActualRun.algorithm I).Solves (problem I) := by
  have : Fact P256.DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  exact LogicalResources.complete_correct (P256.DomainParameters.curve I.curveCert) 255
    P256.Measured.fieldTail_sameWidth P256.Measured.fieldTail_fits
    (P256.Measured.fieldModulus_odd I.curveCert) (P256.Cascade.ecdlpInstance I)
    (P256.Cascade.addend I) (P256.Measured.fixedSeed I)
    (P256.Measured.addend_original_encoding I) 4714 ((1 : ℝ) / 100)
    (P256.Measured.fixedSeed_repetitionCondition I)

/-- One complete actual P-256 execution solves the independent original-input problem. -/
public theorem main (I : P256.DomainParameters.PublicKeyInstance) :
    ∃ candidate : Algorithm (.quantum AlgorithmGate.model .empty BitWord.model)
        (P256.ActualRun.Pre I) (P256.ActualRun.Post I)
        (P256.ActualRun.OutputShape I), candidate.Solves (problem I) := by
  have : Fact P256.DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  exact LogicalResources.main (P256.DomainParameters.curve I.curveCert) 255
    P256.Measured.fieldTail_sameWidth P256.Measured.fieldTail_fits
    (P256.Measured.fieldModulus_odd I.curveCert) (P256.Cascade.ecdlpInstance I)
    (P256.Cascade.addend I) (P256.Measured.fixedSeed I)
    (P256.Measured.addend_original_encoding I) 4714 ((1 : ℝ) / 100)
    (P256.Measured.fixedSeed_repetitionCondition I)

end

end QuantumAlg.EllipticCurve.P256LogicalResources
