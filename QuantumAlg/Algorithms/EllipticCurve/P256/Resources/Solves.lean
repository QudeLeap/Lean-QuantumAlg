/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Problem
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Algorithms.EllipticCurve.P256.ActualRun
import all QuantumAlg.Algorithms.EllipticCurve.P256.Cascade.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Seed
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Repetition
import all QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Problem
import all QuantumAlg.Algorithms.EllipticCurve.Resources

/-! # The original P-256 algorithm solves its independent complete-run problem -/

namespace QuantumAlg.EllipticCurve.P256LogicalResources

noncomputable section

/-- The fixed algorithm contains precisely the one original actual measured P-256 run. -/
public def algorithm (I : P256.DomainParameters.PublicKeyInstance) :
    Algorithm .quantum (P256.ActualRun.Pre I) (P256.ActualRun.Post I)
      (P256.ActualRun.OutputShape I) where
  run := P256.ActualRun.run I

/-- All correctness, restoration and resource obligations come from the same generic run. -/
theorem algorithm_solves (I : P256.DomainParameters.PublicKeyInstance) :
    (algorithm I).Solves (problem I) := by
  let : Fact P256.DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  exact LogicalResources.main (P256.DomainParameters.curve I.curveCert) 255
    P256.Measured.fieldTail_sameWidth P256.Measured.fieldTail_fits
    (P256.Measured.fieldModulus_odd I.curveCert) (P256.Cascade.ecdlpInstance I)
    (P256.Cascade.addend I) (P256.Measured.fixedSeed I)
    (P256.Measured.addend_original_encoding I) 4714 ((1 : ℝ) / 100)
    (P256.Measured.repetitionCondition I)

end

end QuantumAlg.EllipticCurve.P256LogicalResources
