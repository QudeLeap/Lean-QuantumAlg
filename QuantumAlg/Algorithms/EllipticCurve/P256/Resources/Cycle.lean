/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Solves
public import QuantumAlg.Algorithms.EllipticCurve.Resources.Cycle.Complete
import all QuantumAlg.Algorithms.EllipticCurve.P256.ActualRun
import all QuantumAlg.Algorithms.EllipticCurve.P256.Cascade.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Seed
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Cycle.Complete

/-!
# Independent complete-cycle problem for the original P-256 execution

The fixed plan specializes the generic initialized, reused and terminal
protocol at the original 4714 attempts. Initialization, paid resets,
checked recovery, borrowed restoration and final packing remain physical
parts of that same execution [PZ03, ecc.tex:448-556].
-/

namespace QuantumAlg.EllipticCurve.P256LogicalResources

noncomputable section

/-- The original fixed execution follows the generic physically complete cycle problem. -/
public def completeCycleProblem (I : P256.DomainParameters.PublicKeyInstance) :
    CycleProblem (.quantum AlgorithmGate.model .empty BitWord.model)
      (P256.ActualRun.Pre I) (P256.ActualRun.Post I) (P256.ActualRun.OutputShape I) := by
  letI : Fact P256.DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  exact LogicalResources.completeCycleProblem (P256.DomainParameters.curve I.curveCert) 255
    P256.Measured.fieldTail_sameWidth P256.Measured.fieldTail_fits
    (P256.Cascade.ecdlpInstance I) (P256.Cascade.addend I) (P256.Measured.fixedSeed I)
    (P256.Measured.addend_original_encoding I) 4714 ((1 : ℝ) / 100)

end

end QuantumAlg.EllipticCurve.P256LogicalResources
