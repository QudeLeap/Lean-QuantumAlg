/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Arithmetic
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.RecoveryDepth
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Spec

/-!
# Complete original P-256 native event and depth ceilings

Every number is a normalization of the original independent scalar
allowances. The same 4714-round execution includes preparation, real reset,
measurement, correction, checked recovery and final result packing. The
native pool includes alternative reset corrections; the path event bound
counts only the correction selected on that path. Neither is a tight peak
or a gate estimate for a different EEA construction.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured

noncomputable section

open Execution PrimeFieldShortWeierstrass ECDLP.Measured

variable (I : DomainParameters.PublicKeyInstance)

/-- The complete original independent native pool has this explicit cardinality ceiling. -/
theorem p256_repeatedRunBudget_card_le
    (seed : AffinePoint (DomainParameters.curve I.curveCert)) :
  let _ : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩;
    (repeatedRunBudget (DomainParameters.curve I.curveCert) 255
      fieldTail_sameWidth fieldTail_fits (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
      seed I.subgroupCert.prime.two_le 4714).card ≤ 1593604205541192770952445805 := by
  dsimp only
  let _ : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  refine (repeatedRunBudget_card_le I seed).trans_eq ?_
  rw [p256_multiplierBudget_card, p256_pointBudget_card]

/-- The independent unit-duration allowance includes the original checked classical recovery. -/
theorem p256_depthLimit_le :
    LogicalResources.depthLimit (DomainParameters.curve I.curveCert)
      (Cascade.ecdlpInstance I) 4714 ≤ 1593604204331439804319771867 := by
  rw [LogicalResources.depthLimit, p256_samplingRoundUnitDepth_eq]
  have checked := attemptDepthLimit_unit_le_fixed I
  omega

attribute [local irreducible] exponentRepeatedRun

/-- Every complete actual path pays only its selected reset corrections within the native bound. -/
theorem p256_exponentRepeatedRun_eventCount_le
    (seed : AffinePoint (DomainParameters.curve I.curveCert)) :
  let _ : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩;
    ∀ (path : (exponentRepeatedRun (DomainParameters.curve I.curveCert) 255
      fieldTail_sameWidth fieldTail_fits (fieldModulus_odd I.curveCert)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) (Cascade.addend I) seed
      I.subgroupCert.prime.two_le 4714).code.Path),
    ((exponentRepeatedRun (DomainParameters.curve I.curveCert) 255
      fieldTail_sameWidth fieldTail_fits (fieldModulus_odd I.curveCert)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) (Cascade.addend I) seed
      I.subgroupCert.prime.two_le 4714).code.eventTrace path).length ≤
        1593604205541192770946147901 := by
  dsimp only
  let _ : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  intro path
  refine (exponentRepeatedRun_eventCount_fixed_le I seed path).trans_eq ?_
  rw [p256_multiplierBudget_card, p256_pointBudget_card]

/-- Every same complete path has the original parallel quantum stages and serial recovery. -/
theorem p256_exponentRepeatedRun_unitDepth_le
    (seed : AffinePoint (DomainParameters.curve I.curveCert)) :
  let _ : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩;
    ∀ (path : (exponentRepeatedRun (DomainParameters.curve I.curveCert) 255
      fieldTail_sameWidth fieldTail_fits (fieldModulus_odd I.curveCert)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) (Cascade.addend I) seed
      I.subgroupCert.prime.two_le 4714).code.Path),
    (exponentRepeatedRun (DomainParameters.curve I.curveCert) 255
      fieldTail_sameWidth fieldTail_fits (fieldModulus_odd I.curveCert)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) (Cascade.addend I) seed
      I.subgroupCert.prime.two_le 4714).code.depth (fun _ => 1) path ≤
        1593604204331439804319771867 := by
  dsimp only
  let _ : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  intro path
  refine (exponentRepeatedRun_unitDepth_recovery_le I seed path).trans_eq ?_
  rw [p256_multiplierDepthBound_eq, p256_pointDepthBound_eq]

end

end QuantumAlg.EllipticCurve.P256.Measured
