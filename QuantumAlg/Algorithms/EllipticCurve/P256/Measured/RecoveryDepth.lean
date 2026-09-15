/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Events
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Depth

/-!
# Original P-256 checked-recovery unit duration

The same attempt depth allowance is bounded through its original native pool,
then specialized to the certified field and exponent widths. All 4714 actual
rounds retain the quantum sampling depth and the resulting classical ceiling.
No path count is substituted for an unrelated duration budget.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured

noncomputable section

open Execution PrimeFieldShortWeierstrass FiniteCyclicDLP ConcreteCircuitAccess
open ECDLP.Measured ClassicalRoutines.EllipticCurve.CandidateCheck.Native

/-- The original independent P-256 attempt duration has the complete native ceiling. -/
theorem attemptDepthLimit_unit_le_fixed (I : DomainParameters.PublicKeyInstance) :
    attemptDepthLimit (kind := .quantum)
      (ECDLP.Canonical.Layout.curveSpec (DomainParameters.curve I.curveCert))
      (recoveryModulusSpec (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
        I.subgroupCert.prime.two_le) (fun _ => 1) ≤ 16685359 :=
  (attemptDepthLimit_unit_le_card _ _).trans (attemptEnvelope_card_le_fixed I)

private theorem combine_recovery (product point checked : Nat) (within : checked ≤ 16685359) :
    3 + 4714 * (38589 + 4 * product + 520 * point + checked) ≤
      3 + 4714 * (16723948 + 4 * product + 520 * point) := by omega

attribute [local irreducible] exponentRepeatedRun

/-- The same complete actual path retains sampling depth and the proved classical ceiling. -/
theorem exponentRepeatedRun_unitDepth_recovery_le (I : DomainParameters.PublicKeyInstance)
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
      3 + 4714 * (16723948 + 4 * MAU.Multiplication.Gidney.eventBound 256 +
        520 * MeasuredPointAddition.depthBound 256) := by
  dsimp only
  let _ : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  intro path
  exact (exponentRepeatedRun_unitDepth_fixed_le I seed path).trans
    (combine_recovery _ _ _ (attemptDepthLimit_unit_le_fixed I))

end

end QuantumAlg.EllipticCurve.P256.Measured
