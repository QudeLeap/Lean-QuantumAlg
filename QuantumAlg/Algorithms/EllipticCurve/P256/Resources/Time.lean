/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.ActualRun
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Resources.Bounds
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Resources.Events
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Limits

/-!
# Canonical P-256 quantum-time ceiling on the actual streaming run

The numeric substitution concerns the actual 4714-attempt execution, including
every reset and all four coordinate conversions. The independent numerical
time allowance specializes the same formula used by the public problem. Quantum
space and complete unit-event depth have separate resource owners.


-/

namespace QuantumAlg.EllipticCurve.P256.StreamingResources.Time

noncomputable section

open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.ExecutionContract

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.GenericPointAddition.InPlace
open FiniteCyclicDLP

/-- Every path meets the canonical reset/sampling bound used by the public problem. -/
lemma run_quantumTime_le (I : P256.DomainParameters.PublicKeyInstance)
    (path : (P256.ActualRun.algorithm I).run.code.Path) :
    (P256.ActualRun.algorithm I).run.code.quantumTime path ≤
      P256LogicalResources.Limits.quantumTime := by
  have : Fact P256.DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  refine (Bounds.run_quantumTime_le (P256.DomainParameters.curve I.curveCert) 255
    (ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I))
    (P256.Cascade.addend I) (P256.Measured.fixedSeed I) P256.DomainParameters.subgroupOrder
    (Semantics.radixUnit P256.DomainParameters.fieldModulus (Nat.succ 255)
      (P256.Measured.fieldModulus_odd I.curveCert))
    I.subgroupCert.prime.two_le 4714 path).trans_eq ?_
  rw [Events.terminal_systemCount, P256.Measured.fieldModulus_size,
    P256.Measured.orderWidth_eq_260, LogicalResources.Scalar.multiplierTime_eq,
    LogicalResources.Scalar.pointDepth_eq]
  exact P256LogicalResources.Limits.quantumTime_eq


end

end QuantumAlg.EllipticCurve.P256.StreamingResources.Time
