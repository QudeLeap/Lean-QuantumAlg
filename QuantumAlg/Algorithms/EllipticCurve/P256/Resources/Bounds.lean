/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Solves
import all QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Solves
import all QuantumAlg.Algorithms.EllipticCurve.P256.ActualRun
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Bounds
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Seed
import all QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Problem
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Spec

/-!
# Numeric native-event and depth ceilings of the same public P-256 algorithm

The independent problem budgets and the actual algorithm paths remain
separate observations of the same complete 4714-round implementation.
The event pool includes alternative reset corrections, whereas each path
pays only its selected corrections. The depth coordinate below projects
the existing problem field; it does not introduce another budget or run.
-/

namespace QuantumAlg.EllipticCurve.P256LogicalResources

noncomputable section

open Execution PrimeFieldShortWeierstrass ECDLP.Measured

/-- The limit already stored with the original problem's native-event durations. -/
public def unitDepthLimit (I : P256.DomainParameters.PublicKeyInstance) : Nat :=
  match (problem I).depth with
  | .quantum _ limit => limit

private theorem event_pool (I : P256.DomainParameters.PublicKeyInstance) :
  let _ : Fact P256.DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩;
    (problem I).resources.events =
      repeatedRunBudget (P256.DomainParameters.curve I.curveCert) 255
        P256.Measured.fieldTail_sameWidth P256.Measured.fieldTail_fits
        (ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I))
        (P256.Measured.fixedSeed I) I.subgroupCert.prime.two_le 4714 := by
  dsimp only
  let _ : Fact P256.DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  rfl

private theorem depth_limit (I : P256.DomainParameters.PublicKeyInstance) :
    unitDepthLimit I = LogicalResources.depthLimit (P256.DomainParameters.curve I.curveCert)
      (P256.Cascade.ecdlpInstance I) 4714 := rfl

private theorem depth_budget (I : P256.DomainParameters.PublicKeyInstance) :
    (problem I).depth = .quantum (fun _ => 1) (unitDepthLimit I) := rfl

/-- The original problem charges one unit for every native event and uses its stored limit. -/
public theorem depthBudget_eq (I : P256.DomainParameters.PublicKeyInstance) :
    (problem I).depth = .quantum (fun _ => 1) (unitDepthLimit I) :=
  depth_budget I

/-- Cardinality of the complete independent native event pool of the public problem. -/
public theorem eventBudget_card_le (I : P256.DomainParameters.PublicKeyInstance) :
    (problem I).resources.events.card ≤ 1593604205541192770952445805 := by
  let _ : Fact P256.DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  exact (congrArg Multiset.card (event_pool I)).le.trans
    (P256.Measured.p256_repeatedRunBudget_card_le I (P256.Measured.fixedSeed I))

/-- The existing problem's unit-duration depth allowance has this complete numeric ceiling. -/
public theorem unitDepthLimit_le (I : P256.DomainParameters.PublicKeyInstance) :
    unitDepthLimit I ≤ 1593604204331439804319771867 :=
  (depth_limit I).le.trans (P256.Measured.p256_depthLimit_le I)

attribute [local irreducible] exponentRepeatedRun

private theorem actual_events (I : P256.DomainParameters.PublicKeyInstance)
    (path : (algorithm I).run.code.Path) :
    ((algorithm I).run.code.eventTrace path).length ≤ 1593604205541192770946147901 := by
  let _ : Fact P256.DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  exact P256.Measured.p256_exponentRepeatedRun_eventCount_le I (P256.Measured.fixedSeed I) path

private theorem actual_depth (I : P256.DomainParameters.PublicKeyInstance)
    (path : (algorithm I).run.code.Path) :
    (algorithm I).run.code.depth (fun _ => 1) path ≤ 1593604204331439804319771867 := by
  let _ : Fact P256.DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  exact P256.Measured.p256_exponentRepeatedRun_unitDepth_le I (P256.Measured.fixedSeed I) path

/-- Every actual path of the same public algorithm obeys the selected-correction event bound. -/
public theorem algorithm_eventCount_le (I : P256.DomainParameters.PublicKeyInstance)
    (path : (algorithm I).run.code.Path) :
    ((algorithm I).run.code.eventTrace path).length ≤ 1593604205541192770946147901 :=
  actual_events I path

/-- Every same actual path retains the original parallel stages and all serial recovery work. -/
public theorem algorithm_unitDepth_le (I : P256.DomainParameters.PublicKeyInstance)
    (path : (algorithm I).run.code.Path) :
    (algorithm I).run.code.depth (fun _ => 1) path ≤ 1593604204331439804319771867 :=
  actual_depth I path

end

end QuantumAlg.EllipticCurve.P256LogicalResources
