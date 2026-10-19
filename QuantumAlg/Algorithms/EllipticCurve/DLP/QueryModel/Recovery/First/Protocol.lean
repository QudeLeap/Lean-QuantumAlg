/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Specification

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Failure
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Failure
import all QuantumAlg.Core.Execution.State.Requirement

/-!
# Independent original-input protocol of the first complete ECDLP cycle

The original public-point caller domain supplies no secret, prepared state,
candidate, success certificate or fresh service assumption. All original
reference extensions are admitted. The observed result and fixed physical
zero promise are the same completed computation as for later rounds; its
separate event allowance additionally pays the one-time bank preparation.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The prescribed full owned zero state on every observed first-round result. -/
public def firstRoundStateRequirement (I : ECDLPInstance E) :
    StateRequirement (Sampling.pre I) (context I) :=
  .marginal (context I).borrowedSelectionᶜ (roundResultRead I)
    (fun _ _ => .pure (NormalizedVector.ket (roundZeroSeed I)))

/-- The caller requests one original-input complete ECDLP computation.

**Input.** Original affine public points, with arbitrary references
and joint service correlations. No secret or prepared quantum bank is supplied.
**Output.** Actual bounded accepted scalar relation, all live entries, restored
borrowed observations and the same zero owned bank on every result fiber.
**Resource budget.** One-time preparation, both bank resets, one original
declared group query and all native sampling/checking/feedback operations;
both complete dimension-indexed peaks and weighted serial depth.
**Success.** The original selected-family floor for the prescribed input.
**Source.** [PZ03, ecc.tex:448-462,525-640]; [Sho95, source.tex:1704-1740];
[SV24, Uniform.tex:622-664,775-805,996-1024]; [RNSL17, ECDLP.tex:483-510,649-709].
-/
public def firstRoundProblem (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) :
    Problem (Sampling.executionModel I) (Sampling.pre I) (context I)
      (.product .bit (.unsignedWord (scalarWidth I))) where
  Witness := FiniteCyclicDLP.Canonical.Probability.SecretInput (problem I)
  valid := fun environment _ state => Sampling.Admissible I environment ∧ inputDomain I state
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ result => roundAccepts I result
  successLB := fun _ _ => ⟨ENNReal.ofReal (Sampling.Reuse.successFloor I),
    ENNReal.ofReal_le_one.mpr (successFloor_le_one I)⟩
  states := fun _ _ => [firstRoundStateRequirement I]
  resources :=
    { events := firstRoundEventBudget I expansion nontrivial
      resident := roundResidentBudget I
      auxiliary := roundAuxiliaryBudget I }
  quantumTimeLimit := ResourcePool.weightedCount Resource.Event.quantumDuration
    (firstRoundEventBudget I expansion nontrivial)

/-- The actual initialized first round observes only its existing two result cells. -/
public def firstRoundAlgorithm (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) :
    Algorithm (Sampling.executionModel I) (Sampling.pre I) (context I)
      (.product .bit (.unsignedWord (scalarWidth I))) :=
  ⟨{ code := firstRound I expansion nontrivial
     output := Output.all (context I) (roundResultRead I) }⟩

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
