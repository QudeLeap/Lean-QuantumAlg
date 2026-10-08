/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

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
public def firstRoundProblem (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (duration : Resource.Event (Sampling.executionModel I A) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Problem (Sampling.executionModel I A) (Sampling.pre I) (context I)
      (.product .bit (.unsignedWord (scalarWidth I))) where
  valid := inputDomain I
  initialization := fun _ => True
  accepts := fun _ result => roundAccepts I result
  successLB := ⟨ENNReal.ofReal (Sampling.Reuse.successFloor I),
    ENNReal.ofReal_le_one.mpr (successFloor_le_one I)⟩
  states := [firstRoundStateRequirement I]
  resources :=
    { events := firstRoundEventBudget I A expansion nontrivial
      resident := roundResidentBudget I
      auxiliary := roundAuxiliaryBudget I }
  depth :=
    { duration := duration
      limit := ResourcePool.weightedCount duration (firstRoundEventBudget I A expansion nontrivial)
      classicalQuery_unit := fun coordinate => nomatch coordinate
      quantumQuery_unit := unitQueries }

/-- The actual initialized first round observes only its existing two result cells. -/
public def firstRoundAlgorithm (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) :
    Algorithm (Sampling.executionModel I A) (Sampling.pre I) (context I)
      (.product .bit (.unsignedWord (scalarWidth I))) :=
  ⟨{ code := firstRound I A expansion nontrivial
     output := Output.all (context I) (roundResultRead I) }⟩

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
