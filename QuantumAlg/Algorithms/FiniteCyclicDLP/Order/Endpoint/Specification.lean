/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Endpoint.Resources
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Endpoint.Success
public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Core.Algorithm.CyclePlan

/-!
# Independent all-positive-order finite-cyclic DLP specification

The executable input is empty.  The secret remains a proof-side witness in
the accepted-output relation.  The classical finite-group service may start
in any hidden state because every actual power check begins with its granted
explicit reset query.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderEndpoint

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- The exact accepted word is the advertised bounded residue logarithm. -/
@[expose] public def accepts {P : KnownOrderProblem G} (secret : FiniteCyclicDLP.Input P)
    (_initial : Execution.Store OrderExecution.pre)
    (output : CShape.Value (.option (.unsignedWord (OrderPreparation.width P)))) : Prop :=
  output = .optionSome
    (CShape.wordOfNat (OrderPreparation.width P) secret.secret.val)

/-- The source endpoint's fixed two-thirds success threshold. -/
@[expose] public def successLowerBound : ProbabilityLowerBound where
  value := ENNReal.ofReal ((2 : Real) / 3)
  le_one := by
    apply ENNReal.ofReal_le_one.mpr
    norm_num

/-- Complete native event and live-space limits, fixed independently of a path. -/
@[expose] public def resourceBudget (P : KnownOrderProblem G) :
    ResourceBudget (OrderExecution.model P) where
  events := eventBudget P
  resident := residentBudget P
  auxiliary := auxiliaryBudget P

/-- The unit-access dependency convention counts every declared classical or
quantum oracle query as one abstract step. -/
@[expose] public def depthBudget (P : KnownOrderProblem G) :
    DepthBudget (OrderExecution.model P) where
  duration := fun _ => 1
  limit := depthLimit P (fun _ => 1)
  classicalQuery_unit := fun _ => rfl
  quantumQuery_unit := fun _ => rfl

/-- Known-order finite-cyclic discrete logarithm over every positive order.

The algorithm owns fresh exponent registers and one native-dimensional group
system per independent sample. It uses only the declared quantum action and
the declared stateful classical group service, whose accumulator is reset
explicitly before each power check. The output is the optional native word of
the advertised secret. The event budget separates gates, measurements,
native word operations, quantum queries and classical queries. Resident and
auxiliary limits retain all physical banks, measurement cells, the output and
the reused recovery workspace. No bit encoding or memory width is assigned to
a group element. The exact answer is required with probability at least 2/3.
-/
@[expose] public def problem (P : KnownOrderProblem G) (secret : FiniteCyclicDLP.Input P) :
    Problem (OrderExecution.model P) OrderExecution.pre (outputContext P)
      (.option (.unsignedWord (OrderPreparation.width P))) where
  valid := fun _ => True
  initialization := fun _ => True
  accepts := accepts secret
  successLB := successLowerBound
  states := []
  resources := resourceBudget P
  depth := depthBudget P

/-- The independent endpoint contract exposes its acceptance relation without
making the complete specification structure reducible to every consumer. -/
public theorem problem_accepts (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P) (initial : Execution.Store OrderExecution.pre)
    (output : CShape.Value (.option (.unsignedWord (OrderPreparation.width P)))) :
    (problem P secret).accepts initial output = accepts secret initial output := rfl

/-- The endpoint contract uses the fixed source success threshold. -/
public theorem problem_success_value (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P) :
    (problem P secret).successLB.value = ENNReal.ofReal ((2 : Real) / 3) := rfl

/-- No separate final-state promise is needed beyond success and borrowed restoration. -/
public theorem problem_states (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P) : (problem P secret).states = [] := rfl

/-- The endpoint event limit is the independently stated complete-run budget. -/
public theorem problem_event_budget (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P) :
    (problem P secret).resources.events = eventBudget P := rfl

/-- The endpoint resident-space limit is the independently stated complete-run budget. -/
public theorem problem_resident_budget (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P) :
    (problem P secret).resources.resident = residentBudget P := rfl

/-- The endpoint auxiliary-space limit is the independently stated complete-run budget. -/
public theorem problem_auxiliary_budget (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P) :
    (problem P secret).resources.auxiliary = auxiliaryBudget P := rfl

/-- The endpoint dependency contract is the unit-duration complete-run limit. -/
public theorem problem_depth (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P) :
    (problem P secret).depth = depthBudget P := rfl

/-- Complete sampling protocol for the finite-cyclic discrete logarithm.

**Input.** The known-order problem fixes the group action and sample count. The
executable input is empty; the secret is a mathematical witness. The reference
and initial hidden group-service state are arbitrary.

**Output.** The retained vector of `sampleCount P` samples, each consisting of
`OrderExecution.sampleWidth P` binary measurement cells.

**Resource budget.** The independent whole-batch event allowance is
`OrderBatch.eventBudget`. Both live-space allowances are the sample cells plus
the physical banks: `(sampleCount P * OrderExecution.sampleWidth P)` binary
cells and `OrderBatch.layout P (sampleCount P)`. Unit depth is bounded by
`completeCycleDepthLimit P`, including preparation and every measurement.

**Success.** With probability at least two thirds, the specified checked
recovery of the retained vector is the advertised logarithm.

**Source.** The quantum sampling and finite-cyclic formulation follow
[Sho95, source.tex:1713] and [Sho95, source.tex:2001]. The explicit two-thirds
threshold is derived from this construction's actual batch Born law and
checked recovery. The native resource formulas certify this implementation. -/
@[expose] public def samplingProblem (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P) :
    Problem (OrderExecution.model P) OrderExecution.pre (sampledContext P)
      (.fixedVector (sampleCount P)
        (.fixedVector (OrderExecution.sampleWidth P) (.finite 2))) where
  valid := fun _ => True
  initialization := fun _ => True
  accepts := fun _ samples => recoveredValue P samples = .optionSome
    (CShape.wordOfNat (OrderPreparation.width P) secret.secret.val)
  successLB := successLowerBound
  states := []
  resources := {
    events := OrderBatch.eventBudget P (sampleCount P) (OrderExecution.canonicalExpansion P)
    resident := (sampleCount P * OrderExecution.sampleWidth P) •
      SpacePool.ofShape (.finite 2) + SpacePool.ofQuantumLayout
        (OrderBatch.layout P (sampleCount P))
    auxiliary := (sampleCount P * OrderExecution.sampleWidth P) •
      SpacePool.ofShape (.finite 2) + SpacePool.ofQuantumLayout
        (OrderBatch.layout P (sampleCount P)) }
  depth := {
    duration := fun _ => 1
    limit := completeCycleDepthLimit P
    classicalQuery_unit := fun _ => rfl
    quantumQuery_unit := fun _ => rfl }

/-- Exact classical recovery protocol for the retained samples.

**Input.** The retained sample vector, with arbitrary incoming reference and
hidden finite-group service state. Every power check explicitly resets that
service before use.

**Output.** One optional word, exactly `recoveredValue P` of the incoming sample
cells. It is zero for order one; otherwise it is the first checked candidate,
or no value when every candidate fails.

**Resource budget.** The independent event allowance is `recoveryEventBudget P`,
with live-space allowances `residentBudget P` and `auxiliaryBudget P`. The unit
depth limit is `recoveryDepthLimit P (fun _ => 1)`. These formulas include result
allocation, verification and first-success selection.

**Success.** The exact input-to-output recovery relation holds with probability
one for every input sample vector.

**Source.** Candidate recovery and group verification follow
[Sho95, source.tex:1907] and [Sho95, source.tex:1984]. The exact deterministic
relation and native resource formulas certify this implementation. -/
@[expose] public def recoveryProblem (P : KnownOrderProblem G) :
    Problem (OrderExecution.model P) (sampledContext P) (outputContext P)
      (.option (.unsignedWord (OrderPreparation.width P))) where
  valid := fun _ => True
  initialization := fun _ => True
  accepts := fun initial output => output = recoveredValue P
    (initial.read (OrderBatch.samplesInput P (sampleCount P)))
  successLB := ⟨1, le_rfl⟩
  states := []
  resources := {
    events := recoveryEventBudget P
    resident := residentBudget P
    auxiliary := auxiliaryBudget P }
  depth := {
    duration := fun _ => 1
    limit := recoveryDepthLimit P (fun _ => 1)
    classicalQuery_unit := fun _ => rfl
    quantumQuery_unit := fun _ => rfl }

/-- The caller requests one complete quantum batch and a classical recovery
continuation. There is no additional cut within the sampling batch. -/
@[expose] public def cyclePlan (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P) :
    CyclePlan (OrderExecution.model P) OrderExecution.pre (outputContext P)
      (.option (.unsignedWord (OrderPreparation.width P))) :=
  .seq (.cycle (samplingProblem P secret)) (.classical (recoveryProblem P))

/-- The final source contract and the caller's independently specified two-section plan. -/
@[expose] public def cycleProblem (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P) :
    CycleProblem (OrderExecution.model P) OrderExecution.pre (outputContext P)
      (.option (.unsignedWord (OrderPreparation.width P))) where
  outcome := problem P secret
  plan := cyclePlan P secret

end

end QuantumAlg.FiniteCyclicDLP.OrderEndpoint
