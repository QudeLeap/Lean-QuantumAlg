/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Endpoint.Resources
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Endpoint.Success
public import QuantumAlg.Core.Algorithm.Problem

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

/-- The independent whole-run unit-event ceiling also bounds quantum computation time. -/
@[expose] public def quantumTimeLimit (P : KnownOrderProblem G) : Nat :=
  depthLimit P (fun _ => 1)

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
@[expose] public def problem (P : KnownOrderProblem G) :
    Problem (OrderExecution.model P) OrderExecution.pre (outputContext P)
      (.option (.unsignedWord (OrderPreparation.width P))) where
  Witness := FiniteCyclicDLP.Input P
  valid := fun environment _ _ => environment = OrderExecution.sourceEnvironment P
  initialization := fun _ _ _ => True
  accepts := fun _ secret => accepts secret
  successLB := fun _ _ => successLowerBound
  states := fun _ _ => []
  resources := resourceBudget P
  quantumTimeLimit := quantumTimeLimit P

/-- Every source witness and normalized input is admitted by the matching source environment. -/
public lemma orderEndpoint_problem_source_valid (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P)
    (state : ExecutionState (Execution.Store OrderExecution.pre) OrderExecution.pre.register) :
    (problem P).valid (OrderExecution.sourceEnvironment P) secret state := rfl

/-- The endpoint acceptance relation uses the specification witness only. -/
public lemma problem_accepts (P : KnownOrderProblem G)
    (environment : (OrderExecution.model P).Environment)
    (secret : FiniteCyclicDLP.Input P) (initial : Execution.Store OrderExecution.pre)
    (output : CShape.Value (.option (.unsignedWord (OrderPreparation.width P)))) :
    (problem P).accepts environment secret initial output = accepts secret initial output := rfl

/-- The endpoint uses the fixed source success threshold for every environment and witness. -/
public lemma problem_success_value (P : KnownOrderProblem G)
    (environment : (OrderExecution.model P).Environment) (secret : FiniteCyclicDLP.Input P) :
    ((problem P).successLB environment secret).value = ENNReal.ofReal ((2 : Real) / 3) := rfl

/-- No separate final-state promise is needed beyond success and borrowed restoration. -/
public lemma problem_states (P : KnownOrderProblem G)
    (environment : (OrderExecution.model P).Environment) (secret : FiniteCyclicDLP.Input P) :
    (problem P).states environment secret = [] := rfl

/-- The endpoint event limit is the independently stated complete-run budget. -/
public lemma problem_event_budget (P : KnownOrderProblem G) :
    (problem P).resources.events = eventBudget P := rfl

/-- The endpoint resident-space limit is the independently stated complete-run budget. -/
public lemma problem_resident_budget (P : KnownOrderProblem G) :
    (problem P).resources.resident = residentBudget P := rfl

/-- The endpoint auxiliary-space limit is the independently stated complete-run budget. -/
public lemma problem_auxiliary_budget (P : KnownOrderProblem G) :
    (problem P).resources.auxiliary = auxiliaryBudget P := rfl

/-- The endpoint dependency contract is the unit-duration complete-run limit. -/
public lemma orderEndpoint_problem_quantumTimeLimit (P : KnownOrderProblem G) :
    (problem P).quantumTimeLimit = quantumTimeLimit P := rfl

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
`samplingTimeLimit P`, including preparation and every measurement.

**Success.** With probability at least two thirds, the specified checked
recovery of the retained vector is the advertised logarithm.

**Source.** The quantum sampling and finite-cyclic formulation follow
[Sho95, source.tex:1713] and [Sho95, source.tex:2001]. The explicit two-thirds
threshold is derived from this construction's actual batch Born law and
checked recovery. The native resource formulas certify this implementation. -/
@[expose] public def samplingProblem (P : KnownOrderProblem G) :
    Problem (OrderExecution.model P) OrderExecution.pre (sampledContext P)
      (.fixedVector (sampleCount P)
        (.fixedVector (OrderExecution.sampleWidth P) (.finite 2))) where
  Witness := FiniteCyclicDLP.Input P
  valid := fun environment _ _ => environment = OrderExecution.sourceEnvironment P
  initialization := fun _ _ _ => True
  accepts := fun _ secret _ samples => recoveredValue P samples = .optionSome
    (CShape.wordOfNat (OrderPreparation.width P) secret.secret.val)
  successLB := fun _ _ => successLowerBound
  states := fun _ _ => []
  resources := {
    events := OrderBatch.eventBudget P (sampleCount P) (OrderExecution.canonicalExpansion P)
    resident := (sampleCount P * OrderExecution.sampleWidth P) •
      SpacePool.ofShape (.finite 2) + SpacePool.ofQuantumLayout
        (OrderBatch.layout P (sampleCount P))
    auxiliary := (sampleCount P * OrderExecution.sampleWidth P) •
      SpacePool.ofShape (.finite 2) + SpacePool.ofQuantumLayout
        (OrderBatch.layout P (sampleCount P)) }
  quantumTimeLimit := samplingTimeLimit P

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
  Witness := Unit
  valid := fun environment _ _ => environment = OrderExecution.sourceEnvironment P
  initialization := fun _ _ _ => True
  accepts := fun _ _ initial output => output = recoveredValue P
    (initial.read (OrderBatch.samplesInput P (sampleCount P)))
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun _ _ => []
  resources := {
    events := recoveryEventBudget P
    resident := residentBudget P
    auxiliary := auxiliaryBudget P }
  quantumTimeLimit := recoveryDepthLimit P (fun _ => 1)

end

end QuantumAlg.FiniteCyclicDLP.OrderEndpoint
