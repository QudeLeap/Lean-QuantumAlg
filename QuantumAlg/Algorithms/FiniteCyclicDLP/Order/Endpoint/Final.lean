/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Endpoint.Scalar
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Complete all-positive-order finite-cyclic DLP correctness

The named algorithm is exactly the fresh-bank sampler followed by the actual
checked recovery circuit. Its success, resource and restoration obligations
all refer to that single execution.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderEndpoint

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G] [Fintype G]

private lemma output_atom_eq_relational {model : ExecutionModel}
    {environment : model.Environment}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    (selected : AlgorithmRun model pre post shape)
    {Reference : Register}
    (input : Execution.OracleInput model.classicalOracles pre Reference)
    (value : shape.Value) :
    selected.outputDistribution environment input value =
      (selected.relationalDistribution environment input).toOuterMeasure
        {pair | pair.2 = value} := by
  rw [← PMF.toOuterMeasure_apply_singleton]
  simp only [AlgorithmRun.outputDistribution, AlgorithmRun.relationalDistribution,
    PMF.toOuterMeasure_map_apply]
  rfl

/-- The sole candidate is the complete endpoint run. -/
@[expose] public def algorithm (P : KnownOrderProblem G) :
    Algorithm (OrderExecution.model P) OrderExecution.pre (outputContext P)
      (.option (.unsignedWord (OrderPreparation.width P))) where
  run := run P

private lemma accepted_probability (P : KnownOrderProblem G)
    (environment : (OrderExecution.model P).Environment)
    (secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (OrderExecution.model P).classicalOracles
      OrderExecution.pre Reference) :
    ((algorithm P).relationalDistribution environment input).toOuterMeasure
        {pair | (problem P).accepts environment secret pair.1 pair.2} =
      (run P).outputDistribution environment input
        (.optionSome
          (CShape.wordOfNat (OrderPreparation.width P) secret.secret.val)) := by
  change ((run P).relationalDistribution environment input).toOuterMeasure
      {pair | pair.2 = .optionSome
        (CShape.wordOfNat (OrderPreparation.width P) secret.secret.val)} = _
  exact (output_atom_eq_relational (run P) input _).symm

private lemma solves_success (P : KnownOrderProblem G)
    (environment : (OrderExecution.model P).Environment)
    (secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (OrderExecution.model P).classicalOracles
      OrderExecution.pre Reference) :
    (problem P).valid environment secret input.caller.localState →
      (problem P).initialization environment secret input.localState →
        ((problem P).successLB environment secret).value ≤
          ((algorithm P).relationalDistribution environment input).toOuterMeasure
            {pair | (problem P).accepts environment secret pair.1 pair.2} := by
  intro valid _initialized
  have same : environment = OrderExecution.sourceEnvironment P := valid
  subst environment
  rw [problem_success_value, accepted_probability]
  exact run_success P secret input

private lemma solves_states (P : KnownOrderProblem G)
    (environment : (OrderExecution.model P).Environment)
    (secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (OrderExecution.model P).classicalOracles
      OrderExecution.pre Reference) :
    (problem P).valid environment secret input.caller.localState →
      (problem P).initialization environment secret input.localState →
        ∀ requirement ∈ (problem P).states environment secret,
          requirement.Holds input.caller
            ((algorithm P).run.finalState environment Reference input.state) := by
  intro _valid _initialized _requirement present
  rw [problem_states] at present
  exact False.elim (List.not_mem_nil present)

private lemma solves_borrowed (P : KnownOrderProblem G)
    (environment : (OrderExecution.model P).Environment)
    (secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (OrderExecution.model P).classicalOracles
      OrderExecution.pre Reference) :
    (problem P).valid environment secret input.caller.localState →
      (problem P).initialization environment secret input.localState →
        (algorithm P).run.RestoresBorrowed environment input := by
  intro _valid _initialized
  have restored := Circuit.borrowedRestored_of_noBorrowedQuantum (code P) environment
    RuntimeCtx.borrowedQuantumWires_empty Reference
    (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))
  have history := Execution.observeBorrowed_mapClassical input.state
    (fun value => (value.1, (value.2, value.1))) (fun _ => rfl)
  change (code P).BorrowedRestored Reference input.state
    ((code P).execute environment Reference
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1)))))
  unfold Circuit.BorrowedRestored at restored ⊢
  rw [restored]
  refine Eq.trans ?_ history
  apply congrArg (Execution.observeBorrowed Reference)
  exact ExecutionState.executionState_mapClassical_congr_decision _ _ _ (fun _ => rfl) _ _

private lemma solves_events (P : KnownOrderProblem G)
    (environment : (OrderExecution.model P).Environment)
    (secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (OrderExecution.model P).classicalOracles
      OrderExecution.pre Reference) :
    (problem P).valid environment secret input.caller.localState →
      (problem P).initialization environment secret input.localState →
        ∀ path, (algorithm P).run.Supports environment Reference input.state path →
          (algorithm P).run.code.resourcePool path ≤ (problem P).resources.events := by
  intro _valid _initialized path _supported
  simpa only [algorithm, run, problem_event_budget] using code_pool_le P path

private lemma solves_resident (P : KnownOrderProblem G)
    (environment : (OrderExecution.model P).Environment)
    (secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (OrderExecution.model P).classicalOracles
      OrderExecution.pre Reference) :
    (problem P).valid environment secret input.caller.localState →
      (problem P).initialization environment secret input.localState →
        ∀ path, (algorithm P).run.Supports environment Reference input.state path →
          (algorithm P).run.code.peakResidentSpace path ≤
            (problem P).resources.resident := by
  intro _valid _initialized path _supported
  simpa only [algorithm, run, problem_resident_budget] using code_resident_le P path

private lemma solves_auxiliary (P : KnownOrderProblem G)
    (environment : (OrderExecution.model P).Environment)
    (secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (OrderExecution.model P).classicalOracles
      OrderExecution.pre Reference) :
    (problem P).valid environment secret input.caller.localState →
      (problem P).initialization environment secret input.localState →
        ∀ path, (algorithm P).run.Supports environment Reference input.state path →
          (algorithm P).run.code.peakAuxiliarySpace path ≤
            (problem P).resources.auxiliary := by
  intro _valid _initialized path _supported
  simpa only [algorithm, run, problem_auxiliary_budget] using code_auxiliary_le P path

private lemma solves_time (P : KnownOrderProblem G)
    (environment : (OrderExecution.model P).Environment)
    (secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (OrderExecution.model P).classicalOracles
      OrderExecution.pre Reference) :
    (problem P).valid environment secret input.caller.localState →
      (problem P).initialization environment secret input.localState →
        ∀ path, (algorithm P).run.Supports environment Reference input.state path →
          (algorithm P).quantumTime path ≤ (problem P).quantumTimeLimit := by
  intro _valid _initialized path _supported
  rw [orderEndpoint_problem_quantumTimeLimit]
  exact (Circuit.quantumTime_le_unitDepth _ _).trans (code_depth_le P path)

/-- The complete execution solves the independent all-order contract. -/
public lemma algorithm_solves (P : KnownOrderProblem G) :
    Algorithm.Solves (algorithm P) (problem P) where
  success := fun environment secret _ input => solves_success P environment secret input
  states := fun environment secret _ input => solves_states P environment secret input
  borrowed := fun environment secret _ input => solves_borrowed P environment secret input
  events := fun environment secret _ input => solves_events P environment secret input
  resident := fun environment secret _ input => solves_resident P environment secret input
  auxiliary := fun environment secret _ input => solves_auxiliary P environment secret input
  time := fun environment secret _ input => solves_time P environment secret input

end

end QuantumAlg.FiniteCyclicDLP.OrderEndpoint
