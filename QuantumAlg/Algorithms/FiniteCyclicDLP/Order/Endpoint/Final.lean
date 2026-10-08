/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Endpoint.Scalar
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.CyclePlan
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

private theorem output_atom_eq_relational {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    (selected : AlgorithmRun model pre post shape)
    {Reference : Register}
    (input : Execution.OracleInput model.classicalOracles pre Reference)
    (value : shape.Value) :
    selected.outputDistribution input value =
      (selected.relationalDistribution input).toOuterMeasure
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

private theorem accepted_probability (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (OrderExecution.model P).classicalOracles
      OrderExecution.pre Reference) :
    ((algorithm P).relationalDistribution input).toOuterMeasure
        {pair | (problem P secret).accepts pair.1 pair.2} =
      (run P).outputDistribution input
        (.optionSome
          (CShape.wordOfNat (OrderPreparation.width P) secret.secret.val)) := by
  change ((run P).relationalDistribution input).toOuterMeasure
      {pair | pair.2 = .optionSome
        (CShape.wordOfNat (OrderPreparation.width P) secret.secret.val)} = _
  exact (output_atom_eq_relational (run P) input _).symm

private theorem solves_success (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (OrderExecution.model P).classicalOracles
      OrderExecution.pre Reference) :
    (problem P secret).valid input.caller.localState →
      (problem P secret).initialization input.localState →
        (problem P secret).successLB.value ≤
          ((algorithm P).relationalDistribution input).toOuterMeasure
            {pair | (problem P secret).accepts pair.1 pair.2} := by
  intro _valid _initialized
  rw [problem_success_value, accepted_probability]
  exact run_success P secret input

private theorem solves_states (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (OrderExecution.model P).classicalOracles
      OrderExecution.pre Reference) :
    (problem P secret).valid input.caller.localState →
      (problem P secret).initialization input.localState →
        ∀ requirement ∈ (problem P secret).states,
          requirement.Holds input.caller ((algorithm P).run.finalState Reference input.state) := by
  intro _valid _initialized _requirement present
  rw [problem_states] at present
  exact False.elim (List.not_mem_nil present)

private theorem solves_borrowed (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (OrderExecution.model P).classicalOracles
      OrderExecution.pre Reference) :
    (problem P secret).valid input.caller.localState →
      (problem P secret).initialization input.localState →
        (algorithm P).run.RestoresBorrowed input := by
  intro _valid _initialized
  have restored := Circuit.borrowedRestored_of_noBorrowedQuantum (code P)
    RuntimeCtx.borrowedQuantumWires_empty Reference
    (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))
  have history := Execution.observeBorrowed_mapClassical input.state
    (fun value => (value.1, (value.2, value.1))) (fun _ => rfl)
  change (code P).BorrowedRestored Reference input.state
    ((code P).execute Reference
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1)))))
  unfold Circuit.BorrowedRestored at restored ⊢
  rw [restored]
  refine Eq.trans ?_ history
  apply congrArg (Execution.observeBorrowed Reference)
  exact ExecutionState.executionState_mapClassical_congr_decision _ _ _ (fun _ => rfl) _ _

private theorem solves_events (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (OrderExecution.model P).classicalOracles
      OrderExecution.pre Reference) :
    (problem P secret).valid input.caller.localState →
      (problem P secret).initialization input.localState →
        ∀ path, (algorithm P).run.Supports Reference input.state path →
          (algorithm P).run.code.resourcePool path ≤ (problem P secret).resources.events := by
  intro _valid _initialized path _supported
  simpa only [algorithm, run, problem_event_budget] using code_pool_le P path

private theorem solves_resident (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (OrderExecution.model P).classicalOracles
      OrderExecution.pre Reference) :
    (problem P secret).valid input.caller.localState →
      (problem P secret).initialization input.localState →
        ∀ path, (algorithm P).run.Supports Reference input.state path →
          (algorithm P).run.code.peakResidentSpace path ≤
            (problem P secret).resources.resident := by
  intro _valid _initialized path _supported
  simpa only [algorithm, run, problem_resident_budget] using code_resident_le P path

private theorem solves_auxiliary (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (OrderExecution.model P).classicalOracles
      OrderExecution.pre Reference) :
    (problem P secret).valid input.caller.localState →
      (problem P secret).initialization input.localState →
        ∀ path, (algorithm P).run.Supports Reference input.state path →
          (algorithm P).run.code.peakAuxiliarySpace path ≤
            (problem P secret).resources.auxiliary := by
  intro _valid _initialized path _supported
  simpa only [algorithm, run, problem_auxiliary_budget] using code_auxiliary_le P path

private theorem solves_depth (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (OrderExecution.model P).classicalOracles
      OrderExecution.pre Reference) :
    (problem P secret).valid input.caller.localState →
      (problem P secret).initialization input.localState →
        ∀ path, (algorithm P).run.Supports Reference input.state path →
          (problem P secret).depth.Holds (algorithm P).run.code path := by
  intro _valid _initialized path _supported
  rw [problem_depth]
  exact code_depth_le P path

/-- The complete execution solves the independent all-order contract. -/
public theorem algorithm_solves (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P) :
    Algorithm.Solves (algorithm P) (problem P secret) where
  success := fun _ input => solves_success P secret input
  states := fun _ input => solves_states P secret input
  borrowed := fun _ input => solves_borrowed P secret input
  events := fun _ input => solves_events P secret input
  resident := fun _ input => solves_resident P secret input
  auxiliary := fun _ input => solves_auxiliary P secret input
  depth := fun _ input => solves_depth P secret input

/-- The complete endpoint solves both the source outcome contract and the caller's
independent whole-batch sampling and classical recovery protocols. -/
public def algorithmCycleSolves (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P) :
    Algorithm.CycleSolves (algorithm P) (cycleProblem P secret) where
  correctness := algorithm_solves P secret
  schedule := codeCycleSchedule P secret
  entry := by
    intro Reference input admissible
    change True ∧ True
    exact ⟨True.intro, True.intro⟩

end

end QuantumAlg.FiniteCyclicDLP.OrderEndpoint
