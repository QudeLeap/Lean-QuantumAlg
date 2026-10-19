/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Algorithm.Composition
public import QuantumAlg.Core.Algorithm.Composition.Parallel.Admission
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Problem.Parallel
import all QuantumAlg.Core.Algorithm.Composition.Parallel.State
import all QuantumAlg.Core.Execution.State.Requirement.Embedding.Holds
import all QuantumAlg.Core.Execution.Input.Oracle.Service
import all QuantumAlg.Core.Execution.Input

/-!
# Original state requirements of the actual parallel execution

The final local state of each child retains its original external reference.
Every original promise therefore applies to its original unconditional input.
The other child's final state need not equal its initial state, and no product
state or independence assumption is used.
-/

namespace QuantumAlg.Algorithm

noncomputable section

open Execution

private lemma caller_eq_of_state_eq {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {first second : Input ctx Reference}
    (same : first.state = second.state) : first = second := by
  cases first
  cases second
  cases same
  rfl

/-- Both sets of original state promises hold for the same complete parallel final state. -/
public lemma algorithm_parallelClassical_states
    {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .classical} {leftShape rightShape : CShape}
    {allowAllocation : Bool}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Algorithm (.classical operations leftService) left left leftShape false)
    (second : Algorithm (.classical operations rightService) right right rightShape false)
    (firstProblem : Problem (.classical operations leftService) left left leftShape)
    (secondProblem : Problem (.classical operations rightService) right right rightShape)
    (firstCorrect : first.Solves firstProblem) (secondCorrect : second.Solves secondProblem)
    (environment : (ExecutionModel.classical operations parentService).Environment)
    (witness : firstProblem.Witness × secondProblem.Witness)
    {Reference : Register}
    (input : OracleInput parentService (left.disjointUnion right separate) Reference)
    (admitted : (Problem.parallelClassical join separate firstProblem secondProblem).Admits
      environment witness input)
    (requirement : StateRequirement (left.disjointUnion right separate)
      (left.disjointUnion right separate))
    (present : requirement ∈
      (Problem.parallelClassical join separate firstProblem secondProblem).states
        environment witness) :
    requirement.Holds input.caller
      ((parallelClassical (allowAllocation := allowAllocation)
        join separate first second).run.finalState environment Reference input.state) := by
  let leftEnvironment : (ExecutionModel.classical operations leftService).Environment :=
    ⟨environment.quantum, join.interpretationLeft environment.classical⟩
  let rightEnvironment : (ExecutionModel.classical operations rightService).Environment :=
    ⟨environment.quantum, join.interpretationRight environment.classical⟩
  have localAdmitted := (Problem.problem_parallelClassical_admits_local_iff
    join separate firstProblem secondProblem environment witness input).mp admitted
  change requirement ∈ (firstProblem.states leftEnvironment witness.1).map
      (StateRequirement.embed (ContextEmbedding.alongUnion left right separate)) ++
    (secondProblem.states rightEnvironment witness.2).map
      (StateRequirement.embed (ContextEmbedding.alongUnionRight left right separate)) at present
  rcases List.mem_append.mp present with present | present
  · obtain ⟨original, originalPresent, same⟩ := List.mem_map.mp present
    subst requirement
    have transferred := StateRequirement.stateRequirement_embed_holds_of_projection
      (ContextEmbedding.alongUnion left right separate) original (join.leftInput input)
      ((parallelClassical (allowAllocation := allowAllocation)
        join separate first second).run.finalState environment Reference input.state)
      (first.run.finalState leftEnvironment Reference
        ((ContextEmbedding.alongUnion left right separate).localInput (join.leftInput input)).state)
      (parallelClassical_finalState_left join separate first second environment input)
      (firstCorrect.states leftEnvironment witness.1 Reference
        ((ContextEmbedding.alongUnion left right separate).localInput (join.leftInput input))
        localAdmitted.1.1 localAdmitted.1.2 original originalPresent)
    rw [caller_eq_of_state_eq (join.serviceJoin_leftInput_caller_state input)] at transferred
    exact transferred
  · obtain ⟨original, originalPresent, same⟩ := List.mem_map.mp present
    subst requirement
    have transferred := StateRequirement.stateRequirement_embed_holds_of_projection
      (ContextEmbedding.alongUnionRight left right separate) original (join.rightInput input)
      ((parallelClassical (allowAllocation := allowAllocation)
        join separate first second).run.finalState environment Reference input.state)
      (second.run.finalState rightEnvironment Reference
        ((ContextEmbedding.alongUnionRight left right separate).localInput
          (join.rightInput input)).state)
      (parallelClassical_finalState_right join separate first second environment input)
      (secondCorrect.states rightEnvironment witness.2 Reference
        ((ContextEmbedding.alongUnionRight left right separate).localInput (join.rightInput input))
        localAdmitted.2.1 localAdmitted.2.2 original originalPresent)
    rw [caller_eq_of_state_eq (join.serviceJoin_rightInput_caller_state input)] at transferred
    exact transferred

/-- Both sets of original state promises hold for the same complete parallel final state. -/
public lemma algorithm_parallelQuantum_states
    {gates : GateModel} {oracles : OracleModel} {operations : ClassicalOpModel}
    {leftService rightService parentService : ClassicalOracleModel}
    {left right : RuntimeCtx .quantum} {leftShape rightShape : CShape}
    {allowAllocation : Bool}
    (join : ClassicalOracleModel.ServiceJoin leftService rightService parentService)
    (separate : RuntimeCtx.StorageDisjoint left right)
    (first : Algorithm (.quantum gates oracles operations leftService) left left leftShape false)
    (second : Algorithm (.quantum gates oracles operations rightService)
      right right rightShape false)
    (firstProblem : Problem (.quantum gates oracles operations leftService) left left leftShape)
    (secondProblem : Problem (.quantum gates oracles operations rightService)
      right right rightShape)
    (firstCorrect : first.Solves firstProblem) (secondCorrect : second.Solves secondProblem)
    (environment : (ExecutionModel.quantum gates oracles operations parentService).Environment)
    (witness : firstProblem.Witness × secondProblem.Witness)
    {Reference : Register}
    (input : OracleInput parentService (left.disjointUnion right separate) Reference)
    (admitted : (Problem.parallelQuantum join separate firstProblem secondProblem).Admits
      environment witness input)
    (requirement : StateRequirement (left.disjointUnion right separate)
      (left.disjointUnion right separate))
    (present : requirement ∈
      (Problem.parallelQuantum join separate firstProblem secondProblem).states
        environment witness) :
    requirement.Holds input.caller
      ((parallelQuantum (allowAllocation := allowAllocation)
        join separate first second).run.finalState environment Reference input.state) := by
  let leftEnvironment : (ExecutionModel.quantum gates oracles operations leftService).Environment :=
    ⟨environment.quantum, join.interpretationLeft environment.classical⟩
  let rightEnvironment :
      (ExecutionModel.quantum gates oracles operations rightService).Environment :=
    ⟨environment.quantum, join.interpretationRight environment.classical⟩
  have localAdmitted := (Problem.problem_parallelQuantum_admits_local_iff
    join separate firstProblem secondProblem environment witness input).mp admitted
  change requirement ∈ (firstProblem.states leftEnvironment witness.1).map
      (StateRequirement.embed (ContextEmbedding.alongUnion left right separate)) ++
    (secondProblem.states rightEnvironment witness.2).map
      (StateRequirement.embed (ContextEmbedding.alongUnionRight left right separate)) at present
  rcases List.mem_append.mp present with present | present
  · obtain ⟨original, originalPresent, same⟩ := List.mem_map.mp present
    subst requirement
    have transferred := StateRequirement.stateRequirement_embed_holds_of_projection
      (ContextEmbedding.alongUnion left right separate) original (join.leftInput input)
      ((parallelQuantum (allowAllocation := allowAllocation)
        join separate first second).run.finalState environment Reference input.state)
      (first.run.finalState leftEnvironment Reference
        ((ContextEmbedding.alongUnion left right separate).localInput (join.leftInput input)).state)
      (parallelQuantum_finalState_left join separate first second environment input)
      (firstCorrect.states leftEnvironment witness.1 Reference
        ((ContextEmbedding.alongUnion left right separate).localInput (join.leftInput input))
        localAdmitted.1.1 localAdmitted.1.2 original originalPresent)
    rw [caller_eq_of_state_eq (join.serviceJoin_leftInput_caller_state input)] at transferred
    exact transferred
  · obtain ⟨original, originalPresent, same⟩ := List.mem_map.mp present
    subst requirement
    have transferred := StateRequirement.stateRequirement_embed_holds_of_projection
      (ContextEmbedding.alongUnionRight left right separate) original (join.rightInput input)
      ((parallelQuantum (allowAllocation := allowAllocation)
        join separate first second).run.finalState environment Reference input.state)
      (second.run.finalState rightEnvironment Reference
        ((ContextEmbedding.alongUnionRight left right separate).localInput
          (join.rightInput input)).state)
      (parallelQuantum_finalState_right join separate first second environment input)
      (secondCorrect.states rightEnvironment witness.2 Reference
        ((ContextEmbedding.alongUnionRight left right separate).localInput (join.rightInput input))
        localAdmitted.2.1 localAdmitted.2.2 original originalPresent)
    rw [caller_eq_of_state_eq (join.serviceJoin_rightInput_caller_state input)] at transferred
    exact transferred

end

end QuantumAlg.Algorithm
