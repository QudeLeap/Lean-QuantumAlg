/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Composition
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Algorithm.Problem.Parallel
import all QuantumAlg.Core.Algorithm.Composition
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Borrowed
import all QuantumAlg.Core.Algorithm.Composition.Embedding.Borrowed
import all QuantumAlg.Core.Algorithm.Composition.Parallel.Admission
import all QuantumAlg.Core.Algorithm.Composition.Parallel.Borrowed.Input
import all QuantumAlg.Core.Algorithm.Composition.Parallel.Projection
import all QuantumAlg.Core.Algorithm.Problem.Embedding.Admission
import all QuantumAlg.Core.Execution.Borrowed.Parallel
import all QuantumAlg.Core.Execution.Borrowed.State
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Composition.Laws
import all QuantumAlg.Core.Execution.Composition.Parallel
import all QuantumAlg.Core.Execution.Input.Oracle
import all QuantumAlg.Core.Execution.Input.Oracle.Embedding
import all QuantumAlg.Core.Execution.Input.Oracle.Service
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# Joint borrowed restoration of the actual parallel algorithm

Each original child contract is used only on its actual admitted input. The
embedding theorem retains the full classical frame as a reference tag, and
history naturality recovers the existing inactive service and path encoding.
The left call leaves the original right local input unchanged, so the second
contract applies without a conditional admission assumption. Composing the
two full borrowed observations preserves every caller CQ/reference correlation.
-/

namespace QuantumAlg.Algorithm

noncomputable section

attribute [local instance] Classical.decEq

open Execution

private lemma admits_of_same_state
    {model : ExecutionModel} {ctx : RuntimeCtx model.kind} {shape : CShape}
    (problem : Problem model ctx ctx shape) (environment : model.Environment)
    (witness : problem.Witness) {Reference : Register}
    (actual original : OracleInput model.classicalOracles ctx Reference)
    (same : actual.state = original.state)
    (admitted : problem.Admits environment witness original) :
    problem.Admits environment witness actual := by
  rcases actual with ⟨actual, actualNormalized⟩
  rcases original with ⟨original, originalNormalized⟩
  cases same
  exact admitted

private lemma embed_borrowed_with_history
    {model : ExecutionModel} {localCtx caller : RuntimeCtx model.kind} {shape : CShape}
    (placement : ContextEmbedding localCtx caller)
    (child : Algorithm model localCtx localCtx shape false)
    (problem : Problem model localCtx localCtx shape) (correct : child.Solves problem)
    (environment : model.Environment) (witness : problem.Witness)
    {Reference : Register} (input : OracleInput model.classicalOracles caller Reference)
    {H : Type} [Fintype H] (state : State caller Reference (model.HiddenState × H))
    (same : state.mapHistory Prod.fst = input.state)
    (admitted : (problem.embed placement).Admits
      environment witness input) :
    observeBorrowed Reference
      ((Circuit.embed (allowAllocation := false) placement child.run.code).execute
        environment Reference state) = observeBorrowed Reference state := by
  have restores := algorithm_embed_borrowed (model := model) (allowAllocation := false)
    placement child problem correct environment witness input admitted
  have raw : state.mapClassical (fun record => (record.1, record.2.1)) = input.state :=
    (ExecutionState.executionState_mapClassical_congr state rfl).trans same
  have actual := algorithmRun_restoresBorrowed_with_history
    (embed (allowAllocation := false) placement child).run environment input state raw restores
  exact actual

/-- Both original child contracts restore the complete borrowed interface of the parallel run. -/
public lemma algorithm_parallelClassical_borrowed
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
      environment witness input) :
    (parallelClassical (allowAllocation := allowAllocation)
      join separate first second).run.RestoresBorrowed environment input := by
  let leftEnvironment : (ExecutionModel.classical operations leftService).Environment :=
    ⟨environment.quantum, join.interpretationLeft environment.classical⟩
  let rightEnvironment : (ExecutionModel.classical operations rightService).Environment :=
    ⟨environment.quantum, join.interpretationRight environment.classical⟩
  let original : State (left.disjointUnion right separate) Reference
      (parentService.HiddenState × Store (left.disjointUnion right separate)) :=
    input.state.mapClassical (fun record => (record.1, (record.2, record.1)))
  have originalSame : observeBorrowed Reference original =
      observeBorrowed Reference input.state := by
    refine Eq.trans ?_ (observeBorrowed_mapClassical input.state
      (fun record => (record.1, (record.2, record.1))) (fun _ => rfl))
    exact congrArg (fun current : State (left.disjointUnion right separate) Reference
        (parentService.HiddenState × Store (left.disjointUnion right separate)) =>
      observeBorrowed Reference current)
      (ExecutionState.executionState_mapClassical_congr input.state rfl)
  let leftPlacement := ContextEmbedding.alongUnion left right separate
  let rightPlacement := ContextEmbedding.alongUnionRight left right separate
  let firstCall : Circuit (.classical operations leftService)
      (left.disjointUnion right separate) (left.disjointUnion right separate) false :=
    .embed leftPlacement first.run.code
  let secondCall : Circuit (.classical operations rightService)
      (left.disjointUnion right separate) (left.disjointUnion right separate) false :=
    .embed rightPlacement second.run.code
  let leftResult := firstCall.execute leftEnvironment Reference (serviceInputLeft join original)
  let afterLeft := serviceOutputLeft join leftResult
  have localAdmitted := (Problem.problem_parallelClassical_admits_local_iff
    join separate firstProblem secondProblem environment witness input).mp admitted
  have leftAdmitted :=
    (Problem.problem_embed_admits_local_iff (model := .classical operations leftService)
      leftPlacement firstProblem leftEnvironment witness.1
      (join.leftInput input)).mpr localAdmitted.1
  have firstSame : observeBorrowed Reference afterLeft = observeBorrowed Reference original := by
    have restored : observeBorrowed Reference leftResult =
        observeBorrowed Reference (serviceInputLeft join original) :=
      embed_borrowed_with_history (model := .classical operations leftService)
        leftPlacement first firstProblem firstCorrect leftEnvironment witness.1
        (join.leftInput input) (serviceInputLeft join original)
        (serviceInputLeft_inputRecord_raw join input) leftAdmitted
    exact (observeBorrowed_serviceOutputLeft join leftResult).trans
      (restored.trans (observeBorrowed_serviceInputLeft join original))
  have afterNormalized : afterLeft.IsNormalized := by
    calc
      afterLeft.mass = leftResult.mass := serviceOutputLeft_mass join leftResult
      _ = (serviceInputLeft join original).mass :=
        firstCall.execute_mass leftEnvironment Reference (serviceInputLeft join original)
      _ = original.mass := serviceInputLeft_mass join original
      _ = input.state.mass := input.state.mapClassical_mass _
      _ = 1 := input.normalized
  let rightInput : OracleInput rightService (left.disjointUnion right separate) Reference :=
    { state := (serviceInputRight join afterLeft).mapHistory Prod.fst
      normalized := (State.mapHistory_mass _ _).trans
        ((serviceInputRight_mass join afterLeft).trans afterNormalized) }
  have rightSame : (rightPlacement.localInput rightInput).state =
      (rightPlacement.localInput (join.rightInput input)).state := by
    change rightPlacement.projectState
      ((serviceInputRight join afterLeft).mapHistory Prod.fst) = _
    exact serviceLeft_embed_right_rawInput (model := .classical operations leftService)
      join separate first.run.code leftEnvironment input
  have rightAdmitted :=
    (Problem.problem_embed_admits_local_iff (model := .classical operations rightService)
      rightPlacement secondProblem rightEnvironment witness.2 rightInput).mpr
      (admits_of_same_state (model := .classical operations rightService)
        secondProblem rightEnvironment witness.2 (rightPlacement.localInput rightInput)
        (rightPlacement.localInput (join.rightInput input)) rightSame localAdmitted.2)
  let rightResult := secondCall.execute rightEnvironment
    Reference (serviceInputRight join afterLeft)
  let afterRight := serviceOutputRight join rightResult
  have secondRestored : observeBorrowed Reference rightResult =
      observeBorrowed Reference (serviceInputRight join afterLeft) :=
    embed_borrowed_with_history (model := .classical operations rightService)
      rightPlacement second secondProblem
      secondCorrect rightEnvironment witness.2 rightInput
      (serviceInputRight join afterLeft) rfl rightAdmitted
  have secondSame : observeBorrowed Reference afterRight =
      observeBorrowed Reference afterLeft :=
    (observeBorrowed_serviceOutputRight join rightResult).trans
      (secondRestored.trans (observeBorrowed_serviceInputRight join afterLeft))
  have actual :
      (Circuit.parallelClassical (allowAllocation := allowAllocation)
        join separate first.run.code second.run.code).execute environment Reference original =
      afterRight.mapHistory
        (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) :=
    (Circuit.circuit_execute_parallelClassical (allowAllocation := allowAllocation)
      join separate first.run.code second.run.code
      (environment := environment) Reference original).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  change observeBorrowed Reference
      ((Circuit.parallelClassical (allowAllocation := allowAllocation)
        join separate first.run.code second.run.code).execute environment Reference original) =
    observeBorrowed Reference input.state
  rw [actual]
  exact (observeBorrowed_mapHistory afterRight
    (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2))))).trans
      (secondSame.trans (firstSame.trans originalSame))

/-- Both original child contracts restore the complete borrowed interface of the parallel run. -/
public lemma algorithm_parallelQuantum_borrowed
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
      environment witness input) :
    (parallelQuantum (allowAllocation := allowAllocation)
      join separate first second).run.RestoresBorrowed environment input := by
  let leftEnvironment : (ExecutionModel.quantum gates oracles operations leftService).Environment :=
    ⟨environment.quantum, join.interpretationLeft environment.classical⟩
  let rightEnvironment :
      (ExecutionModel.quantum gates oracles operations rightService).Environment :=
    ⟨environment.quantum, join.interpretationRight environment.classical⟩
  let original : State (left.disjointUnion right separate) Reference
      (parentService.HiddenState × Store (left.disjointUnion right separate)) :=
    input.state.mapClassical (fun record => (record.1, (record.2, record.1)))
  have originalSame : observeBorrowed Reference original =
      observeBorrowed Reference input.state := by
    refine Eq.trans ?_ (observeBorrowed_mapClassical input.state
      (fun record => (record.1, (record.2, record.1))) (fun _ => rfl))
    exact congrArg (fun current : State (left.disjointUnion right separate) Reference
        (parentService.HiddenState × Store (left.disjointUnion right separate)) =>
      observeBorrowed Reference current)
      (ExecutionState.executionState_mapClassical_congr input.state rfl)
  let leftPlacement := ContextEmbedding.alongUnion left right separate
  let rightPlacement := ContextEmbedding.alongUnionRight left right separate
  let firstCall : Circuit (.quantum gates oracles operations leftService)
      (left.disjointUnion right separate) (left.disjointUnion right separate) false :=
    .embed leftPlacement first.run.code
  let secondCall : Circuit (.quantum gates oracles operations rightService)
      (left.disjointUnion right separate) (left.disjointUnion right separate) false :=
    .embed rightPlacement second.run.code
  let leftResult := firstCall.execute leftEnvironment Reference (serviceInputLeft join original)
  let afterLeft := serviceOutputLeft join leftResult
  have localAdmitted := (Problem.problem_parallelQuantum_admits_local_iff
    join separate firstProblem secondProblem environment witness input).mp admitted
  have leftAdmitted :=
    (Problem.problem_embed_admits_local_iff (model := .quantum gates oracles operations leftService)
      leftPlacement firstProblem leftEnvironment witness.1
      (join.leftInput input)).mpr localAdmitted.1
  have firstSame : observeBorrowed Reference afterLeft = observeBorrowed Reference original := by
    have restored : observeBorrowed Reference leftResult =
        observeBorrowed Reference (serviceInputLeft join original) :=
      embed_borrowed_with_history (model := .quantum gates oracles operations leftService)
        leftPlacement first firstProblem firstCorrect leftEnvironment witness.1
        (join.leftInput input) (serviceInputLeft join original)
        (serviceInputLeft_inputRecord_raw join input) leftAdmitted
    exact (observeBorrowed_serviceOutputLeft join leftResult).trans
      (restored.trans (observeBorrowed_serviceInputLeft join original))
  have afterNormalized : afterLeft.IsNormalized := by
    calc
      afterLeft.mass = leftResult.mass := serviceOutputLeft_mass join leftResult
      _ = (serviceInputLeft join original).mass :=
        firstCall.execute_mass leftEnvironment Reference (serviceInputLeft join original)
      _ = original.mass := serviceInputLeft_mass join original
      _ = input.state.mass := input.state.mapClassical_mass _
      _ = 1 := input.normalized
  let rightInput : OracleInput rightService (left.disjointUnion right separate) Reference :=
    { state := (serviceInputRight join afterLeft).mapHistory Prod.fst
      normalized := (State.mapHistory_mass _ _).trans
        ((serviceInputRight_mass join afterLeft).trans afterNormalized) }
  have rightSame : (rightPlacement.localInput rightInput).state =
      (rightPlacement.localInput (join.rightInput input)).state := by
    change rightPlacement.projectState
      ((serviceInputRight join afterLeft).mapHistory Prod.fst) = _
    exact serviceLeft_embed_right_rawInput (model := .quantum gates oracles operations leftService)
      join separate first.run.code leftEnvironment input
  have rightAdmitted :=
    (Problem.problem_embed_admits_local_iff
      (model := .quantum gates oracles operations rightService)
      rightPlacement secondProblem rightEnvironment witness.2 rightInput).mpr
      (admits_of_same_state (model := .quantum gates oracles operations rightService)
        secondProblem rightEnvironment witness.2 (rightPlacement.localInput rightInput)
        (rightPlacement.localInput (join.rightInput input)) rightSame localAdmitted.2)
  let rightResult := secondCall.execute rightEnvironment
    Reference (serviceInputRight join afterLeft)
  let afterRight := serviceOutputRight join rightResult
  have secondRestored : observeBorrowed Reference rightResult =
      observeBorrowed Reference (serviceInputRight join afterLeft) :=
    embed_borrowed_with_history (model := .quantum gates oracles operations rightService)
      rightPlacement second secondProblem
      secondCorrect rightEnvironment witness.2 rightInput
      (serviceInputRight join afterLeft) rfl rightAdmitted
  have secondSame : observeBorrowed Reference afterRight =
      observeBorrowed Reference afterLeft :=
    (observeBorrowed_serviceOutputRight join rightResult).trans
      (secondRestored.trans (observeBorrowed_serviceInputRight join afterLeft))
  have actual :
      (Circuit.parallelQuantum (allowAllocation := allowAllocation)
        join separate first.run.code second.run.code).execute environment Reference original =
      afterRight.mapHistory
        (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) :=
    (Circuit.circuit_execute_parallelQuantum (allowAllocation := allowAllocation)
      join separate first.run.code second.run.code
      (environment := environment) Reference original).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  change observeBorrowed Reference
      ((Circuit.parallelQuantum (allowAllocation := allowAllocation)
        join separate first.run.code second.run.code).execute environment Reference original) =
    observeBorrowed Reference input.state
  rw [actual]
  exact (observeBorrowed_mapHistory afterRight
    (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2))))).trans
      (secondSame.trans (firstSame.trans originalSame))

end

end QuantumAlg.Algorithm
