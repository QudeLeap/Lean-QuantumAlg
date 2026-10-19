/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Classical.Oracle.Composition
public import QuantumAlg.Core.Execution.Classical.Step
import all QuantumAlg.Core.Base.Classical.Oracle.Composition

/-!
# Query placement and transition laws for independent services

The queries below use the parent declaration's actual transition on its current
persistent state. Each side receives exactly its declared operands and returns
its actual result. Both chronological orders retain the same joint law after
putting the visible results in canonical left/right order.

The kernel laws apply to arbitrary correlated classical records and complete
subnormalized quantum/reference blocks. They do not identify independent
services with repeated calls to one shared mutable service. Actual executable
queries still require separate storage-placement and resource proofs.
-/

namespace QuantumAlg.ClassicalOracleModel.ServiceJoin

noncomputable section

variable {left right parent : ClassicalOracleModel}

/-- Inject a placed left query without changing its actual input or output cell. -/
@[expose] public def applicationLeft (join : ServiceJoin left right parent)
    {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (application : left.Application ctx) : parent.Application ctx := by
  cases join with
  | sum => exact ⟨.inl application.query, application.input, application.output⟩
  | leftEmpty => exact Empty.elim application.query
  | rightEmpty => exact application

/-- Inject a placed right query without changing its actual input or output cell. -/
@[expose] public def applicationRight (join : ServiceJoin left right parent)
    {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (application : right.Application ctx) : parent.Application ctx := by
  cases join with
  | sum => exact ⟨.inr application.query, application.input, application.output⟩
  | leftEmpty => exact application
  | rightEmpty => exact Empty.elim application.query

/-- Query placement routes the left instruction to its granted parent instance. -/
public lemma serviceJoin_applicationLeft_query (join : ServiceJoin left right parent)
    {kind : ProblemKind} {ctx : RuntimeCtx kind} (application : left.Application ctx) :
    (join.applicationLeft application).query = join.queryLeft application.query := by
  cases join with
  | sum => rfl
  | leftEmpty => exact Empty.elim application.query
  | rightEmpty => rfl

/-- Query placement routes the right instruction to its granted parent instance. -/
public lemma serviceJoin_applicationRight_query (join : ServiceJoin left right parent)
    {kind : ProblemKind} {ctx : RuntimeCtx kind} (application : right.Application ctx) :
    (join.applicationRight application).query = join.queryRight application.query := by
  cases join with
  | sum => rfl
  | leftEmpty => rfl
  | rightEmpty => exact Empty.elim application.query

/-- Execute the left transition then the right, retaining both visible results. -/
public def leftThenRight (join : ServiceJoin left right parent)
    (environment : parent.Interpretation)
    (leftQuery : left.Query) (rightQuery : right.Query) (hidden : parent.HiddenState)
    (leftInput : (left.inputShape leftQuery).Value)
    (rightInput : (right.inputShape rightQuery).Value) :
    PMF (parent.HiddenState ×
      ((left.outputShape leftQuery).Value × (right.outputShape rightQuery).Value)) :=
  (parent.transition environment (join.queryLeft leftQuery) hidden
    (join.inputLeft leftQuery leftInput)).bind fun first =>
      (parent.transition environment (join.queryRight rightQuery) first.1
        (join.inputRight rightQuery rightInput)).map fun second =>
          (second.1, ((join.outputLeft leftQuery).symm first.2,
            (join.outputRight rightQuery).symm second.2))

/-- The sum service retains the two original transitions and both resulting hidden states. -/
public lemma serviceJoin_leftThenRight_sum (left right : ClassicalOracleModel)
    (environment : (ClassicalOracleModel.sum left right).Interpretation)
    (leftQuery : left.Query) (rightQuery : right.Query)
    (leftHidden : left.HiddenState) (rightHidden : right.HiddenState)
    (leftInput : (left.inputShape leftQuery).Value)
    (rightInput : (right.inputShape rightQuery).Value) :
    (ServiceJoin.sum left right).leftThenRight environment leftQuery rightQuery
      (leftHidden, rightHidden) leftInput rightInput =
      (left.transition environment.1 leftQuery leftHidden leftInput).bind fun first =>
        (right.transition environment.2 rightQuery rightHidden rightInput).map fun second =>
          ((first.1, second.1), (first.2, second.2)) := by
  simp only [leftThenRight, queryLeft, queryRight, inputLeft, inputRight, outputLeft,
    outputRight, ClassicalOracleModel.transition, PMF.bind_map, PMF.map_comp, Function.comp_def]
  rfl

/-- Execute in the other order while retaining canonical left/right result order. -/
public def rightThenLeft (join : ServiceJoin left right parent)
    (environment : parent.Interpretation)
    (leftQuery : left.Query) (rightQuery : right.Query) (hidden : parent.HiddenState)
    (leftInput : (left.inputShape leftQuery).Value)
    (rightInput : (right.inputShape rightQuery).Value) :
    PMF (parent.HiddenState ×
      ((left.outputShape leftQuery).Value × (right.outputShape rightQuery).Value)) :=
  (parent.transition environment (join.queryRight rightQuery) hidden
    (join.inputRight rightQuery rightInput)).bind fun first =>
      (parent.transition environment (join.queryLeft leftQuery) first.1
        (join.inputLeft leftQuery leftInput)).map fun second =>
          (second.1, ((join.outputLeft leftQuery).symm second.2,
            (join.outputRight rightQuery).symm first.2))

/-- Independent service transitions commute without assumptions on their current states. -/
public lemma serviceJoin_transitions_commute (join : ServiceJoin left right parent)
    (environment : parent.Interpretation)
    (leftQuery : left.Query) (rightQuery : right.Query) (hidden : parent.HiddenState)
    (leftInput : (left.inputShape leftQuery).Value)
    (rightInput : (right.inputShape rightQuery).Value) :
    join.leftThenRight environment leftQuery rightQuery hidden leftInput rightInput =
      join.rightThenLeft environment leftQuery rightQuery hidden leftInput rightInput := by
  cases join with
  | sum left right =>
      simp only [leftThenRight, rightThenLeft, queryLeft, queryRight, inputLeft,
        inputRight, outputLeft, outputRight,
        ClassicalOracleModel.transition, PMF.bind_map, PMF.map_comp, Function.comp_def]
      exact PMF.bind_comm (left.transition environment.1 leftQuery hidden.1 leftInput)
        (right.transition environment.2 rightQuery hidden.2 rightInput)
        (fun first second => PMF.pure ((first.1, second.1), (first.2, second.2)))
  | leftEmpty => exact Empty.elim leftQuery
  | rightEmpty => exact Empty.elim rightQuery

/-- The initial hidden states and operands may have any joint distribution. -/
public lemma serviceJoin_correlated_initial_law_commutes
    (join : ServiceJoin left right parent) (environment : parent.Interpretation)
    (leftQuery : left.Query) (rightQuery : right.Query)
    {Record : Type} (initial : PMF Record) (hidden : Record → parent.HiddenState)
    (leftInput : Record → (left.inputShape leftQuery).Value)
    (rightInput : Record → (right.inputShape rightQuery).Value) :
    initial.bind (fun record =>
      (join.leftThenRight environment leftQuery rightQuery
        (hidden record) (leftInput record) (rightInput record)).map
          (fun result => (record, result))) =
    initial.bind (fun record =>
      (join.rightThenLeft environment leftQuery rightQuery
        (hidden record) (leftInput record) (rightInput record)).map
          (fun result => (record, result))) := by
  apply congrArg (PMF.bind initial)
  funext record
  exact congrArg (PMF.map (fun result => (record, result)))
    (join.serviceJoin_transitions_commute environment leftQuery rightQuery _ _ _)

/-- Transition commutation retains arbitrary subnormalized quantum/reference blocks. -/
public lemma serviceJoin_correlated_quantum_blocks_commute
    (join : ServiceJoin left right parent) (environment : parent.Interpretation)
    (leftQuery : left.Query) (rightQuery : right.Query)
    {Record : Type} [Fintype Record] {R : Register} (state : ExecutionState Record R)
    (hidden : Record → parent.HiddenState)
    (leftInput : Record → (left.inputShape leftQuery).Value)
    (rightInput : Record → (right.inputShape rightQuery).Value) :
    Execution.kernelChoice state (fun record => join.leftThenRight environment leftQuery rightQuery
      (hidden record) (leftInput record) (rightInput record)) =
    Execution.kernelChoice state (fun record => join.rightThenLeft environment leftQuery rightQuery
      (hidden record) (leftInput record) (rightInput record)) := by
  apply congrArg (Execution.kernelChoice state)
  funext record
  exact join.serviceJoin_transitions_commute environment leftQuery rightQuery _ _ _

end

end QuantumAlg.ClassicalOracleModel.ServiceJoin
