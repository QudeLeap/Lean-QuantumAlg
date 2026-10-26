/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Instrument.Execution
import all QuantumAlg.Core.Execution.Instrument.Execution
public import QuantumAlg.Core.Execution.Instrument.Reference
import all QuantumAlg.Core.Execution.Instrument.Reference

/-!
# Complete local records of actual circuit instructions

Each certificate states the full interpreter equation of its fixed actual
Circuit, with reference-independent local Kraus matrices. Composition uses
the actual returned Store and both original Paths. These algebraic builders
do not assert the certificate of a concrete circuit; that consumer
must construct every field from its actual query, call and scope equations.
-/

@[expose] public section

namespace QuantumAlg.Execution

noncomputable section

open Instrument
open scoped BigOperators

attribute [local instance] Classical.decEq

variable {gates : GateModel} {oracles : OracleModel}
  {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {allowAllocation : Bool}

private lemma referenceLift_mul {Local Reference : Register}
    (left right : HilbertOperator Local) :
    referenceLift Reference (left * right) =
      referenceLift Reference left * referenceLift Reference right := by
  ext row column
  change (∑ middle : Local.Index, left row.1 middle * right middle column.1) *
      (if row.2 = column.2 then (1 : Complex) else 0) =
    ∑ middle : Local.Index × Reference.Index,
      (left row.1 middle.1 * (if row.2 = middle.2 then 1 else 0)) *
        (right middle.1 column.1 * (if middle.2 = column.2 then 1 else 0))
  simp [Fintype.sum_prod_type, mul_ite, ite_mul]

private lemma ite_decisions {Value : Type} {proposition : Prop}
    (first second : Decidable proposition) (yes no : Value) :
    @ite Value proposition first yes no = @ite Value proposition second yes no := by
  cases first with
  | isTrue selected =>
      cases second with
      | isTrue _ => rfl
      | isFalse absent => exact False.elim (absent selected)
  | isFalse absent =>
      cases second with
      | isTrue selected => exact False.elim (absent selected)
      | isFalse _ => rfl

private lemma sum_condition_decisions {Original Outcome Value : Type}
    [Fintype Original] [Fintype Outcome] [AddCommMonoid Value]
    (predicate : Original → Outcome → Prop)
    (first second : ∀ original outcome, Decidable (predicate original outcome))
    (value : Original → Outcome → Value) :
    (∑ original, ∑ outcome,
      @ite Value (predicate original outcome) (first original outcome)
        (value original outcome) 0) =
    ∑ original, ∑ outcome,
      @ite Value (predicate original outcome) (second original outcome)
        (value original outcome) 0 := by
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  exact ite_decisions _ _ _ _

/-- A full arbitrary-input equation of one fixed actual Circuit, with all real records retained. -/
structure Instrument
    (code : Circuit (.quantum gates oracles operations services)
      ctx ctx allowAllocation) (Outcome : Type) [Fintype Outcome]
    (environment : (ExecutionModel.quantum gates oracles operations
      services).Environment) where
  /-- The returned Store and actual Path indexed by the input Store and retained outcome. -/
  record : Store ctx → Outcome → Store ctx × code.Path
  /-- The local Kraus matrix indexed by the same input Store and retained outcome. -/
  operator : Store ctx → Outcome → HilbertOperator ctx.register
  /-- The complete actual block equation for every reference and incoming history. -/
  blocks : ∀ (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History × code.Path))),
    ((code.execute environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ outcome : Outcome,
        if retainedRecord (services := services) record original outcome = result then
          referenceLift Reference (operator original.1 outcome) * (state.block original).matrix *
            (referenceLift Reference (operator original.1 outcome)).conjTranspose
        else 0

namespace Instrument

variable {FirstOutcome SecondOutcome : Type}
  [Fintype FirstOutcome] [Fintype SecondOutcome]
  {first second : Circuit (.quantum gates oracles operations services)
    ctx ctx allowAllocation}
  {environment : (ExecutionModel.quantum gates oracles operations
    services).Environment}

/-- The actual second component reads the exact Store produced by the first measured component. -/
def seq (head : Instrument first FirstOutcome environment)
    (tail : Instrument second SecondOutcome environment) :
    Instrument (first.seq second) (FirstOutcome × SecondOutcome) environment where
  record store outcomes :=
    sequenceRetainedRecord (operations := operations) (services := services)
      first second head.record tail.record store outcomes.1 outcomes.2
  operator store outcomes :=
    tail.operator (head.record store outcomes.1).1 outcomes.2 * head.operator store outcomes.1
  blocks := by
    intro Reference History _ state result
    have actual := execute_sequenceRetainedBlocks
      (gates := gates) (oracles := oracles)
      (operations := operations) (services := services) first second head.record tail.record
      (fun reference store outcome => referenceLift reference (head.operator store outcome))
      (fun reference store outcome => referenceLift reference (tail.operator store outcome))
      environment
      (by
        intro reference history _ current selected
        exact (head.blocks reference current selected).trans (sum_condition_decisions _ _ _ _))
      (by
        intro reference history _ current selected
        exact (tail.blocks reference current selected).trans (sum_condition_decisions _ _ _ _))
      Reference state result
    refine actual.trans ?_
    apply Finset.sum_congr rfl
    intro original _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro firstOutcome _
    apply Finset.sum_congr rfl
    intro secondOutcome _
    by_cases selected : retainedRecord (services := services)
        (fun store outcomes => sequenceRetainedRecord
          (operations := operations) (services := services) first second head.record tail.record
          store outcomes.1 outcomes.2) original (firstOutcome, secondOutcome) = result
    · rw [if_pos selected, if_pos selected, referenceLift_mul]
    · rw [if_neg selected, if_neg selected]

/-- Complete local-Kraus records imply exact naturality on any untouched reference unitary. -/
lemma reference_unitary {Outcome : Type} [Fintype Outcome]
    {code : Circuit (.quantum gates oracles operations services)
      ctx ctx allowAllocation}
    {environment : (ExecutionModel.quantum gates oracles
      operations services).Environment}
    (actual : Instrument code Outcome environment) (Reference : Register)
    (operator : UnitaryOperator Reference) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    code.execute environment Reference
        (state.applyUnitary (fun _ =>
          UnitaryOperator.prodTensor (1 : UnitaryOperator ctx.register) operator)) =
      (code.execute environment Reference state).applyUnitary (fun _ =>
        UnitaryOperator.prodTensor (1 : UnitaryOperator ctx.register) operator) := by
  exact retained_referenceUnitary
    (fun current => code.execute environment Reference current)
    (retainedRecord (services := services) actual.record)
    (fun original outcome => actual.operator original.1 outcome)
    (by
      intro current selected
      exact (actual.blocks Reference current selected).trans (sum_condition_decisions _ _ _ _))
    operator state

end Instrument

end

end QuantumAlg.Execution
