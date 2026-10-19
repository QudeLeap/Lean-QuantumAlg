/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.PostReduction.Layout

/-!
# Actual final first-direction second-pair reduction

The actual refreshed dot product feeds the original first-direction division.
Its stored quotient drives the final third-row reduction in the same circuit
interpreter, preserving complete histories and quantum-reference blocks.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairPostReduction

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual division and row update for the final first-direction coefficient. -/
def divisionReductionInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (RoundedDiv.body refs.machine.division31)
    (LatticeArithmetic.pointReduce (writeInput refs.machine.division31.output)
      refs.machine.basis.first refs.machine.basis.third refs.machine.reduceProduct)

/-- Actual division branch path and the six native third-row updates. -/
def divisionReductionStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (divisionReductionInto (model := model) refs).Path :=
  let divided := RoundedDiv.bodyStep (model := model) refs.machine.division31 store
  let reduced := LatticeArithmetic.pointStep (model := model)
    (writeInput refs.machine.division31.output)
    refs.machine.basis.first refs.machine.basis.third refs.machine.reduceProduct divided.1
  (reduced.1, (divided.2, reduced.2))

/-- Execute the original refresh, division and first-to-third row reduction chronologically. -/
def postReductionInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (LatticeDotRefresh.refreshInto refs.machine.basis.third refs.machine.basis.first
    (refreshG31Refs refs)) (divisionReductionInto (model := model) refs)

/-- Actual final store and recorded path of all three post-reduction stages. -/
def postReductionStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (postReductionInto (model := model) refs).Path :=
  let refreshed := LatticeDotRefresh.refreshStep (model := model)
    refs.machine.basis.third refs.machine.basis.first (refreshG31Refs refs) store
  let reduced := divisionReductionStep (model := model) refs refreshed.1
  (reduced.1, (refreshed.2, reduced.2))

/-- The actual stored quotient feeds the final row reduction in the complete interpreter. -/
lemma divisionReductionInto_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (divisionReductionInto (model := model) refs).execute environment Reference state =
      state.mapClassical (fun entry =>
        let actual := divisionReductionStep (model := model) refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    (RoundedDiv.body (model := model) refs.machine.division31)
    (LatticeArithmetic.pointReduce (model := model)
      (writeInput refs.machine.division31.output)
      refs.machine.basis.first refs.machine.basis.third refs.machine.reduceProduct)
    (fun before =>
      let actual := RoundedDiv.bodyStep (model := model) refs.machine.division31 before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := LatticeArithmetic.pointStep (model := model)
        (writeInput refs.machine.division31.output) refs.machine.basis.first
        refs.machine.basis.third refs.machine.reduceProduct before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => RoundedDiv.body_execute _ reference current)
    (fun reference _history _ current => LatticeArithmetic.pointReduce_execute
      _ _ _ _ reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Complete actual final reduction uses the actual refreshed numerator without a second runtime. -/
lemma postReductionInto_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (postReductionInto (model := model) refs).execute environment Reference state =
      state.mapClassical (fun entry =>
        let actual := postReductionStep (model := model) refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    (LatticeDotRefresh.refreshInto (model := model)
      refs.machine.basis.third refs.machine.basis.first (refreshG31Refs refs))
    (divisionReductionInto (model := model) refs)
    (fun before =>
      let actual := LatticeDotRefresh.refreshStep (model := model)
        refs.machine.basis.third refs.machine.basis.first (refreshG31Refs refs) before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := divisionReductionStep (model := model) refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      LatticeDotRefresh.refreshInto_execute _ _ _ reference current)
    (fun reference _history _ current => divisionReductionInto_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairPostReduction
