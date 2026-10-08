/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Prefix.Layout

/-!
# Actual second-pair reduction prefix

The actual refreshed Gram words feed the two arithmetic expressions, then
rounded division and the actual third-row reduction. Each chronological stage
consumes its predecessor's store and carries its own actual branch path.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairMachine

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Actual second-direction quotient followed by the third-row reduction. -/
def divisionReductionInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (RoundedDiv.body refs.division32)
    (LatticeArithmetic.pointReduce (writeInput refs.division32.output)
      refs.basis.second refs.basis.third refs.reduceProduct)

/-- Actual division path and the six dependent row-update instructions. -/
def divisionReductionStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (divisionReductionInto refs).Path :=
  let divided := RoundedDiv.bodyStep (model := model) refs.division32 store
  let reduced := LatticeArithmetic.pointStep (model := model)
    (writeInput refs.division32.output) refs.basis.second refs.basis.third
    refs.reduceProduct divided.1
  (reduced.1, (divided.2, reduced.2))

/-- Refresh the second third-row dot product before deriving both actual division inputs. -/
def refresh32InputsInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (LatticeDotRefresh.refreshInto refs.basis.third refs.basis.second (refreshG32Refs refs))
    (LatticeSecondReductionInputs.secondReductionInputsInto (reductionInputs refs)
      refs.reductionInputs)

/-- Actual refreshed `g32` feeds both original Gram expressions. -/
def refresh32InputsStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (refresh32InputsInto refs).Path :=
  let refreshed := LatticeDotRefresh.refreshStep (model := model)
    refs.basis.third refs.basis.second (refreshG32Refs refs) store
  let inputs := LatticeSecondReductionInputs.secondReductionInputsStep (model := model)
    (reductionInputs refs) refs.reductionInputs refreshed.1
  (inputs.1, (refreshed.2, inputs.2))

/-- Refresh both original dot products and derive the actual division inputs. -/
def refreshInputsInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (LatticeDotRefresh.refreshInto refs.basis.second refs.basis.first (refreshG21Refs refs))
    (refresh32InputsInto refs)

/-- Actual chronological stores of both dot refreshes and the six arithmetic writes. -/
def refreshInputsStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (refreshInputsInto refs).Path :=
  let refreshed := LatticeDotRefresh.refreshStep (model := model)
    refs.basis.second refs.basis.first (refreshG21Refs refs) store
  let inputs := refresh32InputsStep (model := model) refs refreshed.1
  (inputs.1, (refreshed.2, inputs.2))

/-- Execute the original second-direction reduction from the actual original store. -/
def secondPairPrefixInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (refreshInputsInto refs) (divisionReductionInto refs)

/-- Actual final store and complete recorded path of the five prefix stages. -/
def secondPairPrefixStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (secondPairPrefixInto refs).Path :=
  let inputs := refreshInputsStep (model := model) refs store
  let reduced := divisionReductionStep (model := model) refs inputs.1
  (reduced.1, (inputs.2, reduced.2))

/-- Full actual division and row reduction preserve histories and quantum-reference blocks. -/
theorem divisionReductionInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (divisionReductionInto (model := model) refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := divisionReductionStep (model := model) refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (RoundedDiv.body (model := model) refs.division32)
    (LatticeArithmetic.pointReduce (model := model) (writeInput refs.division32.output)
      refs.basis.second refs.basis.third refs.reduceProduct)
    (fun before =>
      let actual := RoundedDiv.bodyStep (model := model) refs.division32 before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := LatticeArithmetic.pointStep (model := model)
        (writeInput refs.division32.output) refs.basis.second refs.basis.third
        refs.reduceProduct before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => RoundedDiv.body_execute _ reference current)
    (fun reference _history _ current =>
      LatticeArithmetic.pointReduce_execute _ _ _ _ reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Full actual refreshed `g32` and arithmetic execution compose without a parallel store model. -/
theorem refresh32InputsInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (refresh32InputsInto (model := model) refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := refresh32InputsStep (model := model) refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeDotRefresh.refreshInto (model := model)
      refs.basis.third refs.basis.second (refreshG32Refs refs))
    (LatticeSecondReductionInputs.secondReductionInputsInto (model := model)
      (reductionInputs refs) refs.reductionInputs)
    (fun before =>
      let actual := LatticeDotRefresh.refreshStep (model := model)
        refs.basis.third refs.basis.second (refreshG32Refs refs) before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := LatticeSecondReductionInputs.secondReductionInputsStep (model := model)
        (reductionInputs refs) refs.reductionInputs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      LatticeDotRefresh.refreshInto_execute _ _ _ reference current)
    (fun reference _history _ current =>
      LatticeSecondReductionInputs.secondReductionInputsInto_execute _ _ reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Complete actual preparation of the original numerator and denominator retains full state. -/
theorem refreshInputsInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (refreshInputsInto (model := model) refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := refreshInputsStep (model := model) refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeDotRefresh.refreshInto (model := model)
      refs.basis.second refs.basis.first (refreshG21Refs refs))
    (refresh32InputsInto (model := model) refs)
    (fun before =>
      let actual := LatticeDotRefresh.refreshStep (model := model)
        refs.basis.second refs.basis.first (refreshG21Refs refs) before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := refresh32InputsStep (model := model) refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      LatticeDotRefresh.refreshInto_execute _ _ _ reference current)
    (fun reference _history _ current => refresh32InputsInto_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual quotient and row updates consume the actual refreshed Gram-derived inputs. -/
theorem secondPairPrefixInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (secondPairPrefixInto (model := model) refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := secondPairPrefixStep (model := model) refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (refreshInputsInto (model := model) refs)
    (divisionReductionInto (model := model) refs)
    (fun before =>
      let actual := refreshInputsStep (model := model) refs before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := divisionReductionStep (model := model) refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => refreshInputsInto_execute refs reference current)
    (fun reference _history _ current => divisionReductionInto_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairMachine
