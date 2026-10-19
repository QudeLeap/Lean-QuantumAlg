/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Fibers

/-!
# Actual sequence and result-retention laws for reference observations

History reassociation leaves every store-weighted reference entry unchanged.
Retaining one real result transports a weight through the actual store push,
and every lifted earlier input reads its unchanged value. These are laws of
the existing interpreter used to compose actual finite reference observations.
-/

namespace QuantumAlg.Circuit

variable {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Real sequential execution changes only history parentheses after the two actual bodies. -/
lemma referenceFiberSum_execute_seq {allowAllocation : Bool}
    {pre middle post : RuntimeCtx .quantum}
    (first : Circuit (.quantum gates oracles operations classicalOracles) pre middle
        allowAllocation)
    (second : Circuit (.quantum gates oracles operations classicalOracles) middle post
        allowAllocation)
    (environment : (ExecutionModel.quantum gates oracles operations classicalOracles).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State pre Reference (classicalOracles.HiddenState × History)) (weight : Store post → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((Circuit.seq first second).execute environment Reference state)
        (fun entry _ => weight entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum
        (second.execute environment Reference (first.execute environment Reference state))
        (fun entry _ => weight entry.1) leftRef rightRef := by
  have executed := congrArg
    (fun output : State post Reference
        (classicalOracles.HiddenState × (History × (Circuit.seq first second).Path)) =>
      ExecutionState.referenceFiberSum output (fun entry _ => weight entry.1) leftRef rightRef)
    (Circuit.execute_seq (allowAllocation := allowAllocation)
      (environment := environment) first second state)
  refine executed.trans ?_
  simp only [State.mapHistory, ExecutionState.referenceFiberSum_mapClassical]

/-- The actual retain transports the weight through its real context-indexed store update. -/
lemma referenceFiberSum_execute_retain {ctx : RuntimeCtx .quantum}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (environment : (ExecutionModel.quantum gates oracles operations classicalOracles).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (classicalOracles.HiddenState × History))
    (weight : Store (ctx.addRetained key shape fresh) → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((Circuit.retain (model := .quantum gates oracles operations classicalOracles)
          ctx key shape fresh).execute
          environment Reference state)
        (fun entry _ => weight entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (entry.1.pushRetained key shape fresh)) leftRef rightRef := by
  have executed := congrArg
    (fun output : State (ctx.addRetained key shape fresh) Reference
        (classicalOracles.HiddenState × (History × Unit)) =>
      ExecutionState.referenceFiberSum output (fun entry _ => weight entry.1) leftRef rightRef)
    (Circuit.execute_retain (model := .quantum gates oracles operations classicalOracles)
      (environment := environment)
      state key shape fresh)
  exact executed.trans (ExecutionState.referenceFiberSum_mapClassical state
    (fun entry => (entry.1.pushRetained key shape fresh, (entry.2.1, (entry.2.2, ()))))
    (fun entry _ => weight entry.1) leftRef rightRef)

/-- A weight on any lifted earlier operand is unchanged by retaining the real next result. -/
lemma referenceFiberSum_execute_retain_input {ctx : RuntimeCtx .quantum}
    {inputShape : CShape} (input : CInputRef ctx inputShape)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (environment : (ExecutionModel.quantum gates oracles operations classicalOracles).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (classicalOracles.HiddenState × History))
    (weight : inputShape.Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((Circuit.retain (model := .quantum gates oracles operations classicalOracles)
          ctx key shape fresh).execute
          environment Reference state)
        (fun entry _ => weight (entry.1.read (input.underRetained key shape fresh)))
        leftRef rightRef =
      ExecutionState.referenceFiberSum state (fun entry _ => weight (entry.1.read input))
        leftRef rightRef := by
  refine (referenceFiberSum_execute_retain (gates := gates) (oracles := oracles)
    (operations := operations) (classicalOracles := classicalOracles)
    key shape fresh environment state
    (fun store => weight (store.read (input.underRetained key shape fresh)))
    leftRef rightRef).trans ?_
  exact congrArg
    (fun observe : (Store ctx × (classicalOracles.HiddenState × History)) →
        ctx.register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observe leftRef rightRef)
    (funext fun entry => funext fun _ => congrArg weight
      (Store.read_pushRetained_underRetained entry.1 key shape fresh input))

end

end QuantumAlg.Circuit
