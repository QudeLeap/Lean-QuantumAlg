/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Retained.Run
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Execution.Retained.Composition
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# Probability law of an actual retained continuation

An exact map of complete execution records carries the probability law derived
from their quantum blocks through the same map. The source, continuation, and
arbitrary reference remain part of the underlying interpreter equation.
-/

namespace QuantumAlg.AlgorithmRun

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {pre middle : RuntimeCtx model.kind}
  {key : StorageKey} {shape sourceShape resultShape : CShape} {fresh : key ∉ middle.keys}

/-- The actual retained record map pushes forward the normalized execution law. -/
lemma RetainedRecord.executionDistribution_eq_map
    (source : AlgorithmRun model pre middle sourceShape)
    (result : AlgorithmRun model pre (middle.addRetained key shape fresh) resultShape)
    (environment : model.Environment)
    (update : source.Record → result.Record)
    (mapped : RetainedRecord source result environment update)
    {Reference : Register}
    (input : OracleInput model.classicalOracles pre Reference) :
    result.executionDistribution environment input =
      (source.executionDistribution environment input).map update := by
  apply PMF.ext
  intro record
  change ENNReal.ofReal (((result.execute environment Reference input.state).block record).mass) = _
  rw [mapped Reference input.state]
  exact congrArg (fun distribution : PMF result.Record => distribution record)
    (ExecutionState.toPMF_mapClassical (source.execute environment Reference input.state)
      (source.execute_normalized environment input) update)

/-- Retention followed by an actual deterministic body keeps every initial store,
service transition, chronological path and quantum-reference block in its run record. -/
lemma execute_retained_eq_map
    (ctx : RuntimeCtx model.kind) (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (body : Circuit model (ctx.addRetained key shape fresh) (ctx.addRetained key shape fresh))
    (environment : model.Environment)
    (output : Output (ctx.addRetained key shape fresh) resultShape)
    (step : Store (ctx.addRetained key shape fresh) × model.HiddenState →
      (Store (ctx.addRetained key shape fresh) × model.HiddenState) × body.Path)
    (bodyEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (ctx.addRetained key shape fresh) Reference (model.HiddenState × History)),
      body.execute environment Reference state = state.mapClassical (fun entry =>
        let result := step (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (Reference : Register)
    (input : ExecutionState (Store ctx × model.HiddenState)
      (Register.prod ctx.register Reference)) :
    ({ code := .seq (.retain ctx key shape fresh) body, output := output } :
      AlgorithmRun model ctx (ctx.addRetained key shape fresh) resultShape).execute
        environment Reference input =
      input.mapClassical (D := Store (ctx.addRetained key shape fresh) ×
        (model.HiddenState × (Store ctx × (Unit × body.Path)))) (fun entry =>
          let result := step (entry.1.pushRetained key shape fresh, entry.2)
          (result.1.1, (result.1.2, (entry.1, ((), result.2))))) := by
  unfold execute
  refine (Circuit.execute_retain_seq_mapClassical (model := model) ctx key shape fresh
    body environment step bodyEquation Reference
    (input.mapClassical (fun entry => (entry.1, (entry.2, entry.1))))).trans ?_
  erw [ExecutionState.executionState_mapClassical_comp_instances
    (R := Register.prod ctx.register Reference) (result := inferInstance)]
  exact ExecutionState.executionState_mapClassical_congr input rfl

/-- The exact retained run record induces the joint law of the original store
and the value read from its actual final output, with arbitrary incoming reference. -/
lemma relationalDistribution_retained_eq_map
    (ctx : RuntimeCtx model.kind) (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (body : Circuit model (ctx.addRetained key shape fresh) (ctx.addRetained key shape fresh))
    (environment : model.Environment)
    (output : Output (ctx.addRetained key shape fresh) resultShape)
    (step : Store (ctx.addRetained key shape fresh) × model.HiddenState →
      (Store (ctx.addRetained key shape fresh) × model.HiddenState) × body.Path)
    (bodyEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (ctx.addRetained key shape fresh) Reference (model.HiddenState × History)),
      body.execute environment Reference state = state.mapClassical (fun entry =>
        let result := step (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    {Reference : Register} (input : OracleInput model.classicalOracles ctx Reference) :
    ({ code := .seq (.retain ctx key shape fresh) body, output := output } :
      AlgorithmRun model ctx (ctx.addRetained key shape fresh) resultShape).relationalDistribution
        environment input =
      (input.state.toPMF input.normalized).map (fun entry =>
        (entry.1, output.eval (step (entry.1.pushRetained key shape fresh, entry.2)).1.1)) := by
  let selected : AlgorithmRun model ctx (ctx.addRetained key shape fresh) resultShape :=
    { code := .seq (.retain ctx key shape fresh) body, output := output }
  let update : Store ctx × model.HiddenState → Store (ctx.addRetained key shape fresh) ×
      (model.HiddenState × (Store ctx × (Unit × body.Path))) := fun entry =>
    let result := step (entry.1.pushRetained key shape fresh, entry.2)
    (result.1.1, (result.1.2, (entry.1, ((), result.2))))
  have mapped : selected.executionDistribution environment input =
      (input.state.toPMF input.normalized).map update := by
    apply PMF.ext
    intro record
    change ENNReal.ofReal
      (((selected.execute environment Reference input.state).block record).mass) = _
    dsimp only [selected]
    rw [execute_retained_eq_map ctx key shape fresh body environment output step bodyEquation]
    exact congrArg (fun distribution : PMF (Store (ctx.addRetained key shape fresh) ×
      (model.HiddenState × (Store ctx × (Unit × body.Path)))) => distribution record)
      (ExecutionState.toPMF_mapClassical input.state input.normalized update)
  change selected.relationalDistribution environment input = _
  rw [relationalDistribution, mapped, PMF.map_comp]
  rfl

end

end QuantumAlg.AlgorithmRun
