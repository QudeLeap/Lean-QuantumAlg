/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Trace

/-!
# Classical-only actual circuit paths

The property is determined by the actual event trace on every interpreter path.
It excludes quantum gates, queries, preparation and measurement.
-/

namespace QuantumAlg.Circuit

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- A standalone classical section has no hidden quantum operation, query,
preparation, or measurement on any interpreter path. -/
public def IsClassical {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    {allowAllocation : Bool} (code : Circuit model pre post allowAllocation) : Prop :=
  ∀ (path : code.Path) (event : Resource.Event model),
    event ∈ code.eventTrace path →
      (∃ coordinate, event = .classicalOperation coordinate) ∨
      (∃ coordinate, event = .classicalQuery coordinate)

/-- An actual measurement cannot be hidden in a standalone classical section.
Its recorded outcome path always carries a quantum measurement event. -/
public lemma measureZ_notClassical {allowAllocation : Bool} {gates : GateModel}
  {oracles : OracleModel}
    {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
    {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension)) :
    ¬ IsClassical (Circuit.measureZ (allowAllocation := allowAllocation) (gates := gates)
      (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles) wire output) := by
  intro classical
  let dimension := (ctx.quantumLayout.wire wire).dimension
  let path : (Circuit.measureZ (allowAllocation := allowAllocation) (gates := gates)
    (oracles := oracles)
    (operations := operations) (classicalOracles := classicalOracles) wire output).Path :=
      ⟨0, dimension.pos⟩
  have present : (Resource.Event.measurement dimension :
      Resource.Event (.quantum gates oracles operations classicalOracles)) ∈
      (Circuit.measureZ (allowAllocation := allowAllocation) (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := classicalOracles) wire output).eventTrace
          path := by
    simp [Circuit.eventTrace, Circuit.zEvent, dimension]
  rcases classical path (.measurement dimension) present with
    ⟨_, impossible⟩ | ⟨_, impossible⟩
  · cases impossible
  · cases impossible

/-- The terminal range identity contains no event, so is strictly classical. -/
lemma identityClassical {model : ExecutionModel} {allowAllocation : Bool}
    (ctx : RuntimeCtx model.kind) :
    IsClassical (Circuit.id (model := model) (allowAllocation := allowAllocation) ctx) := by
  intro _ _ present
  exact False.elim (List.not_mem_nil present)

end

end QuantumAlg.Circuit
