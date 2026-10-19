/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Core.Execution.State.Requirement.Embedding

/-!
# Independent problems for placed executions

The placement transports the original problem's domain, service initialization,
relational result and state promises. The entire complement contributes to both
resident and auxiliary storage according to its declared roles. The original
event and quantum-time limits stay attached to the child contract. No candidate
execution or accounting witness is used to define these limits.
-/

namespace QuantumAlg.Problem

noncomputable section

variable {model : ExecutionModel} {localCtx caller : RuntimeCtx model.kind} {shape : CShape}

/-- Place every original contract field on the actual caller and charge its full complement. -/
@[expose] public def embed (placement : ContextEmbedding localCtx caller)
    (problem : Problem model localCtx localCtx shape) : Problem model caller caller shape where
  Witness := problem.Witness
  valid := fun environment witness state =>
    problem.valid environment witness
      (placement.projectLocal state (fun store => (placement.store store).1))
  initialization := fun environment witness state =>
    problem.initialization environment witness
      (placement.projectLocal state (fun label => ((placement.store label.1).1, label.2)))
  accepts := fun environment witness original result =>
    problem.accepts environment witness (placement.store original).1 result
  successLB := problem.successLB
  states := fun environment witness =>
    (problem.states environment witness).map (StateRequirement.embed placement)
  resources :=
    { events := problem.resources.events
      resident := problem.resources.resident + placement.frame.residentSpace
      auxiliary := problem.resources.auxiliary + placement.frame.auxiliarySpace }
  quantumTimeLimit := problem.quantumTimeLimit

end

end QuantumAlg.Problem
