/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Algorithm.Composition
public import QuantumAlg.Core.Algorithm.Problem.Embedding.Admission
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Composition
import all QuantumAlg.Core.Algorithm.Problem.Embedding.Admission
import all QuantumAlg.Core.Algorithm.Composition.Embedding.Local
import all QuantumAlg.Core.Execution.State.Requirement.Embedding.Holds

/-!
# All state promises of the actual embedded child

The final local state is projected from the actual parent execution. The
original child contract therefore transports every independent state promise,
including a joint promise referring to the original external reference and
its original input. The same complete run supplies the input, output and
classical readout throughout.
-/

namespace QuantumAlg.Algorithm

noncomputable section

/-- The placed execution satisfies every transported original state requirement. -/
public lemma algorithm_embed_states
    {model : ExecutionModel} {localCtx caller : RuntimeCtx model.kind} {shape : CShape}
    {allowAllocation : Bool} (placement : ContextEmbedding localCtx caller)
    (child : Algorithm model localCtx localCtx shape false)
    (problem : Problem model localCtx localCtx shape) (correct : child.Solves problem)
    (environment : model.Environment) (witness : problem.Witness)
    {Reference : Register} (input : Execution.OracleInput model.classicalOracles caller Reference)
    (admitted : (problem.embed placement).Admits environment witness input)
    (requirement : StateRequirement caller caller)
    (present : requirement ∈ (problem.embed placement).states environment witness) :
    requirement.Holds input.caller
      ((embed (allowAllocation := allowAllocation) placement child).run.finalState
        environment Reference input.state) := by
  have localAdmitted :=
    (Problem.problem_embed_admits_local_iff placement problem environment witness input).mp admitted
  obtain ⟨original, originalPresent, same⟩ := List.mem_map.mp present
  subst requirement
  exact StateRequirement.stateRequirement_embed_holds_of_projection placement original input
    ((embed (allowAllocation := allowAllocation) placement child).run.finalState
      environment Reference input.state)
    (child.run.finalState environment Reference (placement.localInput input).state)
    (embed_finalState_local placement child (environment := environment) input)
    (correct.states environment witness Reference (placement.localInput input)
      localAdmitted.1 localAdmitted.2
      original originalPresent)

end

end QuantumAlg.Algorithm
