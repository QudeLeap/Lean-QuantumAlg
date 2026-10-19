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
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Algorithm.Composition
import all QuantumAlg.Core.Algorithm.Problem.Embedding.Admission
import all QuantumAlg.Core.Algorithm.Composition.Embedding.Observation
import all QuantumAlg.Core.Algorithm.Composition.Embedding.Distribution
import all QuantumAlg.Core.Execution.Composition.Resources
import all QuantumAlg.Core.Execution.Circuit.Allocation

/-!
# Success and resource transfer for the original placed execution

Every guarantee is obtained from the child's complete contract on the same
unconditional input and supported path. Events and quantum time are unchanged;
the entire physical and classical frame remains resident and is charged by its
declared storage roles. The relational success event retains the original
local input store together with the actual output.
-/

namespace QuantumAlg.Algorithm

noncomputable section

variable {model : ExecutionModel} {localCtx caller : RuntimeCtx model.kind} {shape : CShape}
  {allowAllocation : Bool} (placement : ContextEmbedding localCtx caller)
  (child : Algorithm model localCtx localCtx shape false)
  (problem : Problem model localCtx localCtx shape)

/-- The same accepted relational event satisfies the child's original success lower bound. -/
public lemma algorithm_embed_success (correct : child.Solves problem)
    (environment : model.Environment) (witness : problem.Witness)
    {Reference : Register} (input : Execution.OracleInput model.classicalOracles caller Reference)
    (admitted : (problem.embed placement).Admits environment witness input) :
    ((problem.embed placement).successLB environment witness).value ≤
      ((embed (allowAllocation := allowAllocation) placement child).relationalDistribution
        environment input).toOuterMeasure
          {pair | (problem.embed placement).accepts environment witness pair.1 pair.2} := by
  have localAdmitted :=
    (Problem.problem_embed_admits_framed_iff placement problem
      environment witness input).mp admitted
  have success := correct.success environment witness (placement.frame.register.prod Reference)
    (placement.framedInput input) localAdmitted.1 localAdmitted.2
  simp only [Algorithm.relationalDistribution] at success ⊢
  rw [← embed_relationalDistribution_framed
    (allowAllocation := allowAllocation) placement child
    (environment := environment) input] at success
  simpa only [Problem.embed,
    PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq] using success

/-- Every supported placed path obeys all four independently supplied resource limits. -/
public lemma algorithm_embed_resource_bounds (correct : child.Solves problem)
    (environment : model.Environment) (witness : problem.Witness)
    {Reference : Register} (input : Execution.OracleInput model.classicalOracles caller Reference)
    (admitted : (problem.embed placement).Admits environment witness input)
    (path : child.run.code.Path)
    (supported : (embed (allowAllocation := allowAllocation) placement child).run.Supports
      environment Reference input.state path) :
    (embed (allowAllocation := allowAllocation) placement child).run.code.resourcePool path ≤
        (problem.embed placement).resources.events ∧
      (embed (allowAllocation := allowAllocation) placement child).run.code.peakResidentSpace
        path ≤ (problem.embed placement).resources.resident ∧
      (embed (allowAllocation := allowAllocation) placement child).run.code.peakAuxiliarySpace
        path ≤ (problem.embed placement).resources.auxiliary ∧
      (embed (allowAllocation := allowAllocation) placement child).quantumTime path ≤
        (problem.embed placement).quantumTimeLimit := by
  have localAdmitted :=
    (Problem.problem_embed_admits_framed_iff placement problem
      environment witness input).mp admitted
  have localSupported :=
    (embed_supports_framed_iff placement child (environment := environment) input path).mp supported
  have events := correct.events environment witness _ _
    localAdmitted.1 localAdmitted.2 path localSupported
  have resident := correct.resident environment witness _ _
    localAdmitted.1 localAdmitted.2 path localSupported
  have auxiliary := correct.auxiliary environment witness _ _
    localAdmitted.1 localAdmitted.2 path localSupported
  have time := correct.time environment witness _ _
    localAdmitted.1 localAdmitted.2 path localSupported
  refine ⟨events, ?_, ?_, time⟩
  · change Circuit.peakResidentSpace
      (Circuit.embed (allowAllocation := allowAllocation) placement child.run.code) path ≤
        problem.resources.resident + placement.frame.residentSpace
    rw [Circuit.peakResidentSpace_embed, placement.contextEmbedding_resident_space]
    rw [Circuit.fixed_peakResidentSpace] at resident
    exact fun axis => Nat.add_le_add_right (resident axis) _
  · change Circuit.peakAuxiliarySpace
      (Circuit.embed (allowAllocation := allowAllocation) placement child.run.code) path ≤
        problem.resources.auxiliary + placement.frame.auxiliarySpace
    rw [Circuit.peakAuxiliarySpace_embed, placement.contextEmbedding_auxiliary_space]
    rw [Circuit.fixed_peakAuxiliarySpace] at auxiliary
    exact fun axis => Nat.add_le_add_right (auxiliary axis) _

end

end QuantumAlg.Algorithm
