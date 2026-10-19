/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Reference.Preservation
import all QuantumAlg.Core.Execution.Composition.Embedding
import all QuantumAlg.Core.Execution.Composition.Parallel
import all QuantumAlg.Core.Execution.Interpret.Preserving

/-!
# Reference preservation through actual physical and service composition

Embedding preserves the entire frame as part of the child's reference before
tracing the frame at the caller boundary. Service reorganization only changes
finite classical coordinates. Consequently sequential interpretation of the
two physically disjoint children cannot change the original reference state
[dW19, qcnotes.tex:389,5381,6827].
-/

namespace QuantumAlg.Execution

noncomputable section

attribute [local instance] Classical.decEq

/-- The unconditioned recursive result preserves the whole external-reference density operator. -/
abbrev ReferencePreserving {kind : ProblemKind} {pre post : RuntimeCtx kind}
    {Reference : Register} {Hidden Path : Type} [Fintype Hidden] [Fintype Path]
    (body : Preserving Hidden pre post Reference Path) : Prop :=
  ∀ {H : Type} [Fintype H] (state : State pre Reference (Hidden × H)),
    (body state).val.referenceMarginal = state.referenceMarginal

/-- Physical embedding preserves the old reference by retaining and then tracing the full frame. -/
lemma embedPreserving_referenceMarginal {kind : ProblemKind}
    {localCtx caller : RuntimeCtx kind} (placement : ContextEmbedding localCtx caller)
    (Reference : Register) {Hidden Path : Type} [Fintype Hidden] [Fintype Path]
    (body : Preserving Hidden localCtx localCtx (placement.frame.register.prod Reference) Path)
    (preserves : ReferencePreserving body) :
    ReferencePreserving (embedPreserving placement Reference body) := by
  intro H _ state
  apply DensityOperator.ext
  ext row column
  dsimp only [embedPreserving]
  rw [placement.contextEmbedding_join_referenceMarginal_entry]
  simp only [State.mapHistory_referenceMarginal, preserves]
  have complete := placement.contextEmbedding_join_referenceMarginal_entry
    (placement.split state) row column
  rw [placement.contextEmbedding_join_split] at complete
  exact complete.symm

variable {left right parent : ClassicalOracleModel}
  (join : ClassicalOracleModel.ServiceJoin left right parent)
  {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
  {Path : Type} [Fintype Path]

/-- Activating the left service changes no part of the external-reference observation. -/
lemma serviceLeftPreserving_referenceMarginal
    (body : Preserving left.HiddenState ctx ctx Reference Path)
    (preserves : ReferencePreserving body) :
    ReferencePreserving (serviceLeftPreserving join body) := by
  intro H _ state
  dsimp only [serviceLeftPreserving, serviceOutputLeft]
  rw [ExecutionState.mapClassical_referenceMarginal, preserves]
  exact ExecutionState.mapClassical_referenceMarginal state _

/-- Activating the right service likewise retains every old-reference coherence. -/
lemma serviceRightPreserving_referenceMarginal
    (body : Preserving right.HiddenState ctx ctx Reference Path)
    (preserves : ReferencePreserving body) :
    ReferencePreserving (serviceRightPreserving join body) := by
  intro H _ state
  dsimp only [serviceRightPreserving, serviceOutputRight]
  rw [ExecutionState.mapClassical_referenceMarginal, preserves]
  exact ExecutionState.mapClassical_referenceMarginal state _

/-- Both actual child executions preserve the original reference on arbitrary correlated inputs. -/
lemma parallelPreserving_referenceMarginal {leftCtx rightCtx : RuntimeCtx kind}
    (separate : RuntimeCtx.StorageDisjoint leftCtx rightCtx)
    {LeftPath RightPath : Type} [Fintype LeftPath] [Fintype RightPath]
    (first : Preserving left.HiddenState leftCtx leftCtx
      (rightCtx.register.prod Reference) LeftPath)
    (second : Preserving right.HiddenState rightCtx rightCtx
      (leftCtx.register.prod Reference) RightPath)
    (firstPreserves : ReferencePreserving first)
    (secondPreserves : ReferencePreserving second) :
    ReferencePreserving (parallelPreserving join separate first second) := by
  have firstComplete : ReferencePreserving
      (serviceLeftPreserving join
        (embedPreserving (ContextEmbedding.alongUnion leftCtx rightCtx separate)
          Reference first)) :=
    serviceLeftPreserving_referenceMarginal join _
      (embedPreserving_referenceMarginal
        (ContextEmbedding.alongUnion leftCtx rightCtx separate) Reference first firstPreserves)
  have secondComplete : ReferencePreserving
      (serviceRightPreserving join
        (embedPreserving
          (ContextEmbedding.alongUnionRight leftCtx rightCtx separate) Reference second)) :=
    serviceRightPreserving_referenceMarginal join _
      (embedPreserving_referenceMarginal
        (ContextEmbedding.alongUnionRight leftCtx rightCtx separate)
          Reference second secondPreserves)
  intro H _ state
  dsimp only [parallelPreserving, embedServiceLeftPreserving, embedServiceRightPreserving]
  rw [ExecutionState.mapClassical_referenceMarginal, secondComplete, firstComplete]

end

end QuantumAlg.Execution
