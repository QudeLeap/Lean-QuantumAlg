/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Context.Embedding.Selection.Observation
public import QuantumAlg.Core.Execution.Observe.Reference
import all QuantumAlg.Core.Execution.Context.Embedding.Selection.Observation
import all QuantumAlg.Core.Execution.Observe.Reference

/-!
# Local selected states with the original external reference

Physical placement and selected-state observation commute with projecting
away the complete complement. The retained reference is the original caller
reference, with all of its off-diagonal correlations intact
[dW19, qcnotes.tex:5381,6827].
-/

namespace QuantumAlg.ContextEmbedding

noncomputable section

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller)

/-- The selected joint state is exactly that of the unconditional local projection. -/
lemma contextEmbedding_observeSelectionWithReference_project
    (selected : Finset (Fin localCtx.systemCount)) (Reference : Register)
    (state : DensityOperator (caller.register.prod Reference)) :
    (DensityOperator.observeSelectionWithReference caller.quantumLayout
      (placement.selection selected) Reference state).reindex
        (S := (localCtx.quantumLayout.selectedRegister selected).prod Reference)
        ((placement.selectedBasis selected).symm.prodCongr (Equiv.refl Reference.Index)) =
    DensityOperator.observeSelectionWithReference localCtx.quantumLayout selected Reference
      (((state.reindex (S := localCtx.register.prod (placement.frame.register.prod Reference))
        (placement.referenceBasis Reference)).reindex
          (S := (localCtx.register.prod Reference).prod placement.frame.register)
          ExecutionState.referenceFrameBasis).marginalLeft) :=
  (placement.contextEmbedding_observeSelectionWithReference selected Reference state).trans
    (DensityOperator.observeSelectionWithReference_forgetReferenceFrame
      localCtx.quantumLayout selected placement.frame.register Reference _).symm

/-- The selected marginal follows by tracing only the same original external reference. -/
lemma contextEmbedding_observeSelection_project
    (selected : Finset (Fin localCtx.systemCount)) (Reference : Register)
    (state : DensityOperator (caller.register.prod Reference)) :
    (DensityOperator.observeSelection caller.quantumLayout
      (placement.selection selected) Reference state).reindex
        (placement.selectedBasis selected).symm =
    DensityOperator.observeSelection localCtx.quantumLayout selected Reference
      (((state.reindex (S := localCtx.register.prod (placement.frame.register.prod Reference))
        (placement.referenceBasis Reference)).reindex
          (S := (localCtx.register.prod Reference).prod placement.frame.register)
          ExecutionState.referenceFrameBasis).marginalLeft) := by
  have joint := congrArg DensityOperator.marginalLeft
    (placement.contextEmbedding_observeSelectionWithReference_project
      selected Reference state)
  rw [DensityOperator.marginalLeft_reindex_local] at joint
  exact joint

end

end QuantumAlg.ContextEmbedding
