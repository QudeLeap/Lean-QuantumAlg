/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.State.Requirement
public import QuantumAlg.Core.Execution.State.Promise.Reindex
public import QuantumAlg.Core.Execution.Context.Embedding.Selection
public import QuantumAlg.Core.Execution.Context.Embedding.References
public import QuantumAlg.Core.Execution.Input.Embedding
public import QuantumAlg.Core.Execution.Input.Oracle.Projection

/-!
# Independent state requirements at physical placements

Both output selection and classical readout follow the declared wire and key
placement. Targets observe only the original local input and original external
reference. No child run or computed output appears in the specification
[dW19, qcnotes.tex:5381,6827].
-/

namespace QuantumAlg.StateRequirement

noncomputable section

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}

/-- Place an independent local promise on the same selected physical systems. -/
public def embed (placement : ContextEmbedding localCtx caller) :
    StateRequirement localCtx localCtx → StateRequirement caller caller
  | .marginal selection read target =>
      .marginal (placement.selection selection) (placement.outputRead read)
        (fun input value =>
          (target (placement.projectLocal input (fun store => (placement.store store).1))
            value).reindex (placement.selectedBasis selection))
  | .jointReference selection read target =>
      .jointReference (placement.selection selection) (placement.outputRead read)
        (fun Reference input value =>
          (target Reference (placement.projectInput input) value).reindex
            ((placement.selectedBasis selection).prodCongr (Equiv.refl Reference.Index)))

end

end QuantumAlg.StateRequirement
