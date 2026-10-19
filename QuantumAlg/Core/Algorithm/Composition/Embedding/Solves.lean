/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Composition.Embedding.Bounds
public import QuantumAlg.Core.Algorithm.Composition.Embedding.States
public import QuantumAlg.Core.Algorithm.Composition.Embedding.Borrowed
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Problem

/-!
# Complete correctness of an original algorithm at its physical placement

The same embedded execution supplies success, every original state promise,
full borrowed-resource restoration and all four resource bounds. The frame
remains physically present and contributes its declared space. Admission uses
the original unconditional local input, including its service correlations.
-/

namespace QuantumAlg.Algorithm

noncomputable section

/-- Physical embedding transports the complete original algorithm contract. -/
public lemma algorithm_embed_solves
    {model : ExecutionModel} {localCtx caller : RuntimeCtx model.kind} {shape : CShape}
    {allowAllocation : Bool} (placement : ContextEmbedding localCtx caller)
    (child : Algorithm model localCtx localCtx shape false)
    (problem : Problem model localCtx localCtx shape) (correct : child.Solves problem) :
    (embed (allowAllocation := allowAllocation) placement child).Solves
      (problem.embed placement) where
  success environment witness _Reference input valid initialized :=
    algorithm_embed_success placement child problem correct environment witness input
      ⟨valid, initialized⟩
  states environment witness _Reference input valid initialized requirement present :=
    algorithm_embed_states placement child problem correct environment witness input
      ⟨valid, initialized⟩
      requirement present
  borrowed environment witness _Reference input valid initialized :=
    algorithm_embed_borrowed placement child problem correct environment witness input
      ⟨valid, initialized⟩
  events environment witness _Reference input valid initialized path supported :=
    (algorithm_embed_resource_bounds placement child problem correct environment witness input
      ⟨valid, initialized⟩ path supported).1
  resident environment witness _Reference input valid initialized path supported :=
    (algorithm_embed_resource_bounds placement child problem correct environment witness input
      ⟨valid, initialized⟩ path supported).2.1
  auxiliary environment witness _Reference input valid initialized path supported :=
    (algorithm_embed_resource_bounds placement child problem correct environment witness input
      ⟨valid, initialized⟩ path supported).2.2.1
  time environment witness _Reference input valid initialized path supported :=
    (algorithm_embed_resource_bounds placement child problem correct environment witness input
      ⟨valid, initialized⟩ path supported).2.2.2

end

end QuantumAlg.Algorithm
