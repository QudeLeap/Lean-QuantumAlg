/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Local.Framing
import all QuantumAlg.Core.Execution.Context.Permutation.Local

/-!
# Single-layer sequence laws for local circuit transport

Framing and context permutation compile each original instruction in order.
Their sequence laws expose that structure without expanding a nested chain of
retained-cell transports.
-/

namespace QuantumAlg.Execution.ContextUnion

noncomputable section

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}

/-- Framing a local sequence preserves its two original instruction sections. -/
theorem frameLocal_seq (first second : Circuit model ctx ctx)
    (firstLocal : first.IsLocal) (secondLocal : second.IsLocal)
    (frame : RuntimeCtx model.kind)
    (separate : RuntimeCtx.StorageDisjoint ctx frame) :
    frameLocal (first.seq second) ⟨firstLocal, secondLocal⟩ frame separate =
      (frameLocal first firstLocal frame separate).seq
        (frameLocal second secondLocal frame separate) := by
  rfl

end

end QuantumAlg.Execution.ContextUnion

namespace QuantumAlg.Execution.ContextPermutation

noncomputable section

variable {model : ExecutionModel} {ctx target : RuntimeCtx model.kind}

/-- Permuting a local sequence preserves its two original instruction sections. -/
theorem localCircuit_seq (first second : Circuit model ctx ctx)
    (firstLocal : first.IsLocal) (secondLocal : second.IsLocal)
    (same : ctx.entries.Perm target.entries) :
    localCircuit (first.seq second) ⟨firstLocal, secondLocal⟩ target same =
      (localCircuit first firstLocal target same).seq
        (localCircuit second secondLocal target same) := by
  rfl

end

end QuantumAlg.Execution.ContextPermutation
