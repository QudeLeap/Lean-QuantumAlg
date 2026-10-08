/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Local.Retained
import all QuantumAlg.Core.Execution.Local.Sequence

/-!
# Sequence law beside an existing retained cell

The cell stays resident across both original local instructions. Exposing the
two single-layer compilation laws avoids expanding a larger persistent frame.
-/

namespace QuantumAlg.Circuit

noncomputable section

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}

/-- An actual retained cell does not change the ordered local sequence. -/
theorem underRetained_seq (first second : Circuit model ctx ctx)
    (firstLocal : first.IsLocal) (secondLocal : second.IsLocal)
    (combined : (first.seq second).IsLocal)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    underRetained (first.seq second) combined key shape fresh =
      (underRetained first firstLocal key shape fresh).seq
        (underRetained second secondLocal key shape fresh) := by
  rfl

end

end QuantumAlg.Circuit
