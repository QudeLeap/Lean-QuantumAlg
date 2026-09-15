/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Local.Framing
import all QuantumAlg.Core.Execution.Measurement.Sequence

/-!
# Existing Z sequences belong to the local instruction fragment

Every instruction measures its actual wire into an already present cell.
Empty and repeated readout lists preserve the same runtime context; the
certificate follows the literal sequence syntax
[dW19, qcnotes.tex:5409,5420].
-/

namespace QuantumAlg.Circuit

/-- The existing ordered measurement sequence allocates or releases no live resource. -/
theorem measurementSequence_isLocal {ctx : RuntimeCtx .quantum}
    (readouts : List (ZReadout ctx)) : (measurementSequence readouts).IsLocal := by
  induction readouts with
  | nil => trivial
  | cons head tail ih => exact ⟨trivial, ih⟩

end QuantumAlg.Circuit
