/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.State.Marginal
import all QuantumAlg.Core.Execution.State.Coordinates

/-!
# Classical observations while tracing an external reference factor

Reference projection retains the mass of each real classical record and
commutes with any finite record observation.
-/

namespace QuantumAlg.ExecutionState

noncomputable section

variable {C D : Type} [Fintype C] [Fintype D] {R Frame Reference : Register}

/-- The partial trace retains each original block probability. -/
lemma forgetReferenceFrame_block_mass
    (state : ExecutionState C (R.prod (Frame.prod Reference))) (value : C) :
    (state.forgetReferenceFrame.block value).mass = (state.block value).mass :=
  (executionState_marginalLeft_block_mass _ value).trans (reindex_block_mass _ _ value)

/-- Classical readout and an external partial trace sum the same complete blocks. -/
lemma forgetReferenceFrame_mapClassical [DecidableEq D]
    (state : ExecutionState C (R.prod (Frame.prod Reference))) (read : C → D) :
    (state.mapClassical read).forgetReferenceFrame =
      state.forgetReferenceFrame.mapClassical read := by
  unfold forgetReferenceFrame
  rw [← coordinate_reindex_mapClassical, executionState_marginalLeft_mapClassical]

end

end QuantumAlg.ExecutionState
