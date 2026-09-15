/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Cells.Framing.State
import all QuantumAlg.Core.Execution.Context.Union.Basis

/-!
# Framed cell allocation retains the original joint basis coordinates

Each real retain changes only classical storage. The original quantum basis
and the supplied resident frame therefore keep their joint per-wire assembly
through any number of allocated result cells.
-/

namespace QuantumAlg.Execution.MeasurementCells

noncomputable section

open ContextUnion

/-- Retaining the original cells leaves both physical quantum segments exactly where they were. -/
theorem framedBasisEquiv_join {kind : ProblemKind} (ctx frame : RuntimeCtx kind)
    (dimension : ℕ+) (count : Nat)
    (separate : RuntimeCtx.StorageDisjoint (context ctx dimension count) frame)
    (original : ctx.register.Index) (resident : frame.register.Index) :
    framedBasisEquiv ctx frame dimension count separate
      ((unionBasisEquiv ctx frame (original_disjoint ctx frame dimension count separate)).symm
        (original, resident)) =
      (unionBasisEquiv (context ctx dimension count) frame separate).symm
        (basisEquiv ctx dimension count original, resident) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      exact ih (retained_disjoint (context ctx dimension count).canonicalFreshKey
        (.finite dimension) (context ctx dimension count).canonicalFreshKey_fresh separate)

end

end QuantumAlg.Execution.MeasurementCells
