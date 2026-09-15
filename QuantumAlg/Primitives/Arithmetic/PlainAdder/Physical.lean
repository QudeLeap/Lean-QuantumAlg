/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.Arithmetic.PlainAdder.Schedule

/-! # Physical footprint of the canonical plain-adder schedule -/

section

namespace QuantumAlg.PlainAdder.Schedule.PowerOfTwo

noncomputable section

/-- The canonical carry-work clean-carry/sum gate schedule stays in its carrier. -/
theorem carryWorkCleanCarrySumProgram_physical_idx_subset_range (n : Nat) :
    (carryWorkCleanCarrySumProgram n).physical_idx ⊆
      List.range (dataWithCarryWorkEncoding n).width := by
  unfold carryWorkCleanCarrySumProgram CarryWorkLayout.cleanCarrySumProgram
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range
    (CarryWorkLayout.cleanCarrySumGates (carryWorkLayout n))

end

end QuantumAlg.PlainAdder.Schedule.PowerOfTwo

end
