/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Specification
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Selection.Schedule

/-! # Exact original corrected Sign-exchange position of the complete paid selection -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionSpecification

noncomputable section

open NumberTheory.SharedEEA

/-- Under the original prepared control, the complete finite source exchange is unchanged. -/
lemma sourceStep_eq_original (width : Nat) (state : Registers width)
    (clean : state.control = false) :
    sourceStep width state = SelectionSchedule.sourceStep width state := by
  unfold sourceStep SelectionSchedule.sourceStep
  rw [clean, Bool.false_xor]
  change (if state.flags.first ^^ state.flags.second then
    if within : ScanMetadata.position state.coefficientLength state.quotientLength
        state.flags.first < width + 3 then
      SelectionExchange.sourceAction width ⟨_, within⟩ state else state else state) =
    (if within : ScanMetadata.position state.coefficientLength state.quotientLength
        state.flags.first < width + 3 then
      if state.flags.first ^^ state.flags.second then
        SelectionSwap.exchange width ⟨_, within⟩ state else state else state)
  split_ifs <;> rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionSpecification
