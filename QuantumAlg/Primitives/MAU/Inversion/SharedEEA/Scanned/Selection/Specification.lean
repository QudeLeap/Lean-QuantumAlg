/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Exchange.Enable

/-!
# Independent full-label source action of the scanned EEA selection

The original control is XORed with the two original phase bits. When it
selects an exchange, the complete natural length sum and phase offset
identify the original Work1 coordinate; every out-of-range position is
inactive. The input control, phase bits and length words are retained.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionSpecification

noncomputable section

open NumberTheory.SharedEEA

/-- Direct source action, independent of the address-preparation or scan program. -/
def sourceStep (width : Nat) (state : Registers width) : Registers width :=
  if state.control ^^ (state.flags.first ^^ state.flags.second) then
    if within : ScanMetadata.position state.coefficientLength state.quotientLength
        state.flags.first < width + 3 then
      SelectionExchange.sourceAction width
        ⟨ScanMetadata.position state.coefficientLength state.quotientLength state.flags.first,
          within⟩ state
    else state
  else state

/-- An already prepared source control selects from the same full natural metadata position. -/
def selectedSource (width : Nat) (state : Registers width) : Registers width :=
  if state.control then
    if within : ScanMetadata.position state.coefficientLength state.quotientLength
        state.flags.first < width + 3 then
      SelectionExchange.sourceAction width
        ⟨ScanMetadata.position state.coefficientLength state.quotientLength state.flags.first,
          within⟩ state
    else state
  else state

private lemma enable_twice (width : Nat) (state : Registers width) :
    SelectionEnable.sourceStep width (SelectionEnable.sourceStep width state) = state :=
  NativePredicate.xorControl_twice (state.flags.first ^^ state.flags.second) state

/-- The preserved phase-enable calculation cancels on every active and inactive source label. -/
lemma enable_selected_enable (width : Nat) (state : Registers width) :
    SelectionEnable.sourceStep width
      (selectedSource width (SelectionEnable.sourceStep width state)) =
        sourceStep width state := by
  unfold selectedSource sourceStep
  change SelectionEnable.sourceStep width
    (if state.control ^^ (state.flags.first ^^ state.flags.second) then
      if within : ScanMetadata.position state.coefficientLength state.quotientLength
          state.flags.first < width + 3 then
        SelectionExchange.sourceAction width
          ⟨ScanMetadata.position state.coefficientLength state.quotientLength state.flags.first,
            within⟩ (SelectionEnable.sourceStep width state)
      else SelectionEnable.sourceStep width state
    else SelectionEnable.sourceStep width state) = _
  split_ifs
  · rw [SelectionExchange.sourceAction_enable, enable_twice]
  · exact enable_twice width state
  · exact enable_twice width state

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionSpecification
