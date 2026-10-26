/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Scan.Coordinates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Exchange.Metadata

/-!
# Metadata retained by the complete coherent scan

The selected exchange preserves the phase-enable inputs and full address
inputs on every finite source label. These are the actual conditions needed
to clear both preparations after the payload, including inactive labels.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionScan

noncomputable section

open EncodedBit WindowLookup NumberTheory.SharedEEA

/-- The complete scan leaves the full natural metadata address unchanged. -/
lemma step_address (width : Nat) (state : Data width) :
    ScanMetadata.address (step width state).1.coefficientLength
      (step width state).1.quotientLength (step width state).1.flags.first =
      ScanMetadata.address state.1.coefficientLength state.1.quotientLength
        state.1.flags.first := by
  unfold step
  split
  · unfold action
    split
    · exact SelectionExchange.action_address width _ state
    · rfl
  · rfl

/-- The first phase bit is retained for actual inverse address preparation. -/
lemma step_phase1 (width : Nat) (state : Data width) :
    (step width state).1.flags.first = state.1.flags.first := by
  unfold step
  split
  · unfold action
    split
    · exact SelectionExchange.action_phase1 width _ state
    · rfl
  · rfl

/-- The second phase bit is retained for actual inverse enable preparation. -/
lemma step_phase2 (width : Nat) (state : Data width) :
    (step width state).1.flags.second = state.1.flags.second := by
  unfold step
  split
  · unfold action
    split
    · exact SelectionExchange.action_phase2 width _ state
    · rfl
  · rfl

/-- The original source control is itself outside every selected exchange. -/
lemma step_control (width : Nat) (state : Data width) :
    (step width state).1.control = state.1.control := by
  unfold step
  split
  · unfold action
    split
    · exact (SelectionExchange.action_preserves width _).2 ⟨0, by omega⟩ state
    · rfl
  · rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionScan
