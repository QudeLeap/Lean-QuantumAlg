/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Scan
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Address.BitVec

/-! # Exact original address and complete restored pool of the scanned EEA exchange -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionScan

noncomputable section

open EncodedBit WindowLookup NumberTheory.SharedEEA

/-- The scan reads the entire original physical address word, without truncation or bit reversal. -/
lemma label_eq (width : Nat) (state : Data width) :
    label width state = state.2.1.toFin :=
  (SelectionFrame.frame width).addressLabelAt_bitVec state.2.1 state
    (fun index => SelectionFrame.address_get width index state)

private lemma exchange_pool (width : Nat) (index : Fin (width + 3)) (state : Data width) :
    (SelectionExchange.action width index state).2 = state.2 := by
  apply GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate present
  simp only [swapGates, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl
  · exact fun _ => rfl
  · exact fun _ => rfl
  · exact fun _ => rfl

/-- The selected payload retains the complete address, prefix word and conjunction bit. -/
lemma action_pool (width : Nat) (selected : Fin (2 ^ ScanMetadata.addressWidth width))
    (state : Data width) :
    (action width selected state).2 = state.2 := by
  unfold action
  split
  · exact exchange_pool width _ state
  · rfl

/-- Both inactive and active source controls restore the complete original pool. -/
lemma step_pool (width : Nat) (state : Data width) :
    (step width state).2 = state.2 := by
  unfold step
  split
  · exact action_pool width _ state
  · rfl

/-- Only the exact original unsigned address may select the exchanged Work1 position. -/
lemma step_eq (width : Nat) (state : Data width) :
    step width state = if state.1.control then
      if within : state.2.1.toNat < width + 3 then
        SelectionExchange.action width ⟨state.2.1.toNat, within⟩ state
      else state
    else state := by
  rw [step, label_eq]
  unfold action
  simp only [BitVec.val_toFin]
  split
  · split <;> rfl
  · rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionScan
