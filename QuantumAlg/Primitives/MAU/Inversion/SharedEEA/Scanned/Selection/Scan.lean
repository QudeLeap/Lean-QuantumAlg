/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Exchange

/-!
# Actual pruned full-address EEA exchange

Only full-width labels that designate original Work1 coordinates retain a
leaf program. Every such program uses the actual one-Toffoli Fredkin. The
unitary traversal returns all clean prefixes and preserves all address bits;
all inactive source controls and out-of-range labels act as identity.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionScan

noncomputable section

open EncodedBit WindowLookup NumberTheory.SharedEEA

/-- Presence is decided from the full static label, including the high carry bit. -/
def active (width : Nat) (label : Fin (2 ^ ScanMetadata.addressWidth width)) : Bool :=
  decide (label.val < width + 3)

/-- Every physically meaningful Work1 position retains exactly its full-address leaf. -/
def tree (width : Nat) : SelectorTrie (ScanMetadata.addressWidth width) :=
  SelectorTrie.prune (ScanMetadata.addressWidth width) (active width)

/-- A full-address payload exchanges the selected coordinate or leaves all data unchanged. -/
def action (width : Nat) (label : Fin (2 ^ ScanMetadata.addressWidth width)) :
    Data width → Data width :=
  if within : label.val < width + 3 then SelectionExchange.action width ⟨label.val, within⟩
  else id

/-- Retained native leaves use the existing final prefix and no extra controls or systems. -/
def callback (width : Nat) (label : Fin (2 ^ ScanMetadata.addressWidth width)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  if within : label.val < width + 3 then SelectionExchange.program width ⟨label.val, within⟩
  else .identity _ _ _

private lemma final_control (width : Nat) :
    SelectionExchange.control width =
      (SelectionFrame.frame width).stack ⟨ScanMetadata.addressWidth width, by omega⟩ := by
  change SelectionExchange.control width =
    SelectionFrame.stack width ⟨ScanMetadata.addressWidth width, by omega⟩
  unfold SelectionFrame.stack
  have nonzero : ScanMetadata.addressWidth width ≠ 0 := by
    unfold ScanMetadata.addressWidth
    omega
  rw [dif_neg nonzero]
  rfl

private lemma callback_realizes (width : Nat)
    (label : Fin (2 ^ ScanMetadata.addressWidth width))
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (callback width label) environment
      (conditionalAction
        ((SelectionFrame.frame width).stack ⟨ScanMetadata.addressWidth width, by omega⟩)
        (action width label)) := by
  unfold callback action
  split
  · simpa only [final_control] using SelectionExchange.program_realizes width _ environment
  · apply (UnitaryCircuit.Realizes.identity AlgorithmGate.model .empty
      (encoding width) environment).congrStep
    intro state
    unfold conditionalAction
    split <;> rfl

private lemma action_preserves (width : Nat)
    (label : Fin (2 ^ ScanMetadata.addressWidth width)) :
    (SelectionFrame.frame width).Preserves (action width label) := by
  unfold action
  split
  · exact SelectionExchange.action_preserves width _
  · exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

private lemma action_independent (width : Nat)
    (label : Fin (2 ^ ScanMetadata.addressWidth width)) :
    (SelectionFrame.frame width).IndependentPrefixes (action width label) := by
  unfold action
  split
  · exact SelectionExchange.action_independent width _
  · exact fun _ _ => rfl

/-- The original complete address is decoded with every most-significant-first bit retained. -/
def label (width : Nat) (state : Data width) : Fin (2 ^ ScanMetadata.addressWidth width) :=
  (SelectionFrame.frame width).addressLabelAt (ScanMetadata.addressWidth width)
    0 (by omega) 0 (by omega) state

private lemma selected_action (width : Nat) (state : Data width) :
    (SelectionFrame.frame width).selectedActionAt (action width) (tree width)
      0 (by omega) 0 (by omega) state = action width (label width state) state := by
  rw [tree, SelectorFrame.selectedActionAt_prune]
  change (if decide ((label width state).val < width + 3) = true then
    action width (label width state) state else state) = _
  by_cases within : (label width state).val < width + 3
  · simp only [within, decide_true, if_true]
  · simp only [within, decide_false, Bool.false_eq_true, if_false]
    rw [action, dif_neg within]
    rfl

/-- The actual unitary traversal uses the original full source-plus-pool frame. -/
def program (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum :=
  (SelectionFrame.frame width).program (QubitLayout.canonical _) .empty
    (callback width) (tree width)

/-- Complete conditional action, retaining all other source and workspace coordinates. -/
def step (width : Nat) (state : Data width) : Data width :=
  if state.1.control then action width (label width state) state else state

/-- Every clean-prefix input has the exact coherent full-address conditional exchange. -/
lemma program_apply_encoded_ket (width : Nat) (environment : OracleModel.empty.Interpretation)
    (state : Data width) (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width)) :
    (program width).applyNormalized environment
      (NormalizedVector.ket
        ((QubitLayout.canonical _).basisEquiv.symm ((encoding width).encode state))) =
      NormalizedVector.ket
        ((QubitLayout.canonical _).basisEquiv.symm
          ((encoding width).encode (step width state))) := by
  rw [program, SelectorFrame.program_apply_encoded_ket_clean _ _ _ _ _ environment
    (fun label => callback_realizes width label environment) (action_preserves width)
    (action_independent width) (tree width) state (SelectionFrame.clean_of_prefix_zero _ _ clean)]
  rw [show conditionalAction ((SelectionFrame.frame width).stack ⟨0, by omega⟩)
      ((SelectionFrame.frame width).selectedActionAt (action width) (tree width)
        0 (by omega) 0 (by omega)) state = step width state by
    change (if state.1.control then _ else state) = _
    rw [selected_action]
    rfl]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionScan
