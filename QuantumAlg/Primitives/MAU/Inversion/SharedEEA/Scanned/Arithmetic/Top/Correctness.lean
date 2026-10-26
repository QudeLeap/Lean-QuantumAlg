/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Top

/-!
# Full-frame selected-top overflow semantics

The actual retained prefix selects the native top instruction at the
original full address. Every invalid address is inactive. All other
source coordinates, dirty Iter, the entire address and each prefix
remain on their original physical positions
[TTK09, qic-loglogaddition-quant.tex:285-318].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTop

noncomputable section

open EncodedBit WindowLookup StreamedSelector NumberTheory.SharedEEA

/-- The original native top source word acts on its full actual state. -/
def action (width : Nat) (kind : Kind)
    (label : Fin (2 ^ ScanMetadata.addressWidth width)) : Data width → Data width :=
  GateSpec.stepList (source width kind label.val)

private lemma callback_realizes (width : Nat) (kind : Kind)
    (label : Fin (2 ^ ScanMetadata.addressWidth width))
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (callback width kind label) environment
      (conditionalAction
        ((SelectionFrame.frame width).stack ⟨ScanMetadata.addressWidth width, by omega⟩)
        (action width kind label)) :=
  (payload width kind label).program_realizes (QubitLayout.canonical _) .empty environment

private lemma selected_action (width : Nat) (kind : Kind) (state : Data width) :
    (SelectionFrame.frame width).selectedActionAt (action width kind) (SelectionScan.tree width)
      0 (by omega) 0 (by omega) state = action width kind state.2.1.toFin state := by
  rw [SelectionScan.tree, SelectorFrame.selectedActionAt_prune]
  have label_eq : (SelectionFrame.frame width).addressLabelAt (ScanMetadata.addressWidth width)
      0 (by omega) 0 (by omega) state = state.2.1.toFin := SelectionScan.label_eq width state
  rw [label_eq]
  change (if decide (state.2.1.toFin.val < width + 3) then
    action width kind state.2.1.toFin state else state) = _
  by_cases within : state.2.1.toFin.val < width + 3
  · rw [decide_eq_true within, if_pos rfl]
  · simp only [decide_eq_false within, Bool.false_eq_true, if_false]
    rw [action, source, dif_neg within]
    rfl

/-- The actual source control enables the native top instruction at the unchanged full address. -/
def step (width : Nat) (kind : Kind) (state : Data width) : Data width :=
  if state.1.control then action width kind state.2.1.toFin state else state

/-- The real selected-top traversal has the exact coherent action on the complete original frame. -/
lemma program_apply_encoded_ket (width : Nat) (kind : Kind)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width)) :
    (program width kind).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (step width kind state))) := by
  have actual := SelectorFrame.program_apply_encoded_ket_clean (SelectionFrame.frame width)
    (QubitLayout.canonical _) .empty (callback width kind) (action width kind) environment
    (fun label => callback_realizes width kind label environment)
    (fun label => (payload width kind label).action_preserves)
    (fun label => (payload width kind label).action_independent)
    (SelectionScan.tree width) state (SelectionFrame.clean_of_prefix_zero width state clean)
  change (program width kind).applyNormalized environment _ = _ at actual
  have selected : conditionalAction ((SelectionFrame.frame width).stack ⟨0, by omega⟩)
      ((SelectionFrame.frame width).selectedActionAt (action width kind) (SelectionScan.tree width)
        0 (by omega) 0 (by omega)) state = step width kind state := by
    change (if state.1.control then
      (SelectionFrame.frame width).selectedActionAt (action width kind) (SelectionScan.tree width)
        0 (by omega) 0 (by omega) state else state) = _
    rw [selected_action]
    rfl
  rw [selected] at actual
  exact actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTop
