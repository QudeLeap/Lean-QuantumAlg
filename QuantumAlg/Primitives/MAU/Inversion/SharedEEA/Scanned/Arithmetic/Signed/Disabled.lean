/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Signed.Prefix

/-! # Disabled actual signed traversals on the entire original finite address domain -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticSigned

noncomputable section

open EncodedBit WindowLookup StreamedSelector NumberTheory.SharedEEA ArithmeticTemplate

private lemma fold_disabled (width : Nat) (kind : ArithmeticTop.Kind)
    {remaining : Nat} (tree : SelectorTrie remaining) (depth : Nat)
    (fits : depth + remaining = ScanMetadata.addressWidth width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ ScanMetadata.addressWidth width)
    (state : Data width) (zero : state.2.2.2 = false) :
    foldAt (SelectionFrame.frame width) (fun label => callbackStep width kind label.val)
      tree depth fits offset bounded false state = state := by
  induction tree generalizing depth offset with
  | skip remaining => rfl
  | leaf =>
      change (if state.2.2.2 then GateSpec.stepList
        (source width (stage kind) offset) state else state) = state
      rw [zero]
      rfl
  | @fork remaining left right leftIH rightIH =>
      simp only [foldAt, Bool.false_and]
      rw [leftIH (depth + 1) (by omega) offset (SelectorFrame.left_bound bounded)]
      exact rightIH (depth + 1) (by omega) (offset + 2 ^ remaining)
        (SelectorFrame.right_bound bounded)

/-- Rejected keys can have any finite address; the actual native program still restores its pool. -/
lemma program_apply_disabled (width : Nat) (kind : ArithmeticTop.Kind)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (disabled : state.1.control = false) :
    (program width kind).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state)) := by
  have actual := program_apply_encoded_ket_streamed_clean (SelectionFrame.frame width)
    (QubitLayout.canonical _) .empty (callback width kind)
    (fun label => callbackStep width kind label.val) environment
    (fun label => callback_realizes width kind label environment)
    (callbackStep_preserves width kind) (callbackStep_independent width kind)
    (ArithmeticTemplate.tree width) state (SelectionFrame.clean_of_prefix_zero width state clean)
  have root : ((SelectionFrame.frame width).stack ⟨0, by omega⟩).get state = false := disabled
  rw [root, fold_disabled width kind _ _ _ _ _ state zero] at actual
  exact actual

/-- The paid control copy and fused traversal are both inactive without an address-range premise. -/
lemma forwardProgram_apply_disabled (width : Nat) (kind : ArithmeticTop.Kind)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (disabled : state.1.control = false) :
    (forwardProgram width kind).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state)) := by
  have prepare := (GateSpec.realizes (QubitLayout.canonical _) .empty
    (startGate width) environment).apply_encoded_ket state
  have same : (startGate width).step state = state := by
    change (if state.1.control then (conjunctionBit width).flip state else state) = state
    rw [disabled]
    rfl
  rw [same] at prepare
  exact UnitaryCircuit.applyNormalized_seq_of_eq prepare
    (program_apply_disabled width kind environment state clean zero disabled)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticSigned
