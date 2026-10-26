/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Flag
import all QuantumAlg.Components.Encoded.BitGates.StreamedSelector.Prefix
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Address.BitVec

/-!
# Exact finite-prefix execution of the native TTK stream

The moving flag selects an ordered prefix of the original per-index source
word and returns to zero at its real boundary. Address and prefix systems
are the original shared pool, and all source/reference coordinates remain
inside the complete label used by the actual circuit.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTemplate

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Native callback composition retains the exact moving-flag recurrence and original order. -/
lemma callback_fold (width : Nat) (stage : Stage) (indices : List Nat)
    (enabled : Bool) (last : Nat) (state : Data width) :
    flagEquiv width (indices.foldl (fun value index =>
      (payload width stage index).callbackStep (enabled && decide (index = last)) value) state) =
      indices.foldl (ThresholdStream.forwardStep (baseAction width stage) enabled last)
        (flagEquiv width state) := by
  symm
  apply List.foldl_hom (flagEquiv width)
  intro value index
  exact (callback_threshold width stage index enabled last value).symm

/-- Every in-range boundary clears the physical moving flag after the exact selected prefix. -/
lemma callback_range_complete (width : Nat) (stage : Stage) (count : Nat)
    (enabled : Bool) (last : Nat) (state : Data width)
    (initial : state.2.2.2 = enabled) (within : last < count) :
    flagEquiv width ((List.range count).foldl (fun value index =>
      (payload width stage index).callbackStep (enabled && decide (index = last)) value) state) =
      (if enabled then
        ThresholdStream.word (baseAction width stage) (last + 1) (flagEquiv width state).1
        else (flagEquiv width state).1, false) := by
  rw [callback_fold]
  have start : flagEquiv width state = ((flagEquiv width state).1, enabled) := by
    apply Prod.ext
    · rfl
    · exact initial
  rw [start, ThresholdStream.forward_complete _ _ _ _ _ within]

private lemma address_label (width : Nat) (state : Data width) :
    (SelectionFrame.frame width).addressLabelAt (ScanMetadata.addressWidth width)
      0 (by omega) 0 (by omega) state = state.2.1.toFin :=
  (SelectionFrame.frame width).addressLabelAt_bitVec state.2.1 state
    (fun index => SelectionFrame.address_get width index state)

/-- The literal native tree realizes the selected source prefix and clears its moving flag. -/
lemma program_apply_prefix (width : Nat) (positive : 1 ≤ width) (stage : Stage)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (initial : state.2.2.2 = state.1.control) (within : state.2.1.toNat < width + 3) :
    (program width stage).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode ((flagEquiv width).symm
          (if state.1.control then
            ThresholdStream.word (baseAction width stage) (state.2.1.toNat + 1)
              (flagEquiv width state).1
            else (flagEquiv width state).1, false)))) := by
  have capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width := by
    have last := ScanMetadata.targetIndex_lt width positive
      (⟨width + 2, by omega⟩ : Fin (width + 3))
    change width + 2 < _ at last
    omega
  have complete := (family width stage).program_apply_encoded_ket_flags
    (QubitLayout.canonical _) .empty environment (tree width) state
    (SelectionFrame.clean_of_prefix_zero width state clean)
  simp only [address_label] at complete
  have flags : ∀ label : Fin (2 ^ ScanMetadata.addressWidth width),
      decide (label = state.2.1.toFin) = decide (label.val = state.2.1.toNat) := by
    intro label
    simp only [Fin.ext_iff, BitVec.val_toFin]
  simp only [flags] at complete
  have root : ((SelectionFrame.frame width).stack ⟨0, by omega⟩).get state =
      state.1.control := rfl
  rw [root] at complete
  have visits := StreamedSelector.fold_pruneBelow (width + 3) capacity
    (fun index selected => (payload width stage index).callbackStep selected)
    state.1.control state.2.1.toNat state
  have recurrence := callback_range_complete width stage (width + 3) state.1.control
    state.2.1.toNat state initial within
  have actual : ((StreamedSelector.labelsAt (width := ScanMetadata.addressWidth width)
      (tree width) 0 (by omega)).foldl (fun value label =>
        (payload width stage label.val).callbackStep
          (state.1.control && decide (label.val = state.2.1.toNat)) value) state) =
      (flagEquiv width).symm (if state.1.control then
        ThresholdStream.word (baseAction width stage) (state.2.1.toNat + 1)
          (flagEquiv width state).1 else (flagEquiv width state).1, false) := by
    apply (flagEquiv width).injective
    dsimp only [tree]
    rw [visits, recurrence, Equiv.apply_symm_apply]
  change (program width stage).applyNormalized environment _ = _ at complete
  have projection : ∀ label, (family width stage).payload label =
      payload width stage label.val := fun _ => rfl
  simp only [projection] at complete
  rw [actual] at complete
  exact complete

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTemplate
