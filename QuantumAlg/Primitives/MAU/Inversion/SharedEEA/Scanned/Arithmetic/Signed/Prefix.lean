/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Signed.Callback
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.NativeFold

/-!
# One actual signed traversal with the original selected boundary

The same fixed native tree visits every original template index.
Its retained full quantum address selects exactly one top instruction;
the moving flag limits operand execution to the corresponding prefix.
The paid initial control copy and every physical pool position remain
part of the executed program [TTK09, qic-loglogaddition-quant.tex:285-318].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticSigned

noncomputable section

open EncodedBit WindowLookup StreamedSelector NumberTheory.SharedEEA ArithmeticTemplate

/-- Every native visit agrees with the exact ordered boundary fold on the complete base and flag. -/
lemma callback_fold (width : Nat) (kind : ArithmeticTop.Kind) (indices : List Nat)
    (enabled : Bool) (last : Nat) (state : Data width) :
    flagEquiv width (indices.foldl (fun value index =>
      callbackStep width kind index (enabled && decide (index = last)) value) state) =
      indices.foldl (ThresholdStream.Boundary.forwardStep (baseAction width (stage kind))
        (boundaryAction width kind) enabled last) (flagEquiv width state) := by
  symm
  apply List.foldl_hom (flagEquiv width)
  intro value index
  exact (callback_threshold width kind index enabled last value).symm

private lemma callback_range_complete (width : Nat) (kind : ArithmeticTop.Kind) (count : Nat)
    (enabled : Bool) (last : Nat) (state : Data width)
    (initial : state.2.2.2 = enabled) (within : last < count) :
    flagEquiv width ((List.range count).foldl (fun value index =>
      callbackStep width kind index (enabled && decide (index = last)) value) state) =
      (if enabled then boundaryAction width kind last
        (ThresholdStream.word (baseAction width (stage kind)) (last + 1)
          (flagEquiv width state).1) else (flagEquiv width state).1, false) := by
  rw [callback_fold]
  have start : flagEquiv width state = ((flagEquiv width state).1, enabled) :=
    Prod.ext rfl initial
  rw [start, ThresholdStream.Boundary.forward_complete _ _ _ _ _ _ within]

/-- The literal actual tree fuses top overflow with its original operand traversal. -/
def program (width : Nat) (kind : ArithmeticTop.Kind) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (SelectionFrame.frame width).program (QubitLayout.canonical _) .empty
    (callback width kind) (ArithmeticTemplate.tree width)

private lemma program_apply_prefix (width : Nat) (positive : 1 ≤ width)
    (kind : ArithmeticTop.Kind) (environment : OracleModel.empty.Interpretation)
    (state : Data width) (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (initial : state.2.2.2 = state.1.control) (within : state.2.1.toNat < width + 3) :
    (program width kind).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode ((flagEquiv width).symm
          (if state.1.control then boundaryAction width kind state.2.1.toNat
            (ThresholdStream.word (baseAction width (stage kind)) (state.2.1.toNat + 1)
              (flagEquiv width state).1) else (flagEquiv width state).1, false)))) := by
  have capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width := by
    have last := ScanMetadata.targetIndex_lt width positive
      (⟨width + 2, by omega⟩ : Fin (width + 3))
    change width + 2 < _ at last
    omega
  have complete := program_apply_encoded_ket_streamed_clean (SelectionFrame.frame width)
    (QubitLayout.canonical _) .empty (callback width kind)
    (fun label => callbackStep width kind label.val) environment
    (fun label => callback_realizes width kind label environment)
    (callbackStep_preserves width kind) (callbackStep_independent width kind)
    (ArithmeticTemplate.tree width) state (SelectionFrame.clean_of_prefix_zero width state clean)
  rw [foldAt_eq_bits (SelectionFrame.frame width) _ (callbackStep_preserves width kind)
    (fun index => ((SelectionFrame.frame width).address index).get state)
    (ArithmeticTemplate.tree width) 0 (by omega) 0 (by omega)
    (((SelectionFrame.frame width).stack ⟨0, by omega⟩).get state) state (fun _ => rfl),
    foldBitsAt_eq_label_flags (SelectionFrame.frame width) _ state (fun _ => rfl)] at complete
  simp only [ArithmeticTemplate.address_label] at complete
  have flags : ∀ label : Fin (2 ^ ScanMetadata.addressWidth width),
      decide (label = state.2.1.toFin) = decide (label.val = state.2.1.toNat) := by
    intro label
    simp only [Fin.ext_iff, BitVec.val_toFin]
  simp only [flags] at complete
  have root : ((SelectionFrame.frame width).stack ⟨0, by omega⟩).get state =
      state.1.control := rfl
  rw [root] at complete
  have visits := fold_pruneBelow (width + 3) capacity (callbackStep width kind)
    state.1.control state.2.1.toNat state
  have recurrence := callback_range_complete width kind (width + 3) state.1.control
    state.2.1.toNat state initial within
  have actual : ((labelsAt (width := ScanMetadata.addressWidth width)
      (ArithmeticTemplate.tree width) 0 (by omega)).foldl (fun value label =>
        callbackStep width kind label.val
          (state.1.control && decide (label.val = state.2.1.toNat)) value) state) =
      (flagEquiv width).symm (if state.1.control then
        boundaryAction width kind state.2.1.toNat
          (ThresholdStream.word (baseAction width (stage kind)) (state.2.1.toNat + 1)
            (flagEquiv width state).1) else (flagEquiv width state).1, false) := by
    apply (flagEquiv width).injective
    dsimp only [ArithmeticTemplate.tree]
    rw [visits, recurrence, Equiv.apply_symm_apply]
  change (program width kind).applyNormalized environment _ = _ at complete
  rw [actual] at complete
  exact complete

/-- The selected top word follows exactly its original native operand prefix. -/
def nativeWord (width : Nat) (kind : ArithmeticTop.Kind) (last : Nat) :
    List (GateSpec (encoding width)) :=
  prefixGates width (stage kind) (last + 1) ++ ArithmeticTop.source width kind last

private lemma nativeWord_flagEquiv (width : Nat) (kind : ArithmeticTop.Kind) (last : Nat)
    (state : Data width) :
    flagEquiv width (GateSpec.stepList (nativeWord width kind last) state) =
      (boundaryAction width kind last
        (ThresholdStream.word (baseAction width (stage kind)) (last + 1)
          (flagEquiv width state).1), (flagEquiv width state).2) := by
  rw [nativeWord, GateSpec.stepList_append]
  have top := top_flagEquiv width kind last
    (flagEquiv width (GateSpec.stepList (prefixGates width (stage kind) (last + 1)) state)).1
    (flagEquiv width (GateSpec.stepList (prefixGates width (stage kind) (last + 1)) state)).2
  simp only [Prod.eta, Equiv.symm_apply_apply] at top
  rw [top, prefixGates_flagEquiv]

/-- One paid original Ctrl-to-conjunction copy prepares the same shared moving flag. -/
def forwardProgram (width : Nat) (kind : ArithmeticTop.Kind) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  ((startGate width).program (QubitLayout.canonical _) .empty).seq (program width kind)

/-- The fused stage executes the exact original native prefix and top gate, restoring its flag. -/
lemma forwardProgram_apply_nativeWord (width : Nat) (positive : 1 ≤ width)
    (kind : ArithmeticTop.Kind) (environment : OracleModel.empty.Interpretation)
    (state : Data width) (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (within : state.2.1.toNat < width + 3) :
    (forwardProgram width kind).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (if state.1.control then
          GateSpec.stepList (nativeWord width kind state.2.1.toNat) state else state))) := by
  let started := (startGate width).step state
  have fields := start_fields width state
  have prepared : started.2.2.2 = started.1.control := by
    change ((startGate width).step state).2.2.2 = ((startGate width).step state).1.control
    rw [start_flag, fields.1, zero]
    simp
  have cleanStarted : started.2.2.1 = 0#(ScanMetadata.addressWidth width) :=
    fields.2.2.trans clean
  have withinStarted : started.2.1.toNat < width + 3 := by
    change ((startGate width).step state).2.1.toNat < _
    rw [fields.2.1]
    exact within
  have preparation := (GateSpec.realizes (QubitLayout.canonical _) .empty
    (startGate width) environment).apply_encoded_ket state
  rw [forwardProgram, UnitaryCircuit.applyNormalized_seq, preparation]
  have actual := program_apply_prefix width positive kind environment started
    cleanStarted prepared withinStarted
  dsimp only [started] at actual
  rw [start_base, fields.1, fields.2.1] at actual
  have output : (flagEquiv width).symm (if state.1.control then
      boundaryAction width kind state.2.1.toNat
        (ThresholdStream.word (baseAction width (stage kind)) (state.2.1.toNat + 1)
          (flagEquiv width state).1) else (flagEquiv width state).1, false) =
      (if state.1.control then GateSpec.stepList (nativeWord width kind state.2.1.toNat) state
        else state) := by
    apply (flagEquiv width).injective
    rw [Equiv.apply_symm_apply]
    split
    · rw [nativeWord_flagEquiv]
      exact Prod.ext rfl zero.symm
    · exact Prod.ext rfl zero.symm
  rw [output] at actual
  exact actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticSigned
