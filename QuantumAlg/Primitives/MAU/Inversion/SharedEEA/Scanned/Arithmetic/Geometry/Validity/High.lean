/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Validity
import all QuantumAlg.Components.Encoded.BitGates.StreamedSelector.Pruning

/-!
# Actual high-carry validity on the same full finite geometry frame

The high branch retains every original address. In the small exact-capacity
case it accepts the actual full work-word length, rather than discarding
the carry. Its pruned tree is empty for P-256 and larger ordinary widths.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.GeometryValidity

noncomputable section

open EncodedBit WindowLookup NumberTheory.SharedEEA

/-- A high carry contributes its full place value, without truncating the address. -/
def highActive (width : Nat) (label : Fin (2 ^ ScanMetadata.addressWidth width)) : Bool :=
  decide (2 ^ ScanMetadata.addressWidth width + label.val ≤ width + 3)

/-- Retain precisely the original high-carry addresses that are actual physical lengths. -/
def highTree (width : Nat) : SelectorTrie (ScanMetadata.addressWidth width) :=
  .prune (ScanMetadata.addressWidth width) (highActive width)

/-- The same physical root, address and prefix compute the additional high-carry branch. -/
def highProgram (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum :=
  (frame width).program (QubitLayout.canonical _) .empty (callback width) (highTree width)

/-- Only the original arbitrary Iter output toggles on a valid high-carry length. -/
def highStep (width : Nat) (state : Data width) : Data width :=
  if state.2.2.2 && decide (2 ^ ScanMetadata.addressWidth width + state.2.1.toNat ≤ width + 3)
    then (output width).flip state else state

/-- Actual coherent high-carry execution retains the complete original frame and shared pool. -/
lemma highProgram_apply_encoded_ket (width : Nat) (environment : OracleModel.empty.Interpretation)
    (state : Data width) (zero : state.2.2.1 = 0#(ScanMetadata.addressWidth width)) :
    (highProgram width).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (highStep width state))) := by
  have actual := SelectorFrame.program_apply_encoded_ket_clean (frame width)
    (QubitLayout.canonical _) .empty (callback width) (fun _ => (output width).flip) environment
    (fun label => callback_realizes width label environment) (fun _ => preserves width)
    (fun _ => independent width) (highTree width) state (clean width state zero)
  change (highProgram width).applyNormalized environment _ = _ at actual
  have selected : conditionalAction ((frame width).stack ⟨0, by omega⟩)
      ((frame width).selectedActionAt (fun _ => (output width).flip) (highTree width)
        0 (by omega) 0 (by omega)) state = highStep width state := by
    change (if state.2.2.2 then
      (frame width).selectedActionAt (fun _ => (output width).flip) (highTree width)
        0 (by omega) 0 (by omega) state else state) = _
    rw [highTree, SelectorFrame.selectedActionAt_prune, address_label]
    change (if state.2.2.2 then
      (if decide (2 ^ ScanMetadata.addressWidth width + state.2.1.toFin.val ≤ width + 3) then
        (output width).flip state else state) else state) = _
    rw [BitVec.val_toFin]
    unfold highStep
    cases state.2.2.2 <;> rfl
  rw [selected] at actual
  exact actual

/-- The complete P-256 high-carry tree has no native fork and no callback. -/
lemma p256_highTree : highTree 256 = .skip 10 := by
  apply StreamedSelector.prune_of_false
  intro label
  apply decide_eq_false
  change ¬1024 + label.val ≤ 259
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.GeometryValidity
