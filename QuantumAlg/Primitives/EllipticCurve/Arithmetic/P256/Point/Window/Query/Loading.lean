/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Body.Graph

/-!
# Original full-label input of the actual stored-table arithmetic query

The same native lookup changes its existing result word by XOR. All
twenty-one original pool bits retain their values, so the initialized
pool supplies the concrete arithmetic and selector premises internally.
The actual zero target establishes the same full original table graph.
These are symbolic word and selector facts, without gate-list expansion.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryInsertion

noncomputable section

open EncodedBit.WindowLookup

private lemma originalSource_width : (MAU.Inversion.SharedEEA.encoding 256).width = 559 := by
  rw [MAU.Inversion.SharedEEA.encoding_width]
  decide

private lemma pool_eq_of_scan_get (first second : Raw)
    (same : ∀ bit : EncodedBit (MAU.Inversion.SharedEEA.Scanned.encoding 256),
      559 ≤ bit.wire.val → bit.wire.val < 580 →
      (pointBit (Frame.scanBit bit)).get first = (pointBit (Frame.scanBit bit)).get second) :
    first.1.1.1.2 = second.1.1.1.2 := by
  apply Prod.ext
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    have actual := same (MAU.Inversion.SharedEEA.Scanned.addressBit 256 ⟨index, within⟩)
      (by rw [MAU.Inversion.SharedEEA.Scanned.addressBit_wire, originalSource_width]; omega)
      (by
        rw [MAU.Inversion.SharedEEA.Scanned.addressBit_wire, originalSource_width]
        change 559 + index < 580
        have limit : index < 10 := by simpa only
          [Frame.payloadWidth, NumberTheory.SharedEEA.ScanMetadata.p256_addressWidth] using within
        omega)
    simpa only [pointBit_get, Frame.scanBit_get,
      MAU.Inversion.SharedEEA.Scanned.addressBit_get] using actual
  · apply Prod.ext
    · apply BitVec.eq_of_getMsbD_eq
      intro index within
      have actual := same (MAU.Inversion.SharedEEA.Scanned.prefixBit 256 ⟨index, within⟩)
        (by rw [MAU.Inversion.SharedEEA.Scanned.prefixBit_wire, originalSource_width]; omega)
        (by
          rw [MAU.Inversion.SharedEEA.Scanned.prefixBit_wire, originalSource_width]
          change 559 + NumberTheory.SharedEEA.ScanMetadata.addressWidth 256 + index < 580
          rw [NumberTheory.SharedEEA.ScanMetadata.p256_addressWidth]
          have limit : index < 10 := by simpa only
            [Frame.payloadWidth, NumberTheory.SharedEEA.ScanMetadata.p256_addressWidth] using within
          omega)
      simpa only [pointBit_get, Frame.scanBit_get,
        MAU.Inversion.SharedEEA.Scanned.prefixBit_get] using actual
    · exact same (MAU.Inversion.SharedEEA.Scanned.conjunctionBit 256)
        (by rw [MAU.Inversion.SharedEEA.Scanned.conjunctionBit_wire, originalSource_width]; omega)
        (by rw [MAU.Inversion.SharedEEA.Scanned.conjunctionBit_wire, originalSource_width,
          NumberTheory.SharedEEA.ScanMetadata.p256_addressWidth]; omega)

/-- An actual result-word XOR preserves the complete original shared scan pool. -/
lemma wordXor_pool (port : WordPort) (constant : Fin (2 ^ 256)) (state : Raw) :
    (EncodedBit.Word.xorConstantStep (resultWord port) constant state).1.1.1.2 =
      state.1.1.1.2 := by
  apply pool_eq_of_scan_get
  intro bit lower upper
  apply EncodedBit.Word.xorConstantStep_get_observed_of_target_ne
  intro index same
  have positions := congrArg Fin.val same
  rw [resultWord_wire, pointBit_wire, Frame.scanBit_wire] at positions
  have within := index.isLt
  cases port <;> simp only [WordPort.physicalIndex] at positions <;> omega

/-- The mathematical endpoint of the literal full original-address loader. -/
def loadedState (stream : Fin 2) (port : WordPort) (highRemaining lowWidth : Nat)
    (bounded : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (table : Bool → Fin (2 ^ (highRemaining + lowWidth)) → Fin (2 ^ 256)) (state : Raw) : Raw :=
  splitLookupStep (selector stream (highRemaining + lowWidth) bounded)
    ((Window.unlookup stream port highRemaining lowWidth bounded lowBound).cycleTarget
      (selector stream (highRemaining + lowWidth) bounded)
      (fun bit _label => resultWord_address port bit _)
      (fun bit label => resultWord_stack port bit stream _ bounded label)) table state

lemma loadedState_pool (stream : Fin 2) (port : WordPort) (highRemaining lowWidth : Nat)
    (bounded : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (table : Bool → Fin (2 ^ (highRemaining + lowWidth)) → Fin (2 ^ 256)) (state : Raw) :
    (loadedState stream port highRemaining lowWidth bounded lowBound table state).1.1.1.2 =
      state.1.1.1.2 :=
  wordXor_pool port _ state

lemma loadedState_cleanPool (stream : Fin 2) (port : WordPort) (highRemaining lowWidth : Nat)
    (bounded : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (table : Bool → Fin (2 ^ (highRemaining + lowWidth)) → Fin (2 ^ 256)) (state : Raw)
    (clean : Frame.CleanPool state.1) :
    Frame.CleanPool
      (loadedState stream port highRemaining lowWidth bounded lowBound table state).1 :=
  (loadedState_pool stream port highRemaining lowWidth bounded lowBound table state).trans clean

lemma selector_cleanFrom_of_cleanPool (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Raw) (clean : Frame.CleanPool state.1) :
    (selector stream width bounded).CleanFrom 0 state := by
  intro index _
  exact selector_prefix_clean stream width bounded index state clean

/-- Actual zero-target loading supplies the precise graph needed by the later paid unlookup. -/
lemma loadedState_graph (stream : Fin 2) (port : WordPort) (highRemaining lowWidth : Nat)
    (bounded : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (table : Bool → Fin (2 ^ (highRemaining + lowWidth)) → Fin (2 ^ 256)) (state : Raw)
    (zero : ∀ index, ((resultWord port).bit index).get state = false) :
    (Window.unlookup stream port highRemaining lowWidth bounded lowBound).Graph (splitTable table)
      (loadedState stream port highRemaining lowWidth bounded lowBound table state) :=
  EncodedBit.WindowLookup.UnlookupFrame.splitLookupStep_graph _ _
    (fun bit _label => resultWord_address port bit _)
    (fun bit label => resultWord_stack port bit stream _ bounded label)
    (addressSplit stream port highRemaining lowWidth bounded lowBound) table state zero

end

end QueryInsertion

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
