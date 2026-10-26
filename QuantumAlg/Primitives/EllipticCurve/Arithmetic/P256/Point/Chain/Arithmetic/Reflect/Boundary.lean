/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Reflect.Program
import all QuantumAlg.Primitives.MAU.Addition.TTK.Placement.Readout

/-!
# Original numerical word boundary of the retained-enable reflection

The full-frame coordinates read the original numerical A and X words.
The actual program changes X to p-1-X in enabled canonical sectors and
restores clean A. Every physical position outside those words is retained.
The next table column is Qx+1, so this reflection precedes Qx-X.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Arithmetic

namespace Reflect

noncomputable section

open EncodedBit

attribute [local irreducible] WireSubsystem.complementWidth
attribute [local irreducible] Frame.payloadWidth layout

private lemma word_reads (port : WordPort) (state : Frame.Raw) (index : Fin 256) :
    ((word port).bit index).get state =
      (BitVec.ofFin (port.value state)).getMsbD index.val := by
  change (port.bit index.rev).get state = _
  rw [WordPort.bit_get]
  simp only [Fin.val_rev, BitVec.getMsbD_eq_getLsbD, index.isLt, decide_true, Bool.true_and,
    BitVec.getLsbD]
  change (port.value state).val.testBit (256 - (index.val + 1)) =
    (port.value state).val.testBit (256 - 1 - index.val)
  apply congrArg (Nat.testBit (port.value state).val)
  omega

lemma grouped_work1 (state : Frame.Raw) :
    (layout.grouping state).1.1 = Frame.work1 state := by
  apply words.grouped_addend_fin_of_wires restEncoding layout _ state
    (Frame.work1 state) (word_reads .work1 state)
  intro index
  have location := (subsystem.placeBit_wire source_onto Frame.encoding_surjective
    (MAU.Addition.TTK.WordPlacement.firstLens index)).trans
      (wordPairSubsystem_left words.addend words.target words.addendDistinct
        words.targetDistinct words.separate index)
  simpa only [WireSubsystem.placeBit, WireSubsystem.paddedBit, WireSubsystem.paddedEncoding,
    layout, restEncoding]
    using location

lemma grouped_work2 (state : Frame.Raw) :
    (layout.grouping state).1.2 = Frame.work2 state := by
  apply words.grouped_target_fin_of_wires restEncoding layout _ state
    (Frame.work2 state) (word_reads .work2 state)
  intro index
  have location := (subsystem.placeBit_wire source_onto Frame.encoding_surjective
    (MAU.Addition.TTK.WordPlacement.secondLens index)).trans
      (wordPairSubsystem_right words.addend words.target words.addendDistinct
        words.targetDistinct words.separate index)
  simpa only [WireSubsystem.placeBit, WireSubsystem.paddedBit, WireSubsystem.paddedEncoding,
    layout, restEncoding]
    using location

/-- Complete output coordinates keep A and the whole physical complement. -/
def step (state : Frame.Raw) : Frame.Raw :=
  layout.grouping.symm
    (((layout.grouping state).1.1,
      outputWord (layout.grouping state).1.2 (layout.grouping state).2),
      (layout.grouping state).2)

lemma step_work1 (state : Frame.Raw) : Frame.work1 (step state) = Frame.work1 state := by
  have preserves {Data A B Saved : Type} (grouping : Data ≃ ((A × B) × Saved))
      (read : Data → A) (same : ∀ value, (grouping value).1.1 = read value)
      (next : B → Saved → B) (value : Data) :
      read (grouping.symm
        (((grouping value).1.1, next (grouping value).1.2 (grouping value).2),
          (grouping value).2)) = read value := by
    have coordinates := congrArg (fun item : (A × B) × Saved => item.1.1)
      (grouping.apply_symm_apply
        (((grouping value).1.1, next (grouping value).1.2 (grouping value).2),
          (grouping value).2))
    exact (same _).symm.trans (coordinates.trans (same value))
  exact preserves layout.grouping Frame.work1 grouped_work1 outputWord state

lemma step_work2 (state : Frame.Raw) :
    Frame.work2 (step state) =
      if Native.BorrowedControl.flag.get state then
        MAU.Addition.TTK.Reflection.reflected (width := 256) constant (Frame.work2 state)
      else Frame.work2 state := by
  rw [← grouped_work2, step, Equiv.apply_symm_apply]
  dsimp only [outputWord]
  rw [controlBit_get, grouped_work2]
  rfl

/-- This boundary keeps the entire existing complement, including gamma and arbitrary W. -/
lemma step_other (observed : EncodedBit Frame.encoding)
    (outside : observed.wire ∉ Set.range subsystem.wires) (state : Frame.Raw) :
    observed.get (step state) = observed.get state := by
  have before := subsystem.full_complement_read
    source_onto Frame.encoding_surjective observed outside state
  have after := subsystem.full_complement_read
    source_onto Frame.encoding_surjective observed outside
    (step state)
  exact after.symm.trans (by
    simpa only [step, layout, Equiv.apply_symm_apply] using before)

/-- Canonical arithmetic is required only on the actually enabled sectors. -/
lemma step_work2_value (state : Frame.Raw)
    (canonical : Native.BorrowedControl.flag.get state = true →
      (Frame.work2 state).val < modulus) :
    (Frame.work2 (step state)).val =
      if Native.BorrowedControl.flag.get state then modulus - 1 - (Frame.work2 state).val
      else (Frame.work2 state).val := by
  rw [step_work2]
  split
  · exact MAU.Addition.TTK.Reflection.reflected_value constant _ (canonical ‹_›)
  · rfl

private lemma clean_input (state : Frame.Raw)
    (clean : Frame.work1 state = MAU.Addition.TTK.Reflection.zero 256) :
    state = inputState (Frame.work2 state) (layout.grouping state).2 := by
  apply layout.grouping.injective
  change layout.grouping state =
    layout.grouping (layout.grouping.symm
      ((MAU.Addition.TTK.Reflection.zero 256, Frame.work2 state), (layout.grouping state).2))
  rw [Equiv.apply_symm_apply]
  exact Prod.ext (Prod.ext ((grouped_work1 state).trans clean) (grouped_work2 state)) rfl

/-- The actual placed native word realizes this full boundary on every clean-A input. -/
lemma program_apply_clean (environment : OracleModel.empty.Interpretation) (state : Frame.Raw)
    (clean : Frame.work1 state = MAU.Addition.TTK.Reflection.zero 256) :
    program.applyNormalized environment (Native.ket state) = Native.ket (step state) := by
  have actual := program_apply environment (Frame.work2 state) (layout.grouping state).2
  rw [← clean_input state clean] at actual
  apply actual.trans
  apply congrArg Native.ket
  apply layout.grouping.injective
  simp only [inputState, step, Equiv.apply_symm_apply, grouped_work1, grouped_work2, clean]

end

end Reflect

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Arithmetic
