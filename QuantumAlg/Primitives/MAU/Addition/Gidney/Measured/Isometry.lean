/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Tail.Wires
import all QuantumAlg.Util.Nat.FixedWidth

/-!
# Injectivity of the full actual adder label map on its clean-helper input subspace

Finite selected addition is cancellative once the unchanged coherent control
is fixed. Every dirty and outside physical bit is retained, and both helpers
are zero at input and output. These facts identify the complete original
encoded label. No injectivity of a free reset map is assumed
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The complete actual target word is exactly selected finite-word addition. -/
lemma adderWord_targetWord (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false) :
    layout.targetWord (wordLabel (layout.adderWord wide constant) initial) =
      layout.targetWord initial + layout.selectedOffsetWord constant initial := by
  apply BitVec.eq_of_getLsbD_eq
  intro index inside
  change (layout.targetWord (wordLabel (layout.adderWord wide constant) initial)).toNat.testBit
    index = _
  rw [targetWord_bit _ _ _ inside, adderWord_target_get layout wide constant initial clean]

/-- Equal complete outputs imply equal complete clean-helper inputs, with arbitrary dirty bits. -/
lemma adderWord_label_injective_clean (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (first second : Data)
    (firstClean : ∀ helper, (layout.clean helper).get first = false)
    (secondClean : ∀ helper, (layout.clean helper).get second = false)
    (same : wordLabel (layout.adderWord wide constant) first =
      wordLabel (layout.adderWord wide constant) second) : first = second := by
  have sameControl : layout.control.get first = layout.control.get second := by
    have actual := congrArg layout.control.get same
    rwa [adderWord_control_get layout wide constant first firstClean,
      adderWord_control_get layout wide constant second secondClean] at actual
  have sameOffset : layout.selectedOffsetWord constant first =
      layout.selectedOffsetWord constant second := by
    unfold selectedOffsetWord
    rw [sameControl]
  have sameTarget : layout.targetWord first = layout.targetWord second := by
    have actual := congrArg layout.targetWord same
    rw [adderWord_targetWord layout wide constant first firstClean,
      adderWord_targetWord layout wide constant second secondClean, sameOffset] at actual
    exact (BitVec.add_left_inj _).mp actual
  have samePort (port : Port width) :
      (layout.bit port).get first = (layout.bit port).get second := by
    rcases port with singleton | index | index | helper
    · cases singleton
      exact sameControl
    · have bit := congrArg (fun word : BitVec width => word.toNat.testBit index.val) sameTarget
      rwa [targetWord_bit _ _ _ index.isLt, targetWord_bit _ _ _ index.isLt] at bit
    · have actual := congrArg (layout.dirty index).get same
      rwa [adderWord_dirty_get layout wide constant first firstClean,
        adderWord_dirty_get layout wide constant second secondClean] at actual
    · exact (firstClean helper).trans (secondClean helper).symm
  apply encoding.encode_injective
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro bit
  let wire := WireAddress.littleEndianWire bit
  by_cases addressed : ∃ port, (layout.bit port).wire = wire
  · obtain ⟨port, portWire⟩ := addressed
    have actual := samePort port
    rw [← (layout.bit port).get_eq first, ← (layout.bit port).get_eq second, portWire] at actual
    simpa only [wire, WireAddress.bitIndex_littleEndianWire] using actual
  · have outside : ∀ port, (layout.bit port).wire ≠ wire := by
      intro port equal
      exact addressed ⟨port, equal⟩
    have firstRetained := adderWord_wire_read layout wide constant wire outside first
    have secondRetained := adderWord_wire_read layout wide constant wire outside second
    have actual := congrArg (fun state : Data =>
      (encoding.encode state).val.testBit (WireAddress.bitIndex wire).val) same
    have inputSame := firstRetained.symm.trans (actual.trans secondRetained)
    simpa only [wire, WireAddress.bitIndex_littleEndianWire] using inputSame

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
