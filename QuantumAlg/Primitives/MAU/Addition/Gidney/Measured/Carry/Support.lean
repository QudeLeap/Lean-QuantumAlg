/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Gates
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Gates
import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-!
# Full physical read/write support of the literal native carry word

Every native gate reads and writes only the supplied control, source and
carry-output systems. An excluded physical bit is therefore retained and
its flip commutes with the same native word. This full-label law includes
arbitrary dirty values and is used when uncomputing comparison workspace
[G25, main.tex:253-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

private lemma affine_disjoint (observed offset first second output : EncodedBit encoding)
    (offsetFirst : offset.wire ≠ first.wire) (offsetSecond : offset.wire ≠ second.wire)
    (firstSecond : first.wire ≠ second.wire) (firstOutput : first.wire ≠ output.wire)
    (secondOutput : second.wire ≠ output.wire) (useFirst useSecond : Bool)
    (offsetOutside : offset.wire ≠ observed.wire) (firstOutside : first.wire ≠ observed.wire)
    (secondOutside : second.wire ≠ observed.wire) (outputOutside : output.wire ≠ observed.wire) :
    ∀ gate ∈ affineToffoliGates offset first second output offsetFirst offsetSecond firstSecond
      firstOutput secondOutput useFirst useSecond, bitDisjoint observed gate := by
  cases useFirst <;> cases useSecond <;>
    simp [affineToffoliGates, bitDisjoint, offsetOutside, firstOutside, secondOutside,
      outputOutside]

private lemma descending_disjoint {length : Nat}
    (layout : CarryLayout encoding (length + 1)) (constant : BitVec (length + 1))
    (positive : 0 < length) (observed : EncodedBit encoding)
    (controlOutside : layout.control.wire ≠ observed.wire)
    (sourceOutside : ∀ index, (layout.source index).wire ≠ observed.wire)
    (outputOutside : ∀ index, (layout.output index).wire ≠ observed.wire) :
    ∀ gate ∈ layout.descendingTop constant positive, bitDisjoint observed gate := by
  unfold descendingTop
  apply affine_disjoint
  · exact controlOutside
  · exact sourceOutside _
  · exact outputOutside _
  · exact outputOutside _

private lemma ascending_disjoint {length : Nat}
    (layout : CarryLayout encoding (length + 1)) (constant : BitVec (length + 1))
    (positive : 0 < length) (observed : EncodedBit encoding)
    (controlOutside : layout.control.wire ≠ observed.wire)
    (sourceOutside : ∀ index, (layout.source index).wire ≠ observed.wire)
    (outputOutside : ∀ index, (layout.output index).wire ≠ observed.wire) :
    ∀ gate ∈ layout.ascendingTop constant positive, bitDisjoint observed gate := by
  unfold ascendingTop
  apply affine_disjoint
  · exact controlOutside
  · exact sourceOutside _
  · exact outputOutside _
  · exact outputOutside _

private lemma offset_disjoint {length : Nat}
    (layout : CarryLayout encoding (length + 1)) (constant : BitVec (length + 1))
    (observed : EncodedBit encoding) (controlOutside : layout.control.wire ≠ observed.wire)
    (outputOutside : ∀ index, (layout.output index).wire ≠ observed.wire) :
    ∀ gate ∈ layout.topOffsetGates constant, bitDisjoint observed gate := by
  unfold topOffsetGates
  split_ifs <;> simp [bitDisjoint, controlOutside, outputOutside]

private lemma low_disjoint {length : Nat} (layout : CarryLayout encoding length)
    (constant : BitVec length) (observed : EncodedBit encoding)
    (controlOutside : layout.control.wire ≠ observed.wire)
    (sourceOutside : ∀ index, (layout.source index).wire ≠ observed.wire)
    (outputOutside : ∀ index, (layout.output index).wire ≠ observed.wire) :
    ∀ gate ∈ layout.lowGates constant, bitDisjoint observed gate := by
  unfold lowGates
  by_cases nonempty : 0 < length
  · rw [dif_pos nonempty]
    cases constant.getLsbD 0 <;>
      simp [bitDisjoint, controlOutside, sourceOutside, outputOutside]
  · rw [dif_neg nonempty]
    simp

/-- Every actual native instruction uses only the original control/source/carry-output ports. -/
lemma gates_bitDisjoint : ∀ {length : Nat} (layout : CarryLayout encoding length)
    (constant : BitVec length) (observed : EncodedBit encoding),
    layout.control.wire ≠ observed.wire →
    (∀ index, (layout.source index).wire ≠ observed.wire) →
    (∀ index, (layout.output index).wire ≠ observed.wire) →
    ∀ gate ∈ layout.gates constant, bitDisjoint observed gate := by
  intro length
  induction length with
  | zero => intro layout constant observed _ _ _; simp [gates]
  | succ length ih =>
      intro layout constant observed controlOutside sourceOutside outputOutside
      rw [gates]
      by_cases positive : 0 < length
      · rw [dif_pos positive]
        intro gate present
        rcases List.mem_append.mp present with before | finish
        · rcases List.mem_append.mp before with before | offset
          · rcases List.mem_append.mp before with descend | lower
            · exact descending_disjoint layout constant positive observed controlOutside
                sourceOutside outputOutside gate descend
            · exact ih layout.lower (constant.setWidth length) observed controlOutside
                (fun index => sourceOutside index.castSucc)
                (fun index => outputOutside index.castSucc) gate lower
          · exact offset_disjoint layout constant observed controlOutside outputOutside gate offset
        · exact ascending_disjoint layout constant positive observed controlOutside
            sourceOutside outputOutside gate finish
      · rw [dif_neg positive]
        intro gate present
        rcases List.mem_append.mp present with offset | low
        · exact offset_disjoint layout constant observed controlOutside outputOutside gate offset
        · exact low_disjoint layout constant observed controlOutside sourceOutside outputOutside
            gate low

/-- The full native carry word commutes with flipping any excluded original physical bit. -/
lemma gates_flip_comm {length : Nat} (layout : CarryLayout encoding length)
    (constant : BitVec length) (observed : EncodedBit encoding)
    (controlOutside : layout.control.wire ≠ observed.wire)
    (sourceOutside : ∀ index, (layout.source index).wire ≠ observed.wire)
    (outputOutside : ∀ index, (layout.output index).wire ≠ observed.wire) (state : Data) :
    stepList (layout.gates constant) (observed.flip state) =
      observed.flip (stepList (layout.gates constant) state) :=
  stepList_flip_comm_of_bitDisjoint _ _
    (gates_bitDisjoint layout constant observed controlOutside sourceOutside outputOutside) state

end

end QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout
