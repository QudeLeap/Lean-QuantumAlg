/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Frame.Ports
import all QuantumAlg.Primitives.MeasuredUncompute.Native.Product.Frame
import all QuantumAlg.Util.FinPow.BinaryBasis
import all QuantumAlg.Util.Nat.FixedWidth

/-!
# Actual product grouping reads X, Y, A and the complete retained history

The word equations are derived from the existing placement's actual wire
bijection. The left and right product inputs read the original X and Y
ports; its accumulator reads A. The independent history read includes all
six padding bits and every original length/control bit
[LYL+26, sec_point_add/sec_point_add.tex:51-105]. No ideal arithmetic map
is substituted for the placement's actual grouping.
-/

namespace QuantumAlg.MeasuredUncompute.ProductReadout

noncomputable section

open ProductPlacement MAU.Multiplication BinaryLabelEncoding

private def readWord {width : Nat} (word : EncodedBit.Word (frameEncoding width) width)
    (state : Frame width) : Fin (2 ^ width) :=
  BinaryBasis.bigEndianEquiv width
    (fun index => finTwoEquiv.symm ((word.bit index).get state))

private theorem readWord_bit {width : Nat}
    (word : EncodedBit.Word (frameEncoding width) width) (state : Frame width) (index : Fin width) :
    (readWord word state).val.testBit index.rev.val = (word.bit index).get state := by
  rw [readWord, BinaryBasis.bigEndianEquiv_bit]
  exact finTwoEquiv.apply_symm_apply _

/-- The complete first input value is read from the actual trailing Work2 bit lenses. -/
def input (width : Nat) (state : Frame width) : Fin (2 ^ width) :=
  readWord (FramePorts.input width) state

/-- The complete second input value is read from the already existing Y bit lenses. -/
def numerator (width : Nat) (state : Frame width) : Fin (2 ^ width) :=
  readWord (FramePorts.numerator width) state

/-- The complete target value is read from the first n actual Work1 bit lenses. -/
def accumulator (width : Nat) (state : Frame width) : Fin (2 ^ width) :=
  readWord (FramePorts.accumulator width) state

private theorem word_ext {width : Nat} {left right : Fin (2 ^ width)}
    (bits : ∀ index : Fin width, left.val.testBit index.rev.val =
      right.val.testBit index.rev.val) : left = right := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  simpa only [Fin.rev_rev] using bits index.rev

private theorem bit_read {Data : Type} {label : BinaryLabelEncoding Data}
    (bit : EncodedBit label) (state : Data) :
    bit.get state = (label.encode state).val.testBit bit.wire.rev.val := by
  rw [← bit.get_eq]
  apply congrArg (fun position => (label.encode state).val.testBit position)
  dsimp only [WireAddress.bitIndex, Fin.rev]
  omega

private def firstBit (width : Nat) (index : Fin width) : EncodedBit (sourceEncoding width) :=
  prodLeftBit (VariableGidney.encoding width) (finIdentity (historyWidth width))
    (prodLeftBit (finIdentity width) (Accumulate.Gidney.encoding width)
      (finIdentityBit width index))

private def secondBit (width : Nat) (index : Fin width) : EncodedBit (sourceEncoding width) :=
  prodLeftBit (VariableGidney.encoding width) (finIdentity (historyWidth width))
    (prodRightBit (finIdentity width) (Accumulate.Gidney.encoding width)
      (prodLeftBit (finIdentity width) (finIdentity width) (finIdentityBit width index)))

private def targetBit (width : Nat) (index : Fin width) : EncodedBit (sourceEncoding width) :=
  prodLeftBit (VariableGidney.encoding width) (finIdentity (historyWidth width))
    (prodRightBit (finIdentity width) (Accumulate.Gidney.encoding width)
      (prodRightBit (finIdentity width) (finIdentity width) (finIdentityBit width index)))

private theorem first_wire (width : Nat) (index : Fin width) :
    (firstBit width index).wire.val = index.val := rfl

private theorem second_wire (width : Nat) (index : Fin width) :
    (secondBit width index).wire.val = width + index.val := rfl

private theorem target_wire (width : Nat) (index : Fin width) :
    (targetBit width index).wire.val = 2 * width + index.val := by
  change width + (width + index.val) = _
  omega

private theorem placed_read (width : Nat) (state : Frame width)
    (source : EncodedBit (sourceEncoding width)) (target : EncodedBit (frameEncoding width))
    (same : wires width source.wire = target.wire) :
    source.get ((placement width).grouping state) = target.get state := by
  rw [bit_read, bit_read]
  exact (grouping_bit width state source.wire).trans
    (congrArg (fun wire : Fin (frameEncoding width).width =>
      ((frameEncoding width).encode state).val.testBit wire.rev.val) same)

/-- The first grouped native word is exactly the actual X port, for arbitrary complete frames. -/
theorem grouping_input (width : Nat) (state : Frame width) :
    ((placement width).grouping state).1.1 = input width state := by
  apply word_ext
  intro index
  have wires : ProductPlacement.wires width (firstBit width index).wire =
      ((FramePorts.input width).bit index).wire := by
    apply Fin.ext
    rw [wires_address, first_wire, ProductWires.address_first, FramePorts.input_wire]
  have actual := placed_read width state (firstBit width index)
    ((FramePorts.input width).bit index) wires
  change (finIdentityBit width index).get ((placement width).grouping state).1.1 = _ at actual
  rw [bit_read] at actual
  exact actual.trans (readWord_bit (FramePorts.input width) state index).symm

/-- The second grouped native word is the already present Y port, with no extra register. -/
theorem grouping_numerator (width : Nat) (state : Frame width) :
    ((placement width).grouping state).1.2.1 = numerator width state := by
  apply word_ext
  intro index
  have wires : ProductPlacement.wires width (secondBit width index).wire =
      ((FramePorts.numerator width).bit index).wire := by
    apply Fin.ext
    rw [wires_address, second_wire, ProductWires.address_second, FramePorts.numerator_wire]
  have actual := placed_read width state (secondBit width index)
    ((FramePorts.numerator width).bit index) wires
  change (finIdentityBit width index).get ((placement width).grouping state).1.2.1 = _ at actual
  rw [bit_read] at actual
  exact actual.trans (readWord_bit (FramePorts.numerator width) state index).symm

/-- The grouped native target is exactly A's first n physical Work1 positions. -/
theorem grouping_accumulator (width : Nat) (state : Frame width) :
    ((placement width).grouping state).1.2.2 = accumulator width state := by
  apply word_ext
  intro index
  have wires : ProductPlacement.wires width (targetBit width index).wire =
      ((FramePorts.accumulator width).bit index).wire := by
    apply Fin.ext
    rw [wires_address, target_wire, ProductWires.address_target, FramePorts.accumulator_wire]
  have actual := placed_read width state (targetBit width index)
    ((FramePorts.accumulator width).bit index) wires
  change (finIdentityBit width index).get ((placement width).grouping state).1.2.2 = _ at actual
  rw [bit_read] at actual
  exact actual.trans (readWord_bit (FramePorts.accumulator width) state index).symm

/-- Read all six original padding bits and then every original length/control bit, in order. -/
def historyWire (width : Nat) (index : Fin (historyWidth width)) :
    Fin (frameEncoding width).width :=
  ⟨if index.val < 6 then width + index.val else 2 * width + index.val, by
    have bound := index.isLt
    rw [frame_width]
    unfold ProductWires.width historyWidth at *
    split_ifs <;> omega⟩

/-- The retained history is an independent physical read, not a definition through grouping. -/
def history (width : Nat) (state : Frame width) : Fin (2 ^ historyWidth width) :=
  BinaryBasis.bigEndianEquiv (historyWidth width) (fun index => finTwoEquiv.symm
    (((frameEncoding width).encode state).val.testBit (historyWire width index).rev.val))

private def historyBit (width : Nat) (index : Fin (historyWidth width)) :
    EncodedBit (sourceEncoding width) :=
  prodRightBit (VariableGidney.encoding width) (finIdentity (historyWidth width))
    (finIdentityBit (historyWidth width) index)

private theorem history_source_wire (width : Nat) (index : Fin (historyWidth width)) :
    (historyBit width index).wire.val = 3 * width + index.val := by
  change (width + (width + width)) + index.val = _
  omega

private theorem history_wire (width : Nat) (index : Fin (historyWidth width)) :
    wires width (historyBit width index).wire = historyWire width index := by
  apply Fin.ext
  rw [wires_address, history_source_wire]
  by_cases padding : index.val < 6
  · have actual := ProductWires.address_padding width (tailWidth width) ⟨index.val, padding⟩
    exact actual.trans (if_pos padding).symm
  · have bound := index.isLt
    let tail : Fin (tailWidth width) := ⟨index.val - 6, by unfold historyWidth at bound; omega⟩
    have actual := ProductWires.address_tail width (tailWidth width) tail
    have source : 3 * width + 6 + tail.val = 3 * width + index.val := by
      change 3 * width + 6 + (index.val - 6) = _
      omega
    rw [source] at actual
    change ProductWires.address width (tailWidth width) (3 * width + index.val) =
      if index.val < 6 then width + index.val else 2 * width + index.val
    rw [if_neg padding, actual]
    change 2 * width + 6 + (index.val - 6) = _
    omega

/-- Every retained grouped bit is the same actual padding/length/control bit of the old frame. -/
theorem grouping_history (width : Nat) (state : Frame width) :
    ((placement width).grouping state).2 = history width state := by
  apply word_ext
  intro index
  have actual := grouping_bit width state (historyBit width index).wire
  have read := bit_read (historyBit width index) ((placement width).grouping state)
  have source : (historyBit width index).get ((placement width).grouping state) =
      ((placement width).grouping state).2.val.testBit index.rev.val :=
    bit_read (finIdentityBit (historyWidth width) index) ((placement width).grouping state).2
  have joined := source.symm.trans (read.trans actual)
  rw [history_wire] at joined
  rw [history, BinaryBasis.bigEndianEquiv_bit, Equiv.apply_symm_apply]
  exact joined

/-- The supplied Y field agrees exactly with its complete physical word read. -/
theorem numerator_eq (width : Nat) (state : Frame width) : numerator width state = state.2 := by
  apply word_ext
  intro index
  exact (readWord_bit (FramePorts.numerator width) state index).trans
    (FramePorts.numerator_read width index state)

/-- The actual placed product preserves every retained history bit, jointly with all three words. -/
theorem product_history (width : Nat) (modulus : Fin (2 ^ width + 1)) (state : Frame width) :
    history width (NativeProductFrame.step width modulus state) = history width state := by
  rw [← grouping_history, ← grouping_history]
  have actual := (placement width).grouping.apply_symm_apply
    (VariableGidney.prefixOutput modulus width ((placement width).grouping state).1,
      ((placement width).grouping state).2)
  have projected := congrArg
    (fun value : VariableGidney.Registers width × Fin (2 ^ historyWidth width) => value.2) actual
  exact projected

end

end QuantumAlg.MeasuredUncompute.ProductReadout
