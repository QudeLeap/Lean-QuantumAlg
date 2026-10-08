/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Frame.Swap
import all QuantumAlg.Primitives.MeasuredUncompute.Product.PortLaws
import all QuantumAlg.Primitives.MeasuredUncompute.ReusedProduct.Readout
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Arithmetic

/-!
# Complete frame action of the literal final A/Y swap

The existing three-CNOT-per-bit program exchanges A and Y and leaves X
and every retained padding/history bit unchanged. Its full basis action
therefore equals the already proved coordinate exchange, with no missing
complementary state [LYL+26, sec_point_add/sec_point_add.tex:101-105].
The equality below proves the actual emitted swap gates; it does not
assign a free operation to the workspace placement used for earlier gates.
-/

namespace QuantumAlg.MeasuredUncompute.FrameSwapReadout

noncomputable section

open ProductPlacement ProductReadout MAU.Inversion

private def historyBit (width : Nat) (index : Fin (historyWidth width)) :
    EncodedBit (frameEncoding width) where
  wire := historyWire width index
  get state := ((frameEncoding width).encode state).val.testBit
    (WireAddress.bitIndex (historyWire width index)).val
  flip state := (Equiv.ofBijective (frameEncoding width).encode
    ⟨(frameEncoding width).encode_injective, frame_total width⟩).symm
      (WireAddress.flipBit (historyWire width index) ((frameEncoding width).encode state))
  get_eq _ := rfl
  encode_flip _state :=
    (Equiv.ofBijective (frameEncoding width).encode
      ⟨(frameEncoding width).encode_injective, frame_total width⟩).apply_symm_apply _

private theorem history_unchanged (width : Nat) (state : Frame width) :
    history width (FrameSwap.step width state) = history width state := by
  apply word_ext
  intro index
  simp only [history, BinaryBasis.bigEndianEquiv_bit, Equiv.apply_symm_apply]
  have actual := FrameSwap.frameSwap_other width (historyBit width index)
    (fun selected => by
      intro same
      have values := congrArg (fun wire : Fin (frameEncoding width).width => wire.val) same
      rw [FramePorts.accumulator_wire] at values
      have within := selected.isLt
      change selected.val =
        if index.val < 6 then width + index.val else 2 * width + index.val at values
      split_ifs at values <;> omega)
    (fun selected => by
      intro same
      have values := congrArg (fun wire : Fin (frameEncoding width).width => wire.val) same
      have within := InPlaceArithmetic.history_before_numerator width index
      change (SharedEEA.encoding width).width + selected.val =
        (historyWire width index).val at values
      omega) state
  rw [bit_read, bit_read] at actual
  exact actual

/-- Every complete frame undergoes exactly the actual A/Y coordinate exchange. -/
theorem step_eq_grouping (width : Nat) (state : Frame width) :
    FrameSwap.step width state = (WorkspaceReuse.placement width).grouping state := by
  apply ProductPortLaws.frame_ext
  · rw [ReusedProductReadout.input]
    apply word_ext
    intro index
    simp only [input, readWord_bit]
    exact FrameSwap.frameSwap_input width index state
  · rw [ReusedProductReadout.numerator]
    apply word_ext
    intro index
    simp only [numerator, accumulator, readWord_bit]
    exact FrameSwap.frameSwap_numerator width index state
  · rw [ReusedProductReadout.accumulator]
    apply word_ext
    intro index
    simp only [accumulator, numerator, readWord_bit]
    exact FrameSwap.frameSwap_accumulator width index state
  · exact (history_unchanged width state).trans (ReusedProductReadout.history width state).symm

/-- The real final gates undo the earlier workspace-role exchange on every complete label. -/
theorem program_reused_ket (width : Nat) (state : Frame width) :
    (FrameSwap.program width).applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical (frameEncoding width).width).basisEquiv.symm
            ((frameEncoding width).encode
              ((WorkspaceReuse.placement width).grouping.symm state)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding width).width).basisEquiv.symm
          ((frameEncoding width).encode state)) := by
  have actual := (FrameSwap.frameSwap_realizes width).apply_encoded_ket
    ((WorkspaceReuse.placement width).grouping.symm state)
  rw [step_eq_grouping, Equiv.apply_symm_apply] at actual
  exact actual

end

end QuantumAlg.MeasuredUncompute.FrameSwapReadout
