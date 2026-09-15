/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Product.Readout
import all QuantumAlg.Primitives.MeasuredUncompute.WorkspaceReuse

/-!
# Exact product words after the actual workspace reuse placement

The existing wire bijection exchanges the roles of A and Y while X and
all six padding bits and small fields remain at their original identities.
The complete word equalities below follow from these actual coordinates,
including arbitrary dirty values and all retained history
[LYL+26, sec_point_add/sec_point_add.tex:75-105]. They describe readout of
the real placement, not an extra free SWAP operation or idealized grouping.
-/

namespace QuantumAlg.MeasuredUncompute.ReusedProductReadout

noncomputable section

open ProductPlacement MAU.Inversion

private theorem encoded_bit (width : Nat) (state : Frame width)
    (index : Fin (frameEncoding width).width) :
    ((frameEncoding width).encode ((WorkspaceReuse.placement width).grouping state)).val.testBit
        index.rev.val =
      ((frameEncoding width).encode state).val.testBit
        (WorkspaceReuse.wires width index).rev.val := by
  have actual := EncodedBit.FullPlacement.wireBasis_bit
    (frameEncoding width) (frameEncoding width) (WorkspaceReuse.wires width)
    ((frameEncoding width).encode ((WorkspaceReuse.placement width).grouping state)) index
  have encoded := (WorkspaceReuse.placement width).basis_encode state
  change EncodedBit.FullPlacement.wireBasis _ _ (WorkspaceReuse.wires width)
    ((frameEncoding width).encode ((WorkspaceReuse.placement width).grouping state)) = _ at encoded
  rw [encoded] at actual
  exact actual.symm

private theorem bit_read (width : Nat) (state : Frame width)
    (source target : EncodedBit (frameEncoding width))
    (same : WorkspaceReuse.wires width source.wire = target.wire) :
    source.get ((WorkspaceReuse.placement width).grouping state) = target.get state := by
  rw [ProductReadout.bit_read, ProductReadout.bit_read]
  exact (encoded_bit width state source.wire).trans
    (congrArg (fun wire : Fin (frameEncoding width).width =>
      ((frameEncoding width).encode state).val.testBit wire.rev.val) same)

private theorem input_wire (width : Nat) (index : Fin width) :
    WorkspaceReuse.wires width ((FramePorts.input width).bit index).wire =
      ((FramePorts.input width).bit index).wire := by
  apply Fin.ext
  change WorkspaceReuse.address width ((FramePorts.input width).bit index).wire.val = _
  rw [FramePorts.input_wire]
  apply WorkspaceReuse.address_retained
  · omega
  · have bound := index.isLt
    rw [SharedEEA.encoding_width]
    omega

private theorem accumulator_wire (width : Nat) (index : Fin width) :
    WorkspaceReuse.wires width ((FramePorts.accumulator width).bit index).wire =
      ((FramePorts.numerator width).bit index).wire := by
  apply Fin.ext
  change WorkspaceReuse.address width index.val = (SharedEEA.encoding width).width + index.val
  exact WorkspaceReuse.address_accumulator width index

private theorem numerator_wire (width : Nat) (index : Fin width) :
    WorkspaceReuse.wires width ((FramePorts.numerator width).bit index).wire =
      ((FramePorts.accumulator width).bit index).wire := by
  apply Fin.ext
  change WorkspaceReuse.address width ((SharedEEA.encoding width).width + index.val) = index.val
  exact WorkspaceReuse.address_numerator width index

/-- X remains the identical complete word under the actual workspace-role exchange. -/
theorem input (width : Nat) (state : Frame width) :
    ProductReadout.input width ((WorkspaceReuse.placement width).grouping state) =
      ProductReadout.input width state := by
  apply ProductReadout.word_ext
  intro index
  simp only [ProductReadout.input, ProductReadout.readWord_bit]
  exact bit_read width state _ _ (input_wire width index)

/-- The source A role reads the complete existing Y value. -/
theorem accumulator (width : Nat) (state : Frame width) :
    ProductReadout.accumulator width ((WorkspaceReuse.placement width).grouping state) =
      ProductReadout.numerator width state := by
  apply ProductReadout.word_ext
  intro index
  simp only [ProductReadout.accumulator, ProductReadout.numerator, ProductReadout.readWord_bit]
  exact bit_read width state _ _ (accumulator_wire width index)

/-- The source Y role reads the complete saved A value. -/
theorem numerator (width : Nat) (state : Frame width) :
    ProductReadout.numerator width ((WorkspaceReuse.placement width).grouping state) =
      ProductReadout.accumulator width state := by
  apply ProductReadout.word_ext
  intro index
  simp only [ProductReadout.numerator, ProductReadout.accumulator, ProductReadout.readWord_bit]
  exact bit_read width state _ _ (numerator_wire width index)

private theorem history_wire (width : Nat) (index : Fin (historyWidth width)) :
    WorkspaceReuse.wires width (ProductReadout.historyWire width index) =
      ProductReadout.historyWire width index := by
  apply Fin.ext
  change WorkspaceReuse.address width (ProductReadout.historyWire width index).val = _
  apply WorkspaceReuse.address_retained
  · change width ≤ if index.val < 6 then width + index.val else 2 * width + index.val
    split_ifs <;> omega
  · have bound := index.isLt
    rw [SharedEEA.encoding_width]
    change (if index.val < 6 then width + index.val else 2 * width + index.val) < _
    unfold historyWidth tailWidth at bound
    split_ifs <;> omega

/-- Every retained padding, length, and control value survives the actual role exchange. -/
theorem history (width : Nat) (state : Frame width) :
    ProductReadout.history width ((WorkspaceReuse.placement width).grouping state) =
      ProductReadout.history width state := by
  apply ProductReadout.word_ext
  intro index
  simp only [ProductReadout.history, BinaryBasis.bigEndianEquiv_bit, Equiv.apply_symm_apply]
  exact (encoded_bit width state (ProductReadout.historyWire width index)).trans
    (congrArg (fun wire : Fin (frameEncoding width).width =>
      ((frameEncoding width).encode state).val.testBit wire.rev.val) (history_wire width index))

/-- The actual product source after reuse is X/A/Y, with the exact entire history retained. -/
theorem grouping_words (width : Nat) (state : Frame width) :
    (ProductPlacement.placement width).grouping
        ((WorkspaceReuse.placement width).grouping state) =
      ((ProductReadout.input width state, ProductReadout.accumulator width state,
        ProductReadout.numerator width state), ProductReadout.history width state) := by
  apply Prod.ext
  · apply Prod.ext
    · exact (ProductReadout.grouping_input width _).trans (input width state)
    · exact Prod.ext
        ((ProductReadout.grouping_numerator width _).trans (numerator width state))
        ((ProductReadout.grouping_accumulator width _).trans (accumulator width state))
  · exact (ProductReadout.grouping_history width _).trans (history width state)

/-- The inverse grouping also retains X; this follows from the actual equivalence's round trip. -/
theorem input_symm (width : Nat) (state : Frame width) :
    ProductReadout.input width ((WorkspaceReuse.placement width).grouping.symm state) =
      ProductReadout.input width state := by
  have actual := input width ((WorkspaceReuse.placement width).grouping.symm state)
  rw [Equiv.apply_symm_apply] at actual
  exact actual.symm

/-- The inverse grouping's A port contains the full original Y word. -/
theorem accumulator_symm (width : Nat) (state : Frame width) :
    ProductReadout.accumulator width ((WorkspaceReuse.placement width).grouping.symm state) =
      ProductReadout.numerator width state := by
  have actual := numerator width ((WorkspaceReuse.placement width).grouping.symm state)
  rw [Equiv.apply_symm_apply] at actual
  exact actual.symm

/-- The inverse grouping's Y port contains the full original A word. -/
theorem numerator_symm (width : Nat) (state : Frame width) :
    ProductReadout.numerator width ((WorkspaceReuse.placement width).grouping.symm state) =
      ProductReadout.accumulator width state := by
  have actual := accumulator width ((WorkspaceReuse.placement width).grouping.symm state)
  rw [Equiv.apply_symm_apply] at actual
  exact actual.symm

/-- The inverse grouping retains every small history coordinate as well. -/
theorem history_symm (width : Nat) (state : Frame width) :
    ProductReadout.history width ((WorkspaceReuse.placement width).grouping.symm state) =
      ProductReadout.history width state := by
  have actual := history width ((WorkspaceReuse.placement width).grouping.symm state)
  rw [Equiv.apply_symm_apply] at actual
  exact actual.symm

end

end QuantumAlg.MeasuredUncompute.ReusedProductReadout
