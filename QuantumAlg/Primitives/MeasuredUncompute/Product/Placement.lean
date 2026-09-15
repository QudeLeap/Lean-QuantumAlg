/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Product.Wires
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Registers
import all QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.WordAction
import all QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.Program
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement

/-!
# Three native product words in the actual shared-EEA frame

The original two shared words and the existing Y word contain all
three arithmetic ports. An explicit physical permutation groups X,
Y, A for the existing variable product and preserves every other bit.
Both the complete field grouping and binary basis transport come from
that same wire map [LYL+26, sec_point_add/sec_point_add.tex:51-105].
-/

namespace QuantumAlg.MeasuredUncompute.ProductPlacement

noncomputable section

open MAU.Inversion MAU.Multiplication

/-- Original shared EEA fields followed by the existing numerator/product word. -/
abbrev Frame (width : Nat) := SharedEEA.Registers width × Fin (2 ^ width)

/-- Four actual finite length words and the five original controls. -/
def tailWidth (width : Nat) : Nat := 4 * width.size + 5

/-- The same retained fields plus the six padding bits inside the two shared words. -/
def historyWidth (width : Nat) : Nat := 6 + tailWidth width

/-- Every actual original wire is encoded in its existing shared-frame order. -/
def frameEncoding (width : Nat) : BinaryLabelEncoding (Frame width) :=
  BinaryLabelEncoding.prod (SharedEEA.encoding width) (BinaryLabelEncoding.finIdentity width)

/-- The product reads X/Y/A before the complete unchanged small frame. -/
def sourceEncoding (width : Nat) :
    BinaryLabelEncoding (VariableGidney.Registers width × Fin (2 ^ historyWidth width)) :=
  BinaryLabelEncoding.prod (VariableGidney.encoding width)
    (BinaryLabelEncoding.finIdentity (historyWidth width))

theorem frame_width (width : Nat) :
    (frameEncoding width).width = ProductWires.width width (tailWidth width) := by
  change (SharedEEA.encoding width).width + width = _
  rw [SharedEEA.encoding_width]
  unfold ProductWires.width tailWidth
  omega

theorem source_width (width : Nat) :
    (sourceEncoding width).width = ProductWires.width width (tailWidth width) := by
  change (width + (width + width)) + historyWidth width = _
  unfold ProductWires.width historyWidth
  omega

private theorem frame_total (width : Nat) :
    Function.Surjective (frameEncoding width).encode := by
  intro label
  obtain ⟨⟨shared, numerator⟩, rfl⟩ :=
    (prodEquiv (m := (SharedEEA.encoding width).width) (n := width)).surjective label
  obtain ⟨state, rfl⟩ := SharedEEA.encoding_surjective width shared
  exact ⟨(state, numerator), rfl⟩

private theorem source_total (width : Nat) :
    Function.Surjective (sourceEncoding width).encode := by
  intro label
  obtain ⟨⟨product, retained⟩, rfl⟩ :=
    (prodEquiv (m := (VariableGidney.encoding width).width)
      (n := historyWidth width)).surjective label
  obtain ⟨state, rfl⟩ := (VariableGidney.wordLabelEquiv width).surjective product
  exact ⟨(state, retained), rfl⟩

/-- Exact actual wire positions, with only natural-width transports at the two encodings. -/
def wires (width : Nat) : Fin (sourceEncoding width).width ≃ Fin (frameEncoding width).width :=
  (finCongr (source_width width)).trans
    ((ProductWires.permutation width (tailWidth width)).trans (finCongr (frame_width width).symm))

/-- The complete basis and grouping are both determined by these same original physical wires. -/
def placement (width : Nat) :
    EncodedBit.FullPlacement (sourceEncoding width) (frameEncoding width) :=
  EncodedBit.FullPlacement.ofWires _ _ (source_total width) (frame_total width) (wires width)

/-- Each grouped source position names precisely its proved physical product port. -/
theorem wires_address (width : Nat) (index : Fin (sourceEncoding width).width) :
    (wires width index).val = ProductWires.address width (tailWidth width) index.val := rfl

/-- Every source bit reads the actual original target-frame wire, for arbitrary complete fields. -/
theorem grouping_bit (width : Nat) (state : Frame width)
    (index : Fin (sourceEncoding width).width) :
    ((sourceEncoding width).encode ((placement width).grouping state)).val.testBit index.rev.val =
      ((frameEncoding width).encode state).val.testBit (wires width index).rev.val := by
  have actual := EncodedBit.FullPlacement.wireBasis_bit
    (sourceEncoding width) (frameEncoding width) (wires width)
    ((sourceEncoding width).encode ((placement width).grouping state)) index
  have encoded := (placement width).basis_encode state
  change EncodedBit.FullPlacement.wireBasis _ _ (wires width)
    ((sourceEncoding width).encode ((placement width).grouping state)) = _ at encoded
  rw [encoded] at actual
  exact actual.symm

end

end QuantumAlg.MeasuredUncompute.ProductPlacement
