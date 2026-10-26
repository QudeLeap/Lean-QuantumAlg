/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Placement
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Readout

/-! # Generic finite-word readouts of the complete two-word physical grouping -/

namespace QuantumAlg.MAU.Addition.TTK.WordPlacement

noncomputable section

open EncodedBit

variable {Data : Type} {frame : BinaryLabelEncoding Data} {width : Nat}
    (placement : WordPlacement frame width)
    (sourceOnto : Function.Surjective (encoding width).encode)
    (targetOnto : Function.Surjective frame.encode)

/-- The whole selected first word follows from its original physical bit readouts. -/
lemma grouped_addend_fin (state : Data) (value : Fin (2 ^ width))
    (reads : ∀ index, (placement.addend.bit index).get state =
      (BitVec.ofFin value).getMsbD index.val) :
    ((placement.subsystem.full sourceOnto targetOnto).grouping state).1.1 = value :=
  congrArg BitVec.toFin (placement.grouped_addend state (BitVec.ofFin value) reads)

/-- The whole selected second word follows without normalizing a concrete exponential basis. -/
lemma grouped_target_fin (state : Data) (value : Fin (2 ^ width))
    (reads : ∀ index, (placement.target.bit index).get state =
      (BitVec.ofFin value).getMsbD index.val) :
    ((placement.subsystem.full sourceOnto targetOnto).grouping state).1.2 = value :=
  congrArg BitVec.toFin (placement.grouped_target state (BitVec.ofFin value) reads)

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)
    (whole : FullPlacement (.prod (encoding width) saved) frame)

/-- Read the first word through a supplied full layout and literal physical wire certificates. -/
lemma grouped_addend_fin_of_wires
    (locations : ∀ index,
      (whole.placeBit (BinaryLabelEncoding.prodLeftBit (encoding width) saved
        (firstLens index))).wire = (placement.addend.bit index).wire)
    (state : Data) (value : Fin (2 ^ width))
    (reads : ∀ index, (placement.addend.bit index).get state =
      (BitVec.ofFin value).getMsbD index.val) :
    (whole.grouping state).1.1 = value := by
  apply whole.read_fin_of_placeBit_wires (fun pair => pair.1.1)
    (fun index => BinaryLabelEncoding.prodLeftBit (encoding width) saved (firstLens index))
    placement.addend.bit _ locations state value reads
  intro sourceState index
  exact fin_bit_get index sourceState.1.1

/-- Read the second word without constructing or converting a second semantic grouping. -/
lemma grouped_target_fin_of_wires
    (locations : ∀ index,
      (whole.placeBit (BinaryLabelEncoding.prodLeftBit (encoding width) saved
        (secondLens index))).wire = (placement.target.bit index).wire)
    (state : Data) (value : Fin (2 ^ width))
    (reads : ∀ index, (placement.target.bit index).get state =
      (BitVec.ofFin value).getMsbD index.val) :
    (whole.grouping state).1.2 = value := by
  apply whole.read_fin_of_placeBit_wires (fun pair => pair.1.2)
    (fun index => BinaryLabelEncoding.prodLeftBit (encoding width) saved (secondLens index))
    placement.target.bit _ locations state value reads
  intro sourceState index
  exact fin_bit_get index sourceState.1.2

end

end QuantumAlg.MAU.Addition.TTK.WordPlacement
