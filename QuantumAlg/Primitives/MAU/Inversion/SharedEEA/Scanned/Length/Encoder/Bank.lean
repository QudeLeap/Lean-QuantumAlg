/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Encoder.Frame
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.ManyDirty.Frame

/-!
# Borrow the other complete original work word for actual first-one tests

The bank is exactly existing Work1 or Work2, opposite the selected source.
Every bit is arbitrary and is restored by the complete native test. All
source, output and prefix separations are physical and value-independent.
No additional quantum system or clean full word is supplied.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthEncoder

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

/-- The entire opposite original word is an arbitrary restored bank, with unchanged wires. -/
def bank (width : Nat) (field : Field) (first : Bool) :
    (frame width field first).BorrowedBank (width + 3) where
  word := ⟨ArithmeticRotation.bit width (!first)⟩
  distinct := source_distinct width .divisor (!first)
  capacity := by omega
  sourceBank := by
    intro input borrowed same
    have values := congrArg Fin.val same
    change (ArithmeticRotation.bit width first
        (LengthAlignment.priorityIndex width field input)).wire.val =
      (ArithmeticRotation.bit width (!first) borrowed).wire.val at values
    rw [ArithmeticRotation.bit_value, ArithmeticRotation.bit_value] at values
    have inputFits := (LengthAlignment.priorityIndex width field input).isLt
    have bankFits := borrowed.isLt
    cases first <;>
      simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true] at values
      <;> omega
  outputBank := fun output borrowed =>
    (source_address width .divisor (!first) borrowed output.rev).symm
  stackBank := by
    intro stack borrowed
    change (SelectionFrame.stack width stack).wire ≠
      (ArithmeticRotation.bit width (!first) borrowed).wire
    unfold SelectionFrame.stack
    split
    · exact (source_flag width .divisor (!first) borrowed (SharedEEA.controlBit width)
        (by rw [SharedEEA.controlBit_wire]; omega)).symm
    · exact (source_prefix width .divisor (!first) borrowed _).symm

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthEncoder
