/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Window

/-!
# Literal native TTK gates at the streamed source positions

Each original TTK sum, operand-chain, and carry primitive maps to exactly
the physical source gate used by the moving-flag stream. Both its kind and
its complete ordered operands are retained. This is gate placement, with
no executed word permutation [TTK09, qic-loglogaddition-quant.tex:285-318].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticWindow

noncomputable section

open EncodedBit NumberTheory.SharedEEA ArithmeticTemplate

/-- Relocate one original native TTK instruction to its exact existing operand wires. -/
def mapGate (width length : Nat) (fits : length ≤ width + 3)
    (gate : GateSpec (Addition.TTK.encoding length)) : GateSpec (Scanned.encoding width) :=
  (placement width length fits).subsystem.placeGate (source_onto length)
    (Scanned.encoding_surjective width) gate

/-- The original sum CNOT is exactly the literal streamed sum CNOT at that source index. -/
lemma map_sumGate (width length : Nat) (fits : length ≤ width + 3) (index : Fin length) :
    mapGate width length fits
      (.cnot (Addition.TTK.leftBit length index) (Addition.TTK.rightBit length index)
        (Addition.TTK.ttkLeftRight_disjoint length index index)) =
      (sumGate width ⟨index.val, lt_of_lt_of_le index.isLt fits⟩).val := by
  change GateSpec.cnot
      ((placement width length fits).subsystem.placeBit (source_onto length)
        (Scanned.encoding_surjective width) (Addition.TTK.leftBit length index))
      ((placement width length fits).subsystem.placeBit (source_onto length)
        (Scanned.encoding_surjective width) (Addition.TTK.rightBit length index)) _ = _
  congr 1
  · exact placed_leftBit width length fits index
  · exact placed_rightBit width length fits index

private def before (length : Nat) (index : Fin length) : Fin length :=
  ⟨index.val - 1, by have := index.isLt; omega⟩

private lemma before_ne (length : Nat) (index : Fin length) (positive : 0 < index.val) :
    before length index ≠ index := by
  intro same
  have values := congrArg Fin.val same
  change index.val - 1 = index.val at values
  omega

/-- The original operand-chain CNOT retains the same previous and current physical positions. -/
lemma map_chainGate (width length : Nat) (fits : length ≤ width + 3) (index : Fin length)
    (positive : 0 < index.val) :
    mapGate width length fits
      (.cnot (Addition.TTK.leftBit length (before length index))
        (Addition.TTK.leftBit length index)
        (Addition.TTK.ttkLeftLeft_disjoint length _ _ (before_ne length index positive))) =
      (chainGate width ⟨index.val, lt_of_lt_of_le index.isLt fits⟩ positive).val := by
  change GateSpec.cnot
      ((placement width length fits).subsystem.placeBit (source_onto length)
        (Scanned.encoding_surjective width) (Addition.TTK.leftBit length (before length index)))
      ((placement width length fits).subsystem.placeBit (source_onto length)
        (Scanned.encoding_surjective width) (Addition.TTK.leftBit length index)) _ = _
  congr 1
  · exact placed_leftBit width length fits (before length index)
  · exact placed_leftBit width length fits index

/-- All three original carry positions agree with the actual streamed Toffoli. -/
lemma map_carryGate (width length : Nat) (fits : length ≤ width + 3) (index : Fin length)
    (positive : 0 < index.val) :
    mapGate width length fits
      (.toffoli (Addition.TTK.rightBit length (before length index))
        (Addition.TTK.leftBit length (before length index)) (Addition.TTK.leftBit length index)
        (Addition.TTK.ttkLeftRight_disjoint length _ _).symm
        (Addition.TTK.ttkLeftRight_disjoint length _ _).symm
        (Addition.TTK.ttkLeftLeft_disjoint length _ _ (before_ne length index positive))) =
      (carryGate width ⟨index.val, lt_of_lt_of_le index.isLt fits⟩ positive).val := by
  change GateSpec.toffoli
      ((placement width length fits).subsystem.placeBit (source_onto length)
        (Scanned.encoding_surjective width) (Addition.TTK.rightBit length (before length index)))
      ((placement width length fits).subsystem.placeBit (source_onto length)
        (Scanned.encoding_surjective width) (Addition.TTK.leftBit length (before length index)))
      ((placement width length fits).subsystem.placeBit (source_onto length)
        (Scanned.encoding_surjective width) (Addition.TTK.leftBit length index)) _ _ _ = _
  congr 1
  · exact placed_rightBit width length fits (before length index)
  · exact placed_leftBit width length fits (before length index)
  · exact placed_leftBit width length fits index

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticWindow
