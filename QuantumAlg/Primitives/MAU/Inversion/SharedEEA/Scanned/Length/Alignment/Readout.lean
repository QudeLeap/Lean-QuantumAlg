/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Alignment.Positions
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Length.Read
import all QuantumAlg.Util.Nat.FixedWidth.PriorityPrefix

/-!
# Exact clipped priority prefix of the actual aligned physical word

The complete first-one input uses static original wire positions. Its
initial selected prefix is exactly the original source length-read word,
including an empty region. Numeric first-one clipping is a pure readout
identity; native encoding, range tests, writes and cleanup remain separate.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthAlignment

noncomputable section

open EncodedBit LengthCoordinates

/-- Literal original systems in the required priority order, without an executed reflection. -/
def source (width : Nat) (field : Field) (first : Bool) :
    Word (encoding width) (width + 3) :=
  ⟨fun index => ArithmeticRotation.bit width first (priorityIndex width field index)⟩

/-- Mathematical complete-word readout of those same original source positions. -/
def word (width : Nat) (field : Field) (first : Bool) (state : Data width) :
    BitVec (width + 3) :=
  (BitVec.ofBoolListBE
    (List.ofFn fun index => ((source width field first).bit index).get state)).cast
      List.length_ofFn

/-- The complete readout retains every physical source bit in its declared priority order. -/
lemma word_get (width : Nat) (field : Field) (first : Bool) (state : Data width)
    (index : Fin (width + 3)) :
    (word width field first state).getMsbD index.val =
      (ArithmeticRotation.bit width first (priorityIndex width field index)).get state := by
  rw [word, BitVec.getMsbD_cast, BitVec.getMsbD_ofBoolListBE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos index.isLt]
  rfl

/-- Every selected prefix bit agrees with the original finite arithmetic read. -/
lemma selected_get (width : Nat) (field : Field) (first : Bool) (state : Data width)
    (index : Fin (region width field (boundaryValue field state.1))) :
    (word width field first (GateSpec.stepList (gates width field first) state)).getMsbD
        index.val =
      (LengthRead.readWord width field (boundaryValue field state.1)
        (LengthRead.sourceWord first state.1)).getMsbD index.val := by
  rw [word_get width field first _
    ⟨index.val, index.isLt.trans_le (region_le width field _)⟩, gates_selected_get]
  have actual := LengthRead.payloadBit_get width field (boundaryValue field state.1)
    first index state.1
  cases first <;> exact actual

/-- The actual aligned prefix is exactly the original source region, including the empty case. -/
lemma prefix_eq_original (width : Nat) (field : Field) (first : Bool) (state : Data width) :
    (word width field first (GateSpec.stepList (gates width field first) state)).extractLsb'
        (width + 3 - region width field (boundaryValue field state.1))
        (region width field (boundaryValue field state.1)) =
      LengthRead.readWord width field (boundaryValue field state.1)
        (LengthRead.sourceWord first state.1) := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have bound := region_le width field (boundaryValue field state.1)
  have joined : width + 3 - region width field (boundaryValue field state.1) +
      region width field (boundaryValue field state.1) = width + 3 := by omega
  have sourceWithin : width + 3 - index ≤ width + 3 := Nat.sub_le _ _
  have sourceIndex : width + 3 - (width + 3 - index) = index := by omega
  simp only [BitVec.getMsbD_extractLsb', joined, within, sourceWithin, sourceIndex,
    decide_true, Bool.true_and]
  exact selected_get width field first state ⟨index, within⟩

/-- Clipping the complete first-one position gives exactly the original region's natural size. -/
lemma clipped_size (width : Nat) (field : Field) (first : Bool) (state : Data width) :
    (LengthRead.readWord width field (boundaryValue field state.1)
      (LengthRead.sourceWord first state.1)).toNat.size =
        region width field (boundaryValue field state.1) -
          NatFixedWidth.PriorityPrefix.firstOne
            (word width field first (GateSpec.stepList (gates width field first) state)) := by
  rw [← prefix_eq_original]
  exact NatFixedWidth.PriorityPrefix.prefix_size _ _ (region_le width field _)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthAlignment
