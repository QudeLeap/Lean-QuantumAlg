/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Clean
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Support

/-!
# Physical support of the literal clean-low native carry word

Omitting the inactive low descending row introduces no new gate or physical
address. In particular the original high flag is excluded from the complete
lower uncomputation, including its reversed native execution
[G25, main.tex:253-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- Every emitted clean-low native gate is one of the same original native carry gates. -/
lemma cleanLowGates_mem : ∀ {length : Nat} (layout : CarryLayout encoding length)
    (constant : BitVec length) (gate : GateSpec encoding),
    gate ∈ layout.cleanLowGates constant → gate ∈ layout.gates constant := by
  intro length
  induction length with
  | zero => intro layout constant gate present; simp [cleanLowGates] at present
  | succ length ih =>
      intro layout constant gate present
      by_cases positive : 0 < length
      · rw [cleanLowGates, dif_pos positive] at present
        rw [gates, dif_pos positive]
        simp only [List.mem_append] at present ⊢
        rcases present with ((descending | lower) | offset) | ascending
        · have original : gate ∈ layout.descendingTop constant positive := by
            by_cases upper : 1 < length
            · simpa only [if_pos upper] using descending
            · simp only [if_neg upper, List.not_mem_nil] at descending
          exact Or.inl (Or.inl (Or.inl original))
        · exact Or.inl (Or.inl (Or.inr (ih _ _ _ lower)))
        · exact Or.inl (Or.inr offset)
        · exact Or.inr ascending
      · simpa only [cleanLowGates, gates, dif_neg positive] using present

/-- Every read and write of the clean-low native word lies in the original carry interface. -/
lemma cleanLowGates_bitDisjoint {length : Nat} (layout : CarryLayout encoding length)
    (constant : BitVec length) (observed : EncodedBit encoding)
    (controlOutside : layout.control.wire ≠ observed.wire)
    (sourceOutside : ∀ index, (layout.source index).wire ≠ observed.wire)
    (outputOutside : ∀ index, (layout.output index).wire ≠ observed.wire) :
    ∀ gate ∈ layout.cleanLowGates constant, bitDisjoint observed gate := by
  intro gate present
  exact gates_bitDisjoint layout constant observed controlOutside sourceOutside outputOutside
    gate (cleanLowGates_mem layout constant gate present)

/-- The reversed lower native word commutes with the flip of any excluded original system. -/
lemma cleanLowGates_reverse_flip_comm {length : Nat} (layout : CarryLayout encoding length)
    (constant : BitVec length) (observed : EncodedBit encoding)
    (controlOutside : layout.control.wire ≠ observed.wire)
    (sourceOutside : ∀ index, (layout.source index).wire ≠ observed.wire)
    (outputOutside : ∀ index, (layout.output index).wire ≠ observed.wire) (state : Data) :
    stepList (layout.cleanLowGates constant).reverse (observed.flip state) =
      observed.flip (stepList (layout.cleanLowGates constant).reverse state) := by
  apply stepList_flip_comm_of_bitDisjoint
  intro gate present
  exact cleanLowGates_bitDisjoint layout constant observed controlOutside sourceOutside
    outputOutside gate (List.mem_reverse.mp present)

end

end QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout
