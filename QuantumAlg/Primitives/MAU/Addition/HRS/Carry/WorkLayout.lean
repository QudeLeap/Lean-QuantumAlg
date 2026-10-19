/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.Carry
import all QuantumAlg.Util.Nat.FixedWidth

/-!
# Separate the carry's internal borrowed word from its dirty output

The existing carry component packs its output above the `width - 2`
internally borrowed bits. This exact equivalence exposes those two fields
for wiring into the inactive high word and the sole external dirty bit
[HRS16, paper.tex:187-205,232-245]. No state is initialized by this layout.
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

/-- Exact packing of arbitrary borrowed bits below the dirty carry output. -/
def carryWorkEquiv (width : Nat) :
    (Fin (2 ^ (width - 2)) × Bool) ≃ Fin (2 ^ (width - 2 + 1)) :=
  (Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans
    ((Equiv.prodComm _ _).trans
      ((prodEquiv (m := 1) (n := width - 2)).trans
        (finCongr (congrArg (fun n : Nat => 2 ^ n) (Nat.add_comm 1 (width - 2))))))

/-- Low packed bits are precisely the internal borrowed word. -/
lemma hrsCarryWorkEquiv_borrowed (width : Nat)
    (borrowed : Fin (2 ^ (width - 2))) (dirty : Bool) (bit : Fin (width - 2)) :
    (carryWorkEquiv width (borrowed, dirty)).val.testBit bit.val =
      borrowed.val.testBit bit.val := by
  change (prodEquiv (m := 1) (n := width - 2)
    (finTwoEquiv.symm dirty, borrowed)).val.testBit bit.val = _
  exact prodEquiv_testBit_right _ _ bit

/-- The packed highest bit is precisely the arbitrary dirty output. -/
lemma hrsCarryWorkEquiv_dirty (width : Nat)
    (borrowed : Fin (2 ^ (width - 2))) (dirty : Bool) :
    (carryWorkEquiv width (borrowed, dirty)).val.testBit (width - 2) = dirty := by
  change (prodEquiv (m := 1) (n := width - 2)
    (finTwoEquiv.symm dirty, borrowed)).val.testBit (width - 2 + 0) = _
  exact (prodEquiv_testBit_left (m := 1) (n := width - 2)
    (finTwoEquiv.symm dirty) borrowed (0 : Fin 1)).trans (by cases dirty <;> rfl)

/-- The actual carry list preserves the borrowed field and xor-toggles only its output. -/
lemma hrsCarry_packed_step (width : Nat) (constant input : Fin (2 ^ width))
    (borrowed : Fin (2 ^ (width - 2))) (dirty : Bool) :
    EncodedBit.GateSpec.stepList (carryGates width constant)
        (input, carryWorkEquiv width (borrowed, dirty)) =
      (input, carryWorkEquiv width
        (borrowed, dirty ^^ decide (2 ^ width ≤ input.val + constant.val))) := by
  apply Prod.ext
  · exact hrsCarry_restores_input width constant _
  · apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    by_cases hbit : bit.val < width - 2
    · have h := hrsCarry_restores_borrowed width constant
        ⟨bit.val, hbit⟩ (input, carryWorkEquiv width (borrowed, dirty))
      have hread := hrsCarryWorkEquiv_borrowed width borrowed dirty ⟨bit.val, hbit⟩
      have hwrite := hrsCarryWorkEquiv_borrowed width borrowed
        (dirty ^^ decide (2 ^ width ≤ input.val + constant.val)) ⟨bit.val, hbit⟩
      exact h.trans (hread.trans hwrite.symm)
    · have hlast : bit.val = width - 2 := by have := bit.isLt; omega
      rw [hlast]
      have h := hrsCarry_output_get width constant
        (input, carryWorkEquiv width (borrowed, dirty))
      change (EncodedBit.GateSpec.stepList (carryGates width constant)
          (input, carryWorkEquiv width (borrowed, dirty))).2.val.testBit
          (WireAddress.bitIndex (WireAddress.littleEndianWire
            (⟨width - 2, by omega⟩ : Fin (width - 2 + 1)))).val =
        ((carryOutputBit width).get (input, carryWorkEquiv width (borrowed, dirty)) ^^
          decide (2 ^ width ≤ input.val + constant.val)) at h
      rw [WireAddress.bitIndex_littleEndianWire] at h
      rw [carryOutputBit, hrsCarryWorkBit_get, hrsCarryWorkEquiv_dirty] at h
      exact h.trans (hrsCarryWorkEquiv_dirty width borrowed _).symm

/-- The already compiled carry program has the same exact packed endpoint. -/
lemma hrsCarry_packed_apply (width : Nat) (constant input : Fin (2 ^ width))
    (borrowed : Fin (2 ^ (width - 2))) (dirty : Bool) :
    (carryProgram width constant).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (carryEncoding width).width).basisEquiv.symm
            ((carryEncoding width).encode
              (input, carryWorkEquiv width (borrowed, dirty))))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (carryEncoding width).width).basisEquiv.symm
          ((carryEncoding width).encode
            (input, carryWorkEquiv width
              (borrowed, dirty ^^ decide (2 ^ width ≤ input.val + constant.val))))) := by
  have hstep := hrsCarry_packed_step width constant input borrowed dirty
  rw [hrsCarry_step] at hstep
  simpa only [hstep] using (hrsCarry_realizes width constant).apply_encoded_ket
    (input, carryWorkEquiv width (borrowed, dirty))

end

end QuantumAlg.MAU.Addition.HRS
