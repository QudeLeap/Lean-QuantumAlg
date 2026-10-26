/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Preparation.Count

/-!
# Total native seed-loader bound of the same complete measured physical frame

The total residue `1 % N` is zero or one. Its actual source ports therefore
contain at most one true bit, even at zero width or modulus zero/one. This
bound concerns the independent total parameter formula; the factoring
execution retains its original `N>1` input domain [G25, main.tex:271-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open MAU.Multiplication.Gidney.Measured

private lemma seed_true_source (width N : Nat) (port : Port width)
    (selected : ((Physical.layout width).bit port).get (seedLabel width N) = true) :
    ∃ index : Fin width, port = .inr (.inl index) ∧ index.val = 0 := by
  rw [seedLabel, Physical.cleanLabel, Physical.label_bit] at selected
  cases port with
  | inl control => cases control; cases selected
  | inr remainder =>
      cases remainder with
      | inl index =>
          simp only [BitVec.getLsbD_ofNat, index.isLt, decide_true, Bool.true_and] at selected
          have residue : 1 % N = 0 ∨ 1 % N = 1 := by
            have bounded := Nat.mod_le 1 N
            omega
          rcases residue with zero | one
          · rw [zero, Nat.zero_testBit] at selected
            cases selected
          · rw [one] at selected
            exact ⟨index, rfl, Nat.testBit_one_eq_true_iff_self_eq_zero.mp selected⟩
      | inr _ => cases selected

/-- Every total parameter branch of the actual literal loader contains at most one native X. -/
lemma measuredSeed_xCount_le_one (width N : Nat) :
    EncodedBit.Word.BasisLoad.xCount (seedLabel width N) ≤ 1 := by
  rw [EncodedBit.Word.BasisLoad.xCount, ← List.toFinset_card_of_nodup
    (EncodedBit.Word.constantOneIndices_nodup (seedLabel width N))]
  apply Finset.card_le_one.mpr
  intro left leftMember right rightMember
  have leftBit := (EncodedBit.Word.mem_constantOneIndices _ left).mp
    (List.mem_toFinset.mp leftMember)
  have rightBit := (EncodedBit.Word.mem_constantOneIndices _ right).mp
    (List.mem_toFinset.mp rightMember)
  let leftPort := (Physical.ports width).symm (WireAddress.littleEndianWire left)
  let rightPort := (Physical.ports width).symm (WireAddress.littleEndianWire right)
  have truePort (index : Fin (2 * width + 4))
      (selected : (seedLabel width N).val.testBit index.val = true) :
      ((Physical.layout width).bit
        ((Physical.ports width).symm (WireAddress.littleEndianWire index))).get
          (seedLabel width N) = true := by
    change (seedLabel width N).val.testBit
      (WireAddress.bitIndex (Physical.ports width
        ((Physical.ports width).symm (WireAddress.littleEndianWire index)))).val = true
    simpa only [Equiv.apply_symm_apply, WireAddress.bitIndex_littleEndianWire] using selected
  obtain ⟨leftSource, leftSame, leftZero⟩ :=
    seed_true_source width N leftPort (truePort left leftBit)
  obtain ⟨rightSource, rightSame, rightZero⟩ :=
    seed_true_source width N rightPort (truePort right rightBit)
  have sourceSame : leftSource = rightSource := Fin.ext (leftZero.trans rightZero.symm)
  have portSame : leftPort = rightPort := by rw [leftSame, rightSame, sourceSame]
  have wires := congrArg (Physical.ports width) portSame
  have bits := congrArg WireAddress.bitIndex wires
  simpa only [leftPort, rightPort, Equiv.apply_symm_apply,
    WireAddress.bitIndex_littleEndianWire] using bits

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
