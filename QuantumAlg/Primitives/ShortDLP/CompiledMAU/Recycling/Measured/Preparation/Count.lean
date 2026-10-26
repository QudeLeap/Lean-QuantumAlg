/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Preparation
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor

/-!
# Exact literal seed-loader count on the actual complete physical frame

The original identity residue has exactly one true source bit. The complete
physical port bijection carries that unique bit to one actual native X
instruction; the control, auxiliary word, helpers and flag remain zero
[G25, main.tex:271-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open MAU.Multiplication.Gidney.Measured

private lemma seed_true_port (width N : Nat) (wide : 0 < width) (nontrivial : 1 < N)
    (port : Port width) (selected : ((Physical.layout width).bit port).get (seedLabel width N) =
      true) :
    port = .inr (.inl ⟨0, wide⟩) := by
  rw [seedLabel, Physical.cleanLabel, Physical.label_bit, Nat.mod_eq_of_lt nontrivial] at selected
  cases port with
  | inl control => cases control; cases selected
  | inr remainder =>
      cases remainder with
      | inl index =>
          simp only [BitVec.getLsbD_ofNat, index.isLt, decide_true, Bool.true_and] at selected
          have zero : index.val = 0 := Nat.testBit_one_eq_true_iff_self_eq_zero.mp selected
          exact congrArg (fun source : Fin width => (.inr (.inl source) : Port width))
            (Fin.ext zero)
      | inr _ => cases selected

/-- Exactly one native X instruction loads the original nontrivial-modulus identity seed. -/
lemma measuredSeed_xCount (width N : Nat) (wide : 0 < width) (nontrivial : 1 < N) :
    EncodedBit.Word.BasisLoad.xCount (seedLabel width N) = 1 := by
  rw [EncodedBit.Word.BasisLoad.xCount, ← List.toFinset_card_of_nodup
    (EncodedBit.Word.constantOneIndices_nodup (seedLabel width N))]
  let chosen : Port width := .inr (.inl ⟨0, wide⟩)
  have portOfMember (index : Fin (2 * width + 4))
      (member : index ∈ (EncodedBit.Word.constantOneIndices (seedLabel width N)).toFinset) :
      (Physical.ports width).symm (WireAddress.littleEndianWire index) = chosen := by
    have bit := (EncodedBit.Word.mem_constantOneIndices _ index).mp
      (List.mem_toFinset.mp member)
    apply seed_true_port width N wide nontrivial
    change (seedLabel width N).val.testBit
      (WireAddress.bitIndex (Physical.ports width
        ((Physical.ports width).symm (WireAddress.littleEndianWire index)))).val = true
    simpa only [Equiv.apply_symm_apply, WireAddress.bitIndex_littleEndianWire] using bit
  have atMost : (EncodedBit.Word.constantOneIndices (seedLabel width N)).toFinset.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro left leftMember right rightMember
    have ports := (portOfMember left leftMember).trans (portOfMember right rightMember).symm
    have wires := congrArg (Physical.ports width) ports
    have bits := congrArg WireAddress.bitIndex wires
    simpa only [Equiv.apply_symm_apply, WireAddress.bitIndex_littleEndianWire] using bits
  have selected : ((Physical.layout width).bit chosen).get (seedLabel width N) = true := by
    rw [seedLabel, Physical.cleanLabel, Physical.label_bit, Nat.mod_eq_of_lt nontrivial]
    simp only [chosen, BitVec.getLsbD_ofNat, wide, decide_true, Bool.true_and, Nat.testBit_zero]
  have member : WireAddress.bitIndex (Physical.ports width chosen) ∈
      (EncodedBit.Word.constantOneIndices (seedLabel width N)).toFinset := by
    apply List.mem_toFinset.mpr
    apply (EncodedBit.Word.mem_constantOneIndices _ _).mpr
    exact selected
  have atLeast := Finset.one_le_card.mpr ⟨_, member⟩
  omega

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
