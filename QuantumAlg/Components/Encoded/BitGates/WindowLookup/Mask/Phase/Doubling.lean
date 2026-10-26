/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Mask.Phase
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Mask.Conjugation

/-!
# Logarithmic actual mask-parity fan-in

The same certified target layers are traversed in reverse order with their
CNOT directions exchanged. The original pivot then contains exactly the
mask parity, including every arbitrary incoming target value.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count : Nat}

/-- Transposed doubling layers accumulate precisely the complete reached prefix parity. -/
lemma doublingWord_parity (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (height : Nat) (state : Data) :
    bitParity (prefixBits target 1)
      (GateSpec.stepList (layerWordGates
        (parityFanInWord (doublingWord target distinct height))) state) =
      bitParity (prefixBits target (2 ^ height)) state := by
  induction height generalizing state with
  | zero => rfl
  | succ height ih =>
      have gates : layerWordGates (parityFanInWord (doublingWord target distinct (height + 1))) =
          (doublingLayer target distinct (2 ^ height) (Nat.pow_pos (by decide))).transpose.gates ++
            layerWordGates (parityFanInWord (doublingWord target distinct height)) := by
        simp only [doublingWord, parityFanInWord, List.reverse_append, List.reverse_cons,
          List.reverse_nil, List.nil_append, List.map_append, List.map_cons, List.map_nil,
          layerWordGates, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [gates, GateSpec.stepList_append, ih,
        CnotLayer.transpose_parity _ (prefixBits target (2 ^ height))
          (prefixBits_distinct target distinct _)
          (doubling_control_present target distinct _ (Nat.pow_pos (by decide))),
        prefixBits_doubling target distinct _ (Nat.pow_pos (by decide))]
      rw [pow_succ, Nat.mul_comm]

/-- The original pivot reads the exact parity of every selected original target. -/
lemma parityFanInWord_pivot (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (positive : 0 < count) (height : Nat) (covered : count ≤ 2 ^ height) (state : Data) :
    (target ⟨0, positive⟩).get
      (GateSpec.stepList (layerWordGates
        (parityFanInWord (doublingWord target distinct height))) state) =
      bitParity (prefixBits target count) state := by
  have actual := doublingWord_parity target distinct height state
  rw [prefixBits_one target positive] at actual
  simpa only [bitParity, Bool.xor_false, prefixBits, Nat.min_eq_right covered,
    Nat.min_self, Fin.val_cast] using actual

end

end QuantumAlg.EncodedBit.WindowLookup
