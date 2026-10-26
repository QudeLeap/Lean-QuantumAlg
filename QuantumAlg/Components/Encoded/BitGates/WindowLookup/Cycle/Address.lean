/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Cycle.Circuit
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Address.BitVec
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.OneHot.Address
import all QuantumAlg.Components.Encoded.BitGates.BitEquality
import Batteries.Data.BitVec.Lemmas

/-!
# Complete physical address agreement between lookup and split unlookup

The high address is most significant first and the low address is least
significant first. Equality of their actual physical wires proves that
the full native loader and the same-table feedback select the same row.
No numerical address or zero-width case is discarded.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

private def msbWord {width : Nat} (bits : Fin width → Bool) : BitVec width :=
  BitVec.ofFnLE (fun index => bits index.rev)

private lemma msbWord_bit {width : Nat} (bits : Fin width → Bool) (index : Fin width) :
    (msbWord bits).getMsbD index.val = bits index := by
  simp only [msbWord, BitVec.getMsbD_ofFnLE, index.isLt, dite_true, Fin.rev_rev]

private def lsbWord {width : Nat} (bits : Fin width → Bool) : BitVec width :=
  BitVec.ofFnLE bits

private lemma lsbWord_bit {width : Nat} (bits : Fin width → Bool) (index : Fin width) :
    (lsbWord bits).getLsbD index.val = bits index := by
  simp only [lsbWord, BitVec.getLsbD_ofFnLE, index.isLt, dite_true]

private lemma lsbWord_msb {width : Nat} (bits : Fin width → Bool) (index : Fin width) :
    (lsbWord bits).getMsbD index.val = bits index.rev := by
  simp only [lsbWord, BitVec.getMsbD_ofFnLE, index.isLt, dite_true]

private lemma append_joined {highWidth lowWidth : Nat}
    (high : BitVec highWidth) (low : BitVec lowWidth) :
    (high ++ low).toFin = joinedAddress high.toFin low.toFin := by
  apply Fin.ext
  change (high ++ low).toNat = low.toNat + 2 ^ lowWidth * high.toNat
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt low.isLt, Nat.shiftLeft_eq]
  ring

/-- Literal original high/low physical address positions and the retained top control agree. -/
structure AddressSplit {Data : Type} {encoding : BinaryLabelEncoding Data}
    {highWidth lowWidth : Nat} (lookup : SelectorFrame encoding (highWidth + lowWidth))
    (high : SelectorFrame encoding highWidth) (low : UnaryFrame encoding lowWidth) : Prop where
  root : (lookup.stack ⟨0, by omega⟩).wire = (high.stack ⟨0, by omega⟩).wire
  highWires : ∀ index,
    (lookup.address (index.castAdd lowWidth)).wire = (high.address index).wire
  lowWires : ∀ index,
    (lookup.address (index.rev.natAdd highWidth)).wire = (low.address index).wire

namespace AddressSplit

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {highWidth lowWidth : Nat}
    {lookup : SelectorFrame encoding (highWidth + lowWidth)}
    {high : SelectorFrame encoding highWidth} {low : UnaryFrame encoding lowWidth}
    (split : AddressSplit lookup high low)

include split in
lemma root_get (state : Data) :
    (lookup.stack ⟨0, by omega⟩).get state = (high.stack ⟨0, by omega⟩).get state :=
  congrArg (fun bit : EncodedBit encoding => bit.get state)
    (eq_of_wire_eq _ _ split.root)

include split in
/-- Every complete MSB-first lookup address equals the original split feedback address. -/
lemma addressLabel (state : Data) :
    lookup.addressLabelAt (highWidth + lowWidth) 0 (by omega) 0 (by omega) state =
      joinedAddress (high.addressLabelAt highWidth 0 (by omega) 0 (by omega) state)
        (low.prefixLabel lowWidth (Nat.le_refl _) state) := by
  let upper := msbWord (fun index => (high.address index).get state)
  let lower := lsbWord (fun index => (low.address index).get state)
  have highRead := high.addressLabelAt_bitVec upper state
    (fun index => (msbWord_bit (fun bit => (high.address bit).get state) index).symm)
  have lowRead := low.prefixLabel_bitVec lower state
    (fun index => (lsbWord_bit (fun bit => (low.address bit).get state) index).symm)
  have joined := lookup.addressLabelAt_bitVec (upper ++ lower) state (by
    intro index
    refine Fin.addCases (fun index => ?_) (fun index => ?_) index
    · have read := congrArg (fun bit : EncodedBit encoding => bit.get state)
        (eq_of_wire_eq _ _ (split.highWires index))
      rw [BitVec.getMsbD_append]
      change _ = if highWidth ≤ index.val then _ else _
      rw [if_neg (by omega : ¬highWidth ≤ index.val)]
      exact read.trans (msbWord_bit (fun bit => (high.address bit).get state) index).symm
    · have read := congrArg (fun bit : EncodedBit encoding => bit.get state)
        (eq_of_wire_eq _ _ (split.lowWires index.rev))
      simp only [Fin.rev_rev] at read
      rw [BitVec.getMsbD_append]
      change _ = if highWidth ≤ highWidth + index.val then _ else _
      rw [if_pos (by omega : highWidth ≤ highWidth + index.val)]
      simp only [Fin.val_natAdd, Nat.add_sub_cancel_left]
      exact read.trans (lsbWord_msb (fun bit => (low.address bit).get state) index).symm)
  rw [highRead, lowRead]
  exact joined.trans (append_joined upper lower)

end AddressSplit

end

end QuantumAlg.EncodedBit.WindowLookup
