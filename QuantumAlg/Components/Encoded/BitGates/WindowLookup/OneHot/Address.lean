/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.OneHot.Invariant
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Address.BitVec

/-!
# Exact binary values of unary output positions

The least-significant-first address positions determine the successive
doubled unary ranges. The final label is the complete original binary word;
all actual unary stages preserve that original address.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.UnaryFrame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The exact low binary prefix of the original address. -/
def prefixValue (frame : UnaryFrame encoding width) :
    (depth : Nat) → depth ≤ width → Data → Nat
  | 0, _, _ => 0
  | depth + 1, fits, state =>
      frame.prefixValue depth (by omega) state +
        if (frame.address ⟨depth, by omega⟩).get state then 2 ^ depth else 0

/-- Each partial address fits exactly within its own doubled unary range. -/
lemma prefixValue_lt (frame : UnaryFrame encoding width) (depth : Nat)
    (fits : depth ≤ width) (state : Data) : frame.prefixValue depth fits state < 2 ^ depth := by
  induction depth with
  | zero => exact Nat.zero_lt_one
  | succ depth ih =>
      have previous := ih (by omega)
      dsimp only [prefixValue]
      rw [pow_succ]
      split <;> omega

/-- The original partial address expressed in the existing full unary range. -/
def prefixLabel (frame : UnaryFrame encoding width) (depth : Nat) (fits : depth ≤ width)
    (state : Data) : Fin (2 ^ width) :=
  ⟨frame.prefixValue depth fits state, lt_of_lt_of_le (frame.prefixValue_lt depth fits state)
    (Nat.pow_le_pow_right Nat.zero_lt_two fits)⟩

/-- The full-range label still lies inside its exact partial unary range. -/
lemma prefixLabel_lt (frame : UnaryFrame encoding width) (depth : Nat)
    (fits : depth ≤ width) (state : Data) :
    (frame.prefixLabel depth fits state).val < 2 ^ depth :=
  frame.prefixValue_lt depth fits state

/-- Any action preserving every original address readout preserves its exact binary value. -/
lemma prefixValue_congr (frame : UnaryFrame encoding width) (depth : Nat)
    (fits : depth ≤ width) (first second : Data)
    (agree : ∀ index, (frame.address index).get first = (frame.address index).get second) :
    frame.prefixValue depth fits first = frame.prefixValue depth fits second := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      dsimp only [prefixValue]
      rw [ih (by omega), agree]

/-- No exact binary prefix changes when its original address fields are preserved. -/
lemma prefixLabel_congr (frame : UnaryFrame encoding width) (depth : Nat)
    (fits : depth ≤ width) (first second : Data)
    (agree : ∀ index, (frame.address index).get first = (frame.address index).get second) :
    frame.prefixLabel depth fits first = frame.prefixLabel depth fits second :=
  Fin.ext (frame.prefixValue_congr depth fits first second agree)

/-- Every actual unary stage retains every original binary prefix value. -/
lemma prefixLabel_stage (frame : UnaryFrame encoding width) (depth : Nat)
    (present : depth < width) (bits : Nat) (fits : bits ≤ width) (state : Data) :
    frame.prefixLabel bits fits ((frame.stage depth present).step state) =
      frame.prefixLabel bits fits state :=
  frame.prefixLabel_congr bits fits _ _ (fun index => frame.stage_address depth present index state)

/-- Selecting the next doubled half incorporates exactly the next original binary address bit. -/
lemma nextLabel_prefixLabel (frame : UnaryFrame encoding width) (depth : Nat)
    (present : depth < width) (state : Data) :
    nextLabel depth present (frame.prefixLabel depth (by omega) state)
      (frame.prefixLabel_lt depth (by omega) state)
      ((frame.address ⟨depth, present⟩).get state) =
        frame.prefixLabel (depth + 1) (by omega) state := by
  apply Fin.ext
  rw [nextLabel_val]
  change (if (frame.address ⟨depth, present⟩).get state then
      2 ^ depth + frame.prefixValue depth (by omega) state
      else frame.prefixValue depth (by omega) state) =
    frame.prefixValue depth (by omega) state +
      (if (frame.address ⟨depth, present⟩).get state then 2 ^ depth else 0)
  cases (frame.address ⟨depth, present⟩).get state
  · exact (Nat.add_zero _).symm
  · exact Nat.add_comm _ _

/-- The original low prefix agrees with the complete fixed-width word, without truncation. -/
lemma prefixValue_bitVec (frame : UnaryFrame encoding width) (word : BitVec width) (state : Data)
    (addressBits : ∀ index, (frame.address index).get state = word.getLsbD index.val)
    (depth : Nat) (fits : depth ≤ width) :
    frame.prefixValue depth fits state = word.toNat % 2 ^ depth := by
  induction depth with
  | zero => simp only [prefixValue, pow_zero, Nat.mod_one]
  | succ depth ih =>
      dsimp only [prefixValue]
      rw [ih (by omega), addressBits]
      rw [SelectorFrame.mod_two_pow_succ_bit]
      change word.toNat % 2 ^ depth +
          (if word.toNat.testBit depth then 2 ^ depth else 0) = _
      exact Nat.add_comm _ _

/-- The final unary token position is exactly the original full fixed-width address. -/
lemma prefixLabel_bitVec (frame : UnaryFrame encoding width) (word : BitVec width) (state : Data)
    (addressBits : ∀ index, (frame.address index).get state = word.getLsbD index.val) :
    frame.prefixLabel width (Nat.le_refl _) state = word.toFin := by
  apply Fin.ext
  change frame.prefixValue width (Nat.le_refl _) state = word.toNat
  rw [frame.prefixValue_bitVec word state addressBits, Nat.mod_eq_of_lt word.isLt]

end

end QuantumAlg.EncodedBit.WindowLookup.UnaryFrame
