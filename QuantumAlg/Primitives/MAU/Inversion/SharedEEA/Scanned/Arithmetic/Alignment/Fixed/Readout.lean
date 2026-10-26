/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Fixed.Frame
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding

/-!
# Complete static rotation readouts of original work and retained bits

Both original work words use the same physical rotation. Every
unselected original system is retained exactly, including the entire
pool. Actual paid barrel realization is a separate theorem.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment.Fixed

noncomputable section

open EncodedBit

private def pairBit (width : Nat) (first : Bool) (index : Fin (width + 3)) :
    EncodedBit (Addition.TTK.encoding (width + 3)) :=
  if first then BinaryLabelEncoding.prodLeftBit
    (BinaryLabelEncoding.finIdentity (width + 3)) (BinaryLabelEncoding.finIdentity (width + 3))
    (BinaryLabelEncoding.finIdentityBit (width + 3) index)
  else BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.finIdentity (width + 3)) (BinaryLabelEncoding.finIdentity (width + 3))
    (BinaryLabelEncoding.finIdentityBit (width + 3) index)

private lemma pairBit_wire (width : Nat) (first : Bool) (index : Fin (width + 3)) :
    (pairBit width first index).wire =
      if first then Fin.castAdd (width + 3) index else Fin.natAdd (width + 3) index := by
  cases first <;> rfl

private lemma pairPermutation_bit (width displacement : Nat) (first : Bool)
    (index : Fin (width + 3)) :
    pairPermutation width displacement (pairBit width first index).wire =
      (pairBit width first ((permutation width ^ displacement) index)).wire := by
  cases first with
  | false =>
      rw [pairBit_wire, pairBit_wire]
      simp only [Bool.false_eq_true, if_false]
      change finSumFinEquiv
        ((Equiv.sumCongr (permutation width ^ displacement) (permutation width ^ displacement))
          (finSumFinEquiv.symm (Fin.natAdd (width + 3) index))) =
            Fin.natAdd (width + 3) ((permutation width ^ displacement) index)
      simp only [finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inr,
        finSumFinEquiv_apply_right]
  | true =>
      rw [pairBit_wire, pairBit_wire]
      simp only [if_true]
      change finSumFinEquiv
        ((Equiv.sumCongr (permutation width ^ displacement) (permutation width ^ displacement))
          (finSumFinEquiv.symm (Fin.castAdd (width + 3) index))) =
            Fin.castAdd (width + 3) ((permutation width ^ displacement) index)
      simp only [finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl,
        finSumFinEquiv_apply_left]

private lemma operand_location (width : Nat) (first : Bool) (index : Fin (width + 3)) :
    (operands width).wires (pairBit width first index).wire =
      (ArithmeticRotation.bit width first index).wire := by
  cases first with
  | false =>
      change (wordPairSubsystem _ _ _ _ _).wires (Fin.natAdd (width + 3) index) = _
      exact wordPairSubsystem_right _ _ _ _ _ index
  | true =>
      change (wordPairSubsystem _ _ _ _ _).wires (Fin.castAdd (width + 3) index) = _
      exact wordPairSubsystem_left _ _ _ _ _ index

private lemma pairFrame_read (width displacement : Nat) (first : Bool)
    (index : Fin (width + 3)) (state : Addition.TTK.Registers (width + 3)) :
    (pairBit width first index).get ((pairFrame width displacement).grouping state) =
      (pairBit width first ((permutation width ^ displacement) index)).get state :=
  FullPlacement.ofWires_read _ _ (ArithmeticWindow.source_onto (width + 3))
    (ArithmeticWindow.source_onto (width + 3)) (pairPermutation width displacement)
    (pairBit width first index)
    (pairBit width first ((permutation width ^ displacement) index))
    (pairPermutation_bit width displacement first index) state

/-- Each static output bit is the declared original rotated physical word bit. -/
lemma frame_word_get (width displacement : Nat) (first : Bool)
    (index : Fin (width + 3)) (state : Data width) :
    (ArithmeticRotation.bit width first index).get ((frame width displacement).grouping state) =
      (ArithmeticRotation.bit width first
        ((permutation width ^ displacement) index)).get state := by
  have focused := (operands width).full_step_source_read
    (ArithmeticWindow.source_onto (width + 3)) (Scanned.encoding_surjective width)
    (pairBit width first index) (ArithmeticRotation.bit width first index)
    (operand_location width first index) (pairFrame width displacement).grouping state
  have original := (operands width).full_source_read
    (ArithmeticWindow.source_onto (width + 3)) (Scanned.encoding_surjective width)
    (pairBit width first ((permutation width ^ displacement) index))
    (ArithmeticRotation.bit width first ((permutation width ^ displacement) index))
    (operand_location width first ((permutation width ^ displacement) index)) state
  exact focused.trans
    ((pairFrame_read width displacement first index
      ((operandsFrame width).grouping state).1).trans original)

/-- Every original unselected physical system, including the entire pool, keeps its full value. -/
lemma frame_other_get (width displacement : Nat) (observed : EncodedBit (encoding width))
    (outside : observed.wire ∉ Set.range (operands width).wires) (state : Data width) :
    observed.get ((frame width displacement).grouping state) = observed.get state :=
  (operands width).full_step_other_read (ArithmeticWindow.source_onto (width + 3))
    (Scanned.encoding_surjective width) observed outside
    (pairFrame width displacement).grouping state

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment.Fixed
