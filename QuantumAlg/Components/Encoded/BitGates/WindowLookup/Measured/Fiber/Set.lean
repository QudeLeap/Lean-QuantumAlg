/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Fiber
import all QuantumAlg.Components.Encoded.BitGates.StateEquality
import all QuantumAlg.Components.Encoded.BitGates.BitEquality

/-!
# Complete original-label characterization of a mathematical word setter

An original target value and every complementary bit determine the entire
label under a full binary encoding. This fixes the setter independently
of its finite-XOR implementation and proves exact restoration after a
real zero-target lookup. The other numerical words and all workspace
remain part of the complete label throughout these equalities.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The requested word and all original complementary readouts characterize the complete setter. -/
lemma resultSetConstant_eq_of_readouts (onto : Function.Surjective encoding.encode)
    (word : Word encoding width) (distinct : Function.Injective fun index => (word.bit index).wire)
    (value : Fin (2 ^ width)) (first second : Data)
    (target : ∀ index, (word.bit index).get second = value.val.testBit index.val)
    (other : ∀ observed : EncodedBit encoding,
      (∀ index, (word.bit index).wire ≠ observed.wire) →
        observed.get second = observed.get first) :
    resultSetConstant word value first = second := by
  apply state_eq_of_get_eq onto
  intro observed
  by_cases selected : ∃ index, (word.bit index).wire = observed.wire
  · obtain ⟨index, same⟩ := selected
    rw [← eq_of_wire_eq (word.bit index) observed same]
    exact (resultSetConstant_get word distinct value first index).trans (target index).symm
  · have outside : ∀ index, (word.bit index).wire ≠ observed.wire := by
      intro index same
      exact selected ⟨index, same⟩
    exact (resultSetConstant_observed word value observed outside first).trans
      (other observed outside).symm

/-- Setting an already present word value preserves the complete original label. -/
lemma resultSetConstant_self (onto : Function.Surjective encoding.encode)
    (word : Word encoding width) (distinct : Function.Injective fun index => (word.bit index).wire)
    (value : Fin (2 ^ width)) (state : Data)
    (target : ∀ index, (word.bit index).get state = value.val.testBit index.val) :
    resultSetConstant word value state = state :=
  resultSetConstant_eq_of_readouts onto word distinct value state state target (fun _ _ => rfl)

/-- Setters of disjoint original words commute on the complete label. -/
lemma resultSetConstant_comm_of_disjoint {otherWidth : Nat}
    (onto : Function.Surjective encoding.encode) (first : Word encoding width)
    (second : Word encoding otherWidth)
    (firstDistinct : Function.Injective fun index => (first.bit index).wire)
    (secondDistinct : Function.Injective fun index => (second.bit index).wire)
    (disjoint : ∀ left right, (first.bit left).wire ≠ (second.bit right).wire)
    (left : Fin (2 ^ width)) (right : Fin (2 ^ otherWidth)) (state : Data) :
    resultSetConstant first left (resultSetConstant second right state) =
      resultSetConstant second right (resultSetConstant first left state) := by
  apply resultSetConstant_eq_of_readouts onto first firstDistinct
  · intro index
    rw [resultSetConstant_observed second right (first.bit index)
      (fun other => (disjoint index other).symm), resultSetConstant_get first firstDistinct]
  · intro observed outsideFirst
    by_cases selected : ∃ index, (second.bit index).wire = observed.wire
    · obtain ⟨index, same⟩ := selected
      rw [← eq_of_wire_eq (second.bit index) observed same,
        resultSetConstant_get second secondDistinct, resultSetConstant_get second secondDistinct]
    · have outsideSecond : ∀ index, (second.bit index).wire ≠ observed.wire := by
        intro index same
        exact selected ⟨index, same⟩
      rw [resultSetConstant_observed second right observed outsideSecond,
        resultSetConstant_observed second right observed outsideSecond,
        resultSetConstant_observed first left observed outsideFirst]

/-- Loading into a real zero word and clearing that same word restores every original coordinate. -/
lemma resultSetConstant_zero_xor (onto : Function.Surjective encoding.encode)
    (word : Word encoding width) (distinct : Function.Injective fun index => (word.bit index).wire)
    (constant : Fin (2 ^ width)) (state : Data)
    (zero : ∀ index, (word.bit index).get state = false) :
    resultSetConstant word 0 (Word.xorConstantStep word constant state) = state := by
  apply resultSetConstant_eq_of_readouts onto word distinct
  · intro index
    exact (zero index).trans (Nat.zero_testBit index.val).symm
  · intro observed outside
    exact (Word.xorConstantStep_get_observed_of_target_ne word constant observed outside state).symm

end

end QuantumAlg.EncodedBit.WindowLookup
