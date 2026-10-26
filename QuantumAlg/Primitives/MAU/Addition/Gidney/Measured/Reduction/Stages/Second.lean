/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Stages.First
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Stages
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Stages.Offsets
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Arithmetic
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Program
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Branch

/-!
# Actual modular target and physically cleared flag after the second measured addition

The actual second offset and final native comparison realize the independent
controlled modular-addition specification on every canonical target input.
Both original clean helpers and the original flag are restored physically;
the frame laws separately retain arbitrary dirty and outside data
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

open EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The second actual measured addition has exactly the independent second finite-word value. -/
lemma secondAdded_word_nat (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (constantBound : constant.toNat < modulus.toNat)
    (initial : Data) (clean : ∀ helper, (layout.clean helper).get initial = false)
    (flagClean : layout.flag.get initial = false) :
    (layout.sourceWord (layout.secondAdded wide modulus constant initial)).toNat =
      secondWord (2 ^ width) modulus.toNat constant.toNat (layout.sourceWord initial).toNat
        (layout.activeValue initial) := by
  rw [secondAdded, reductionAdder_sourceWord layout wide (constant - modulus) _
    (middleFlagged_frame layout wide modulus constant initial clean).clean,
    selected_add_nat,
    middleFlagged_word_nat layout wide modulus constant constantBound initial clean flagClean,
    middleFlagged_flag layout wide modulus constant constantBound initial clean flagClean,
    secondOffset_nat modulus constant constantBound]
  rfl

/-- The second actual measured addition retains the original complementary flag value. -/
lemma secondAdded_flag (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (constantBound : constant.toNat < modulus.toNat)
    (initial : Data) (clean : ∀ helper, (layout.clean helper).get initial = false)
    (flagClean : layout.flag.get initial = false) :
    layout.flag.get (layout.secondAdded wide modulus constant initial) =
      secondFlag modulus.toNat constant.toNat (layout.sourceWord initial).toNat
        (layout.activeValue initial) := by
  rw [secondAdded, reductionAdder_flag layout wide (constant - modulus) _
    (middleFlagged_frame layout wide modulus constant initial clean).clean,
    middleFlagged_flag layout wide modulus constant constantBound initial clean flagClean]

/-- The actual final native comparison retains the computed modular target word. -/
lemma finalCompared_word_nat (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (constantBound : constant.toNat < modulus.toNat)
    (initial : Data) (clean : ∀ helper, (layout.clean helper).get initial = false)
    (flagClean : layout.flag.get initial = false) :
    (layout.sourceWord (layout.finalCompared wide modulus constant initial)).toNat =
      secondWord (2 ^ width) modulus.toNat constant.toNat (layout.sourceWord initial).toNat
        (layout.activeValue initial) := by
  rw [finalCompared, comparisonGates_sourceWord layout wide constant _
    (secondAdded_frame layout wide modulus constant initial clean).clean,
    secondAdded_word_nat layout wide modulus constant constantBound initial clean flagClean]

/-- The final paid native comparison physically clears the same original reduction flag. -/
lemma finalCompared_flag (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (constantBound : constant.toNat < modulus.toNat)
    (initial : Data) (inputBound : (layout.sourceWord initial).toNat < modulus.toNat)
    (clean : ∀ helper, (layout.clean helper).get initial = false)
    (flagClean : layout.flag.get initial = false) :
    layout.flag.get (layout.finalCompared wide modulus constant initial) = false := by
  have frame := secondAdded_frame layout wide modulus constant initial clean
  have actual := comparisonGates_flag layout wide constant
    (layout.secondAdded wide modulus constant initial) frame.clean
  change layout.flag.get (layout.finalCompared wide modulus constant initial) =
    (layout.flag.get (layout.secondAdded wide modulus constant initial) ^^
      (layout.activeValue (layout.secondAdded wide modulus constant initial) &&
        decide ((layout.sourceWord (layout.secondAdded wide modulus constant initial)).toNat <
          constant.toNat))) at actual
  rw [secondAdded_flag layout wide modulus constant constantBound initial clean flagClean,
    frameInvariant_activeValue frame,
    secondAdded_word_nat layout wide modulus constant constantBound initial clean flagClean]
      at actual
  exact actual.trans (finalFlag_eq_false (by have inside := modulus.isLt; omega)
    constantBound inputBound (layout.activeValue initial))

/-- The actual literal program computes the independent controlled modular target specification. -/
lemma modularWord_target_nat (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (constantBound : constant.toNat < modulus.toNat)
    (initial : Data) (inputBound : (layout.sourceWord initial).toNat < modulus.toNat)
    (clean : ∀ helper, (layout.clean helper).get initial = false)
    (flagClean : layout.flag.get initial = false) :
    (layout.sourceWord (wordLabel (layout.modularWord wide modulus constant) initial)).toNat =
      output modulus.toNat constant.toNat (layout.sourceWord initial).toNat
        (layout.activeValue initial) := by
  by_cases zero : constant = 0
  · subst constant
    rw [modularWord, if_pos rfl]
    change (layout.sourceWord initial).toNat =
      output modulus.toNat 0 (layout.sourceWord initial).toNat (layout.activeValue initial)
    cases layout.activeValue initial with
    | false => rfl
    | true =>
        change (layout.sourceWord initial).toNat = (layout.sourceWord initial).toNat % modulus.toNat
        exact (Nat.mod_eq_of_lt inputBound).symm
  · rw [modularWord_label_stages layout wide modulus constant zero,
      finalCompared_word_nat layout wide modulus constant constantBound initial clean flagClean,
      secondWord_eq_output (by have inside := modulus.isLt; omega) constantBound inputBound]

/-- The same actual literal program returns its original reduction flag physically to zero. -/
lemma modularWord_flag_zero (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (constantBound : constant.toNat < modulus.toNat)
    (initial : Data) (inputBound : (layout.sourceWord initial).toNat < modulus.toNat)
    (clean : ∀ helper, (layout.clean helper).get initial = false)
    (flagClean : layout.flag.get initial = false) :
    layout.flag.get (wordLabel (layout.modularWord wide modulus constant) initial) = false := by
  by_cases zero : constant = 0
  · rw [modularWord, if_pos zero]
    exact flagClean
  · rw [modularWord_label_stages layout wide modulus constant zero]
    exact finalCompared_flag layout wide modulus constant constantBound initial inputBound clean
      flagClean

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
