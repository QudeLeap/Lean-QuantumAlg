/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Stages
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Program
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Isometry
import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-!
# Clean-helper injectivity of the complete actual measured reduction label

Each native subword is inverted only as a native gate word. Both actual
measured additions use their independently proved clean-helper injectivity
and their actual restored input helpers. The resulting full-label law keeps
arbitrary dirty/control/flag values, without assuming global injectivity of
physical reset [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

open EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

private lemma nativeFold_injective (gates : List (GateSpec encoding)) :
    Function.Injective (stepList gates) := by
  intro first second same
  have restored := congrArg (stepList gates.reverse) same
  rwa [stepList_reverse_stepList, stepList_reverse_stepList] at restored

/-- Equal actual full outputs identify equal original full clean-helper labels. -/
lemma modularWord_label_injective_clean (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (first second : Data)
    (firstClean : ∀ helper, (layout.clean helper).get first = false)
    (secondClean : ∀ helper, (layout.clean helper).get second = false)
    (same : wordLabel (layout.modularWord wide modulus constant) first =
      wordLabel (layout.modularWord wide modulus constant) second) : first = second := by
  by_cases zero : constant = 0
  · rw [modularWord, if_pos zero] at same
    exact same
  · rw [modularWord_label_stages layout wide modulus constant zero first,
      modularWord_label_stages layout wide modulus constant zero second] at same
    have secondAddedSame : layout.secondAdded wide modulus constant first =
        layout.secondAdded wide modulus constant second :=
      nativeFold_injective (layout.comparisonGates wide constant) same
    have middleSame := Measured.Layout.adderWord_label_injective_clean layout.adderLayout
      wide (constant - modulus) (layout.middleFlagged wide modulus constant first)
      (layout.middleFlagged wide modulus constant second)
      (middleFlagged_frame layout wide modulus constant first firstClean).clean
      (middleFlagged_frame layout wide modulus constant second secondClean).clean secondAddedSame
    have firstAddedSame : layout.firstAdded wide modulus constant first =
        layout.firstAdded wide modulus constant second :=
      nativeFold_injective layout.toggleFlagGates middleSame
    have firstComparedSame := Measured.Layout.adderWord_label_injective_clean layout.adderLayout
      wide constant (layout.firstCompared wide modulus constant first)
      (layout.firstCompared wide modulus constant second)
      (firstCompared_frame layout wide modulus constant first firstClean).clean
      (firstCompared_frame layout wide modulus constant second secondClean).clean firstAddedSame
    exact nativeFold_injective (layout.comparisonGates wide (modulus - constant)) firstComparedSame

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
