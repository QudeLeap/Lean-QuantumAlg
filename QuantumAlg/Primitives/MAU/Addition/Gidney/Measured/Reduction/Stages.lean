/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Frame
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Program
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Composition
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Branch

/-!
# Exact successive original labels of the literal modular-reduction word

The named labels follow the actual comparison/addition/toggle/addition/
comparison source order. Their frame invariant retains all arbitrary dirty
and outside data and returns both physical helpers to zero at every stage
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

open EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Original label after the actual first native comparison. -/
def firstCompared (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (initial : Data) : Data :=
  stepList (layout.comparisonGates wide (modulus - constant)) initial

/-- Original label after the first actual measured addition. -/
def firstAdded (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (initial : Data) : Data :=
  wordLabel (layout.adderLayout.adderWord wide constant)
    (layout.firstCompared wide modulus constant initial)

/-- Original label after the paid middle native flag toggle. -/
def middleFlagged (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (initial : Data) : Data :=
  stepList layout.toggleFlagGates (layout.firstAdded wide modulus constant initial)

/-- Original label after the second actual measured addition. -/
def secondAdded (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (initial : Data) : Data :=
  wordLabel (layout.adderLayout.adderWord wide (constant - modulus))
    (layout.middleFlagged wide modulus constant initial)

/-- Original label after the actual final native comparison clears the flag. -/
def finalCompared (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (initial : Data) : Data :=
  stepList (layout.comparisonGates wide constant)
    (layout.secondAdded wide modulus constant initial)

/-- The literal nonzero-offset source word has exactly those chronological intermediate labels. -/
lemma modularWord_label_stages (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (nonzero : constant ≠ 0) (initial : Data) :
    wordLabel (layout.modularWord wide modulus constant) initial =
      layout.finalCompared wide modulus constant initial := by
  rw [modularWord, if_neg nonzero]
  simp only [wordLabel_append, wordLabel, labelStep]
  rfl

/-- The actual first comparison restores the original complete frame. -/
lemma firstCompared_frame (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false) :
    layout.FrameInvariant initial (layout.firstCompared wide modulus constant initial) :=
  frameInvariant_comparison (frameInvariant_initial layout initial clean) wide _

/-- The first actual measured addition restores the same original complete frame. -/
lemma firstAdded_frame (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false) :
    layout.FrameInvariant initial (layout.firstAdded wide modulus constant initial) :=
  frameInvariant_adder (firstCompared_frame layout wide modulus constant initial clean) wide _

/-- The paid native middle toggle retains the original complete frame. -/
lemma middleFlagged_frame (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false) :
    layout.FrameInvariant initial (layout.middleFlagged wide modulus constant initial) :=
  frameInvariant_toggle (firstAdded_frame layout wide modulus constant initial clean)

/-- The second actual measured addition restores the original complete frame. -/
lemma secondAdded_frame (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false) :
    layout.FrameInvariant initial (layout.secondAdded wide modulus constant initial) :=
  frameInvariant_adder (middleFlagged_frame layout wide modulus constant initial clean) wide _

/-- The actual final comparison restores the original complete frame. -/
lemma finalCompared_frame (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false) :
    layout.FrameInvariant initial (layout.finalCompared wide modulus constant initial) :=
  frameInvariant_comparison (secondAdded_frame layout wide modulus constant initial clean) wide _

/-- The same literal program restores every original frame system, also for a zero offset. -/
lemma modularWord_frame (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus constant : BitVec width) (initial : Data)
    (clean : ∀ helper, (layout.clean helper).get initial = false) :
    layout.FrameInvariant initial (wordLabel (layout.modularWord wide modulus constant) initial) :=
  by
  by_cases zero : constant = 0
  · rw [modularWord, if_pos zero]
    exact frameInvariant_initial layout initial clean
  · rw [modularWord_label_stages layout wide modulus constant zero]
    exact finalCompared_frame layout wide modulus constant initial clean

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
