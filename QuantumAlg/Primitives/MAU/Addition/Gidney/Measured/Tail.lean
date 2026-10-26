/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Phase.Carry

/-!
# The exact paid phase/carry repair tail of the measured adder

Both complements are literal native X words. The two stored-outcome Z passes
surround the literal native dirty-carry word in the original source order.
This split changes neither the instruction list nor its resource accounting
[G25, main.tex:271-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open EncodedBit GateSpec Instruction
open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Actual native complements and paid phase/carry/phase repair in their chronological order. -/
def tailWord (layout : Layout encoding width) (constant : BitVec width) :
    List (Instruction encoding (width - 2)) :=
  [.native layout.complementGates] ++
    (layout.phaseWord ++ [.native (layout.carryLayout.gates (constant.setWidth (width - 2)))] ++
      layout.phaseWord) ++ [.native layout.complementGates]

/-- Splitting off the actual repair tail preserves the complete literal measured-adder word. -/
lemma adderWord_eq_stream_tail (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) :
    layout.adderWord wide constant =
      layout.streamingWord wide constant ++ layout.tailWord constant :=
  by simp only [adderWord, tailWord, List.append_assoc]

/-- Both paid phase passes preserve labels while the actual native carry word acts between them. -/
lemma tailWord_label (layout : Layout encoding width) (constant : BitVec width) (state : Data) :
    wordLabel (layout.tailWord constant) state =
      stepList layout.complementGates
        (stepList (layout.carryLayout.gates (constant.setWidth (width - 2)))
          (stepList layout.complementGates state)) := by
  simp only [tailWord, wordLabel_append, wordLabel, labelStep, phaseWord_label]

/-- The exact paid tail character is the native carry character of the complemented input. -/
lemma tailWord_weight (layout : Layout encoding width) (constant : BitVec width)
    (outcome : Fin (width - 2) → Fin 2) (state : Data) :
    wordWeight outcome (layout.tailWord constant) state =
      ∏ index : Fin (width - 2), MeasuredUncompute.character (outcome index)
        (layout.carryLayout.carryValues (constant.setWidth (width - 2))
          (stepList layout.complementGates state) (index.val + 1)) := by
  rw [tailWord, wordWeight_append, wordWeight_append]
  simp only [wordWeight, branchWeight, wordLabel, labelStep, mul_one,
    one_mul, phaseCarry_weight]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
