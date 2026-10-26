/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Pattern
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Additional original physical sources for the same dirty-work pattern

An ordered disjoint word extends the controls while retaining the
original output and arbitrary work. This describes actual native
pattern sources, without introducing an initialized temporary word.
-/

namespace QuantumAlg.EncodedBit.Word.OneDirtyLayout

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {controls extra : Nat}

/-- Append distinct original physical sources with the same original output and borrowed work. -/
def appendSources (layout : OneDirtyLayout (encoding := encoding) controls)
    (word : Word encoding extra)
    (distinct : Function.Injective (fun index => (word.bit index).wire))
    (separate : ∀ left right, (layout.source.bit left).wire ≠ (word.bit right).wire)
    (output : ∀ index, (word.bit index).wire ≠ layout.output.wire)
    (work : ∀ index, (word.bit index).wire ≠ layout.work.wire) :
    OneDirtyLayout (encoding := encoding) (controls + extra) where
  source := ⟨Fin.append layout.source.bit word.bit⟩
  output := layout.output
  work := layout.work
  source_injective := by
    intro left right
    refine Fin.addCases (fun left => ?_) (fun left => ?_) left
    · refine Fin.addCases (fun right => ?_) (fun right => ?_) right
      · intro same
        simp only [Fin.append_left] at same
        exact congrArg (Fin.castAdd extra) (layout.source_injective same)
      · intro same
        simp only [Fin.append_left, Fin.append_right] at same
        exact False.elim (separate left right same)
    · refine Fin.addCases (fun right => ?_) (fun right => ?_) right
      · intro same
        simp only [Fin.append_left, Fin.append_right] at same
        exact False.elim (separate right left same.symm)
      · intro same
        simp only [Fin.append_right] at same
        exact congrArg (Fin.natAdd controls) (distinct same)
  source_output_ne := by
    intro index
    refine Fin.addCases (fun index => ?_) (fun index => ?_) index
    · simpa only [Fin.append_left] using layout.source_output_ne index
    · simpa only [Fin.append_right] using output index
  source_work_ne := by
    intro index
    refine Fin.addCases (fun index => ?_) (fun index => ?_) index
    · simpa only [Fin.append_left] using layout.source_work_ne index
    · simpa only [Fin.append_right] using work index
  work_output_ne := layout.work_output_ne

/-- Matching the complete actual source is exactly matching both original ordered source words. -/
lemma appendSources_matches (layout : OneDirtyLayout (encoding := encoding) controls)
    (word : Word encoding extra)
    (distinct : Function.Injective (fun index => (word.bit index).wire))
    (separate : ∀ left right, (layout.source.bit left).wire ≠ (word.bit right).wire)
    (output : ∀ index, (word.bit index).wire ≠ layout.output.wire)
    (work : ∀ index, (word.bit index).wire ≠ layout.work.wire)
    (first : Fin controls → Bool) (second : Fin extra → Bool) (state : Data) :
    (layout.appendSources word distinct separate output work).PatternMatches
        (Fin.append first second) state ↔
      layout.PatternMatches first state ∧
        ∀ index, (word.bit index).get state = second index := by
  constructor
  · intro matched
    constructor
    · intro index
      simpa only [appendSources, Fin.append_left] using matched (index.castAdd extra)
    · intro index
      simpa only [appendSources, Fin.append_right] using matched (index.natAdd controls)
  · rintro ⟨firstMatches, secondMatches⟩ index
    refine Fin.addCases (fun index => ?_) (fun index => ?_) index
    · simpa only [appendSources, Fin.append_left] using firstMatches index
    · simpa only [appendSources, Fin.append_right] using secondMatches index

end

end QuantumAlg.EncodedBit.Word.OneDirtyLayout
