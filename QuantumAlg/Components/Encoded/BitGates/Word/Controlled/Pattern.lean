/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Pattern

/-!
# Actual pattern selection with an additional retained source control

One existing source control is prepended to a one-dirty pattern and given
the fixed expected value one. The actual mask/conjunction/inverse-mask
construction then conditionally executes the original pattern flip.
The same arbitrary work bit is restored; no additional dirty bit or
declared controlled oracle is introduced [G17, paper.tex:278-293].

The control is physically distinct from every original source, the
output, and the work. The complete resulting gate list has exact action
on all encoded values, including a false control and arbitrary work.
Its elementary count includes the new conjunction source and all masks.
-/

namespace QuantumAlg.EncodedBit.Word.OneDirtyLayout

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {controls : Nat}
variable (layout : OneDirtyLayout (encoding := encoding) controls) (control : EncodedBit encoding)
variable (sources : ∀ index, control.wire ≠ (layout.source.bit index).wire)
variable (output : control.wire ≠ layout.output.wire) (work : control.wire ≠ layout.work.wire)

/-- The retained control precedes every original source, using the same output and dirty work. -/
def controlledPatternLayout : OneDirtyLayout (encoding := encoding) (controls + 1) where
  source := ⟨Fin.cases control layout.source.bit⟩
  output := layout.output
  work := layout.work
  source_injective := by
    intro left right
    refine Fin.cases ?_ (fun left => ?_) left
    · refine Fin.cases ?_ (fun right => ?_) right
      · intro _
        rfl
      · intro same
        exact False.elim (sources right same)
    · refine Fin.cases ?_ (fun right => ?_) right
      · intro same
        exact False.elim (sources left same.symm)
      · intro same
        exact congrArg Fin.succ (layout.source_injective same)
  source_output_ne index := Fin.cases output layout.source_output_ne index
  source_work_ne index := Fin.cases work layout.source_work_ne index
  work_output_ne := layout.work_output_ne

/-- The additional physical source has expected value one before the original fixed pattern. -/
def controlledPatternValues (expected : Fin controls → Bool) : Fin (controls + 1) → Bool :=
  Fin.cases true expected

/-- Exact matching of the enlarged physical source is retained control and the original pattern. -/
lemma controlledPattern_matches (expected : Fin controls → Bool) (state : Data) :
    (layout.controlledPatternLayout control sources output work).PatternMatches
        (controlledPatternValues expected) state ↔
      control.get state = true ∧ layout.PatternMatches expected state := by
  constructor
  · intro matched
    exact ⟨matched 0, fun index => matched index.succ⟩
  · rintro ⟨selected, matched⟩ index
    exact Fin.cases selected matched index

/-- Compile the enlarged true-control pattern through the existing actual one-dirty gates. -/
def controlledPatternGates (expected : Fin controls → Bool) : List (GateSpec encoding) :=
  (layout.controlledPatternLayout control sources output work).patternGates
    (controlledPatternValues expected)

private lemma controlledPattern_result (expected : Fin controls → Bool) (state : Data) :
    (if (layout.controlledPatternLayout control sources output work).PatternMatches
        (controlledPatternValues expected) state then layout.output.flip state else state) =
      if control.get state then
        (if layout.PatternMatches expected state then layout.output.flip state else state)
      else state := by
  simp only [controlledPattern_matches]
  by_cases selected : control.get state = true <;> simp [selected]

/-- Full native-list action is the original exact pattern flip selected by the real control. -/
lemma controlledPatternGates_step (expected : Fin controls → Bool) (state : Data) :
    GateSpec.stepList (layout.controlledPatternGates control sources output work expected) state =
      if control.get state then
        (if layout.PatternMatches expected state then layout.output.flip state else state)
      else state := by
  unfold controlledPatternGates
  exact ((layout.controlledPatternLayout control sources output work).patternGates_step
    (controlledPatternValues expected) state).trans
      (layout.controlledPattern_result control sources output work expected state)

/-- The actual reversed list has the same full-state conditional flip, including false controls. -/
lemma controlledPatternGates_reverse_step (expected : Fin controls → Bool) (state : Data) :
    GateSpec.stepList (layout.controlledPatternGates control sources output work expected).reverse
        state =
      if control.get state then
        (if layout.PatternMatches expected state then layout.output.flip state else state)
      else state := by
  unfold controlledPatternGates
  exact ((layout.controlledPatternLayout control sources output work).patternGates_reverse_step
    (controlledPatternValues expected) state).trans
      (layout.controlledPattern_result control sources output work expected state)

/-- The original dirty work value is restored on every input without a cleanliness premise. -/
lemma controlledPatternGates_work (expected : Fin controls → Bool) (state : Data) :
    layout.work.get
        (GateSpec.stepList (layout.controlledPatternGates control sources output work expected)
          state) = layout.work.get state := by
  unfold controlledPatternGates
  exact (layout.controlledPatternLayout control sources output work).patternGates_work_restored
    (controlledPatternValues expected) state

/-- Actual pattern control retains exact encoded amplitudes and every original non-output value. -/
lemma controlledPatternGates_realizes {environment : OracleModel.empty.Interpretation} (expected
    : Fin controls → Bool) :
    UnitaryCircuit.Realizes encoding (layout := QubitLayout.canonical encoding.width)
      (GateSpec.programList (QubitLayout.canonical encoding.width) .empty
        (layout.controlledPatternGates control sources output work expected))
      environment (fun state => if control.get state then
        (if layout.PatternMatches expected state then layout.output.flip state else state)
      else state) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical encoding.width) .empty _
    (layout.controlledPatternGates_step control sources output work expected) environment

/-- Exact emitted length includes both original masks and the enlarged native conjunction. -/
lemma controlledPatternGates_length (expected : Fin controls → Bool) :
    (layout.controlledPatternGates control sources output work expected).length =
      2 * (patternMaskIndices (controlledPatternValues expected)).length +
        (layout.controlledPatternLayout control sources output work).gates.length := by
  unfold controlledPatternGates
  exact (layout.controlledPatternLayout control sources output work).patternGates_length
    (controlledPatternValues expected)

/-- A linear bound counts the additional actual control and the complete dirty cleanup. -/
lemma controlledPatternGates_length_le (expected : Fin controls → Bool) :
    (layout.controlledPatternGates control sources output work expected).length ≤
      10 * (controls + 1) + 1 := by
  unfold controlledPatternGates
  exact (layout.controlledPatternLayout control sources output work).patternGates_length_le
    (controlledPatternValues expected)

/-- Strict unit duration uses the complete actual elementary list. -/
lemma controlledPatternGates_unitDepth (expected : Fin controls → Bool) :
    (GateSpec.programList (QubitLayout.canonical encoding.width) .empty
      (layout.controlledPatternGates control sources output work expected)).evaluatedEventDepth
        (fun _ => 1) =
      (layout.controlledPatternGates control sources output work expected).length :=
  GateSpec.programList_evaluatedEventDepth_unit _ _ _

end

end QuantumAlg.EncodedBit.Word.OneDirtyLayout
