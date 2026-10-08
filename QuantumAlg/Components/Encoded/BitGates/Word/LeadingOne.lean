/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Pattern

/-!
# Actual fixed-prefix equality and leading-one selection with one dirty bit

A retained prefix first matches a fixed key. The following word, read in
most-significant-first order, has zero bits before a selected position and
one at that position. One actual pattern list toggles the designated output
for precisely this condition and restores every other bit, including its
single arbitrary work bit [G17, paper.tex:278-293].

This is the elementary highest-valid-position predicate needed for reversible
length XOR writes [LYL+26, sec_circuit/sub_block_new.tex:211-224,338-341]. The
prefix, candidate position, and expected key are fixed circuit parameters;
all their quantum source values are read by the actual native gate list.
-/

namespace QuantumAlg.EncodedBit.Word.OneDirtyLayout

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {prefixWidth width : Nat}

private def keyIndex (index : Fin prefixWidth) : Fin (prefixWidth + width) :=
  ⟨index.val, by have within := index.isLt; omega⟩

private def wordIndex (index : Fin width) : Fin (prefixWidth + width) :=
  ⟨prefixWidth + index.val, by have within := index.isLt; omega⟩

private def sourceIndex (position : Fin width) (index : Fin (prefixWidth + (position.val + 1))) :
    Fin (prefixWidth + width) :=
  ⟨index.val, by have within := index.isLt; have selected := position.isLt; omega⟩

/-- Restrict the actual source coordinates to the full fixed prefix and selected word prefix. -/
def leadingLayout (layout : OneDirtyLayout (encoding := encoding) (prefixWidth + width))
    (position : Fin width) :
    OneDirtyLayout (encoding := encoding) (prefixWidth + (position.val + 1)) where
  source := ⟨fun index => layout.source.bit (sourceIndex position index)⟩
  output := layout.output
  work := layout.work
  source_injective := by
    intro left right same
    have positions := layout.source_injective same
    exact Fin.ext (congrArg (fun index : Fin (prefixWidth + width) => index.val) positions)
  source_output_ne index := layout.source_output_ne (sourceIndex position index)
  source_work_ne index := layout.source_work_ne (sourceIndex position index)
  work_output_ne := layout.work_output_ne

/-- The actual static key bits, followed by zeros and the candidate's one bit. -/
def leadingPattern (position : Fin width) (expected : Fin prefixWidth → Bool)
    (index : Fin (prefixWidth + (position.val + 1))) : Bool :=
  if before : index.val < prefixWidth then expected ⟨index.val, before⟩
  else decide (index.val = prefixWidth + position.val)

/-- The original source prefix matches its key and the word's first one is at this position. -/
def PrefixLeading (layout : OneDirtyLayout (encoding := encoding) (prefixWidth + width))
    (position : Fin width) (expected : Fin prefixWidth → Bool) (state : Data) : Prop :=
  (∀ index : Fin prefixWidth, (layout.source.bit (keyIndex index)).get state = expected index) ∧
    (∀ previous : Fin position.val,
      (layout.source.bit (wordIndex ⟨previous.val,
        by have before := previous.isLt; have within := position.isLt; omega⟩)).get state = false) ∧
    (layout.source.bit (wordIndex position)).get state = true

private instance prefixLeadingDecidable
    (layout : OneDirtyLayout (encoding := encoding) (prefixWidth + width))
    (position : Fin width) (expected : Fin prefixWidth → Bool) (state : Data) :
    Decidable (layout.PrefixLeading position expected state) := by
  unfold PrefixLeading
  infer_instance

/-- The exact actual pattern reads precisely the fixed key and the first-one condition. -/
theorem leadingPattern_iff
    (layout : OneDirtyLayout (encoding := encoding) (prefixWidth + width))
    (position : Fin width) (expected : Fin prefixWidth → Bool) (state : Data) :
    (layout.leadingLayout position).PatternMatches (leadingPattern position expected) state ↔
      layout.PrefixLeading position expected state := by
  constructor
  · intro matched
    refine ⟨?_, ?_, ?_⟩
    · intro index
      have seen := matched (⟨index.val, by have within := index.isLt; omega⟩ :
        Fin (prefixWidth + (position.val + 1)))
      change (layout.source.bit (keyIndex index)).get state =
        leadingPattern position expected ⟨index.val, _⟩ at seen
      simpa only [leadingPattern, dif_pos index.isLt] using seen
    · intro previous
      let selected : Fin (prefixWidth + (position.val + 1)) :=
        ⟨prefixWidth + previous.val, by have before := previous.isLt; omega⟩
      have seen := matched selected
      have later : ¬selected.val < prefixWidth := by dsimp [selected]; omega
      have notLast : selected.val ≠ prefixWidth + position.val := by
        dsimp [selected]
        have before := previous.isLt
        omega
      change (layout.source.bit (sourceIndex position selected)).get state =
        leadingPattern position expected selected at seen
      have same : sourceIndex position selected = wordIndex
          (⟨previous.val, previous.isLt.trans position.isLt⟩ : Fin width) := rfl
      rw [same] at seen
      simpa only [leadingPattern, dif_neg later, decide_eq_false notLast] using seen
    · let selected : Fin (prefixWidth + (position.val + 1)) :=
        ⟨prefixWidth + position.val, by omega⟩
      have seen := matched selected
      have later : ¬selected.val < prefixWidth := by dsimp [selected]; omega
      change (layout.source.bit (wordIndex position)).get state =
        leadingPattern position expected selected at seen
      have last : selected.val = prefixWidth + position.val := rfl
      simpa only [leadingPattern, dif_neg later, decide_eq_true last] using seen
  · rintro ⟨key, zeros, one⟩ index
    change (layout.source.bit (sourceIndex position index)).get state =
      leadingPattern position expected index
    by_cases before : index.val < prefixWidth
    · rw [leadingPattern, dif_pos before]
      exact key ⟨index.val, before⟩
    · rw [leadingPattern, dif_neg before]
      by_cases last : index.val = prefixWidth + position.val
      · rw [decide_eq_true last]
        have same : sourceIndex position index = wordIndex position := Fin.ext last
        rw [same]
        exact one
      · rw [decide_eq_false last]
        have earlier : index.val - prefixWidth < position.val := by
          have within := index.isLt
          omega
        have same : sourceIndex position index = wordIndex
            (⟨index.val - prefixWidth, earlier.trans position.isLt⟩ : Fin width) := by
          apply Fin.ext
          change index.val = prefixWidth + (index.val - prefixWidth)
          omega
        rw [same]
        exact zeros ⟨index.val - prefixWidth, earlier⟩

/-- The actual masked conjunction toggles its real output and restores its arbitrary work bit. -/
def leadingOneGates (layout : OneDirtyLayout (encoding := encoding) (prefixWidth + width))
    (position : Fin width) (expected : Fin prefixWidth → Bool) : List (GateSpec encoding) :=
  (layout.leadingLayout position).patternGates (leadingPattern position expected)

/-- Exact complete-state action of the emitted prefix/leading-one native gate list. -/
theorem leadingOneGates_step
    (layout : OneDirtyLayout (encoding := encoding) (prefixWidth + width))
    (position : Fin width) (expected : Fin prefixWidth → Bool) (state : Data) :
    GateSpec.stepList (layout.leadingOneGates position expected) state =
      if layout.PrefixLeading position expected state then layout.output.flip state else state := by
  have output : (layout.leadingLayout position).output = layout.output := rfl
  rw [leadingOneGates, patternGates_step, output]
  simp only [leadingPattern_iff]

/-- The actual native program retains the complete predicate-controlled basis amplitudes. -/
theorem leadingOneGates_realizes
    (layout : OneDirtyLayout (encoding := encoding) (prefixWidth + width))
    (position : Fin width) (expected : Fin prefixWidth → Bool) :
    UnitaryCircuit.Realizes encoding (layout := QubitLayout.canonical encoding.width)
      (GateSpec.programList (QubitLayout.canonical encoding.width) .empty
        (layout.leadingOneGates position expected))
      (fun state => if layout.PrefixLeading position expected state
        then layout.output.flip state else state) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical encoding.width) .empty _
    (layout.leadingOneGates_step position expected)

/-- Every actual borrowed-work bit returns unchanged, without an initialization condition. -/
theorem leadingOneGates_work
    (layout : OneDirtyLayout (encoding := encoding) (prefixWidth + width))
    (position : Fin width) (expected : Fin prefixWidth → Bool) (state : Data) :
    layout.work.get (GateSpec.stepList (layout.leadingOneGates position expected) state) =
      layout.work.get state :=
  (layout.leadingLayout position).patternGates_work_restored _ state

/-- Count includes all actual negative masks and the complete dirty conjunction cleanup. -/
theorem leadingOneGates_length_le
    (layout : OneDirtyLayout (encoding := encoding) (prefixWidth + width))
    (position : Fin width) (expected : Fin prefixWidth → Bool) :
    (layout.leadingOneGates position expected).length ≤
      10 * (prefixWidth + (position.val + 1)) + 1 :=
  (layout.leadingLayout position).patternGates_length_le _

end

end QuantumAlg.EncodedBit.Word.OneDirtyLayout
