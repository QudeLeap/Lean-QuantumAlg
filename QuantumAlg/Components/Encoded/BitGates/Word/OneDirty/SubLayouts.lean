/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Layout
import all QuantumAlg.Components.Encoded.BitGates.Word.Dirty.ZeroTest

/-!
# Two physical conjunction sublayouts sharing one dirty bit

The first conjunction targets the external work bit, with controls in the
larger group and borrowed temporary bits in the smaller group. The second
targets the final output, controls on the work bit followed by the smaller
group, and borrows temporary bits from the larger group. Both sublayouts
use the same actual encoded wires and certify every required separation.

The borrowed-work conjunction implementation restores its temporary bits
without assuming their values. No additional physical system is allocated.
-/

namespace QuantumAlg.EncodedBit.Word.OneDirtyLayout

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {controls : Nat}
variable (layout : OneDirtyLayout (encoding := encoding) controls)

private def firstSourceEquiv (large : 3 ≤ controls) :
    Fin (firstWidth controls - 2 + 2) ≃ Fin (firstWidth controls) :=
  finCongr (Nat.sub_add_cancel (balanced_widths large).1)

private def secondSourceEquiv (large : 3 ≤ controls) :
    Fin (secondWidth controls - 1 + 2) ≃ Fin (secondWidth controls + 1) :=
  finCongr (by have positive := (balanced_widths large).2.1; omega)

private def firstWorkIndex (large : 3 ≤ controls)
    (index : Fin (firstWidth controls - 2)) : Fin (secondWidth controls) :=
  ⟨index.val, lt_of_lt_of_le index.isLt (balanced_widths large).2.2.1⟩

private def secondWorkIndex (large : 3 ≤ controls)
    (index : Fin (secondWidth controls - 1)) : Fin (firstWidth controls) :=
  ⟨index.val, lt_of_lt_of_le index.isLt (balanced_widths large).2.2.2⟩

private lemma firstWorkIndex_injective (large : 3 ≤ controls) :
    Function.Injective (firstWorkIndex large) := by
  intro left right same
  exact Fin.ext (congrArg (fun index : Fin (secondWidth controls) => index.val) same)

private lemma secondWorkIndex_injective (large : 3 ≤ controls) :
    Function.Injective (secondWorkIndex large) := by
  intro left right same
  exact Fin.ext (congrArg (fun index : Fin (firstWidth controls) => index.val) same)

/-- The first actual conjunction uses the leading controls and targets the external dirty bit. -/
def firstSubLayout (large : 3 ≤ controls) :
    ZeroTestLayout (encoding := encoding) (firstWidth controls - 2) where
  source := ⟨fun index => layout.firstBit (firstSourceEquiv large index)⟩
  output := layout.work
  work := ⟨fun index => layout.secondBit (firstWorkIndex large index)⟩
  source_source_ne _left _right different := fun same =>
    different ((firstSourceEquiv large).injective (layout.firstBit_injective same))
  source_output_ne index := layout.source_work_ne (firstIndex (firstSourceEquiv large index))
  source_work_ne left right :=
    layout.firstBit_secondBit_ne (firstSourceEquiv large left) (firstWorkIndex large right)
  work_work_ne _left _right different := fun same =>
    different (firstWorkIndex_injective large (layout.secondBit_injective same))
  work_output_ne index := layout.source_work_ne (secondIndex (firstWorkIndex large index))

/-- The second conjunction controls first on the external work bit, then on the smaller group. -/
def secondControl : Fin (secondWidth controls + 1) → EncodedBit encoding :=
  Fin.cases layout.work layout.secondBit

private lemma secondControl_injective :
    Function.Injective (fun index => (layout.secondControl index).wire) := by
  intro left right
  refine Fin.cases ?_ (fun left => ?_) left
  · refine Fin.cases ?_ (fun right => ?_) right
    · intro _
      rfl
    · intro same
      exact False.elim ((layout.source_work_ne (secondIndex right)) same.symm)
  · refine Fin.cases ?_ (fun right => ?_) right
    · intro same
      exact False.elim ((layout.source_work_ne (secondIndex left)) same)
    · intro same
      exact congrArg Fin.succ (layout.secondBit_injective same)

private lemma secondControl_output_ne (index : Fin (secondWidth controls + 1)) :
    (layout.secondControl index).wire ≠ layout.output.wire := by
  refine Fin.cases ?_ (fun index => ?_) index
  · exact layout.work_output_ne
  · exact layout.source_output_ne (secondIndex index)

private lemma secondControl_firstBit_ne (index : Fin (secondWidth controls + 1))
    (first : Fin (firstWidth controls)) :
    (layout.secondControl index).wire ≠ (layout.firstBit first).wire := by
  refine Fin.cases ?_ (fun index => ?_) index
  · exact (layout.source_work_ne (firstIndex first)).symm
  · exact (layout.firstBit_secondBit_ne first index).symm

/-- The second actual conjunction targets the output and borrows only leading control wires. -/
def secondSubLayout (large : 3 ≤ controls) :
    ZeroTestLayout (encoding := encoding) (secondWidth controls - 1) where
  source := ⟨fun index => layout.secondControl (secondSourceEquiv large index)⟩
  output := layout.output
  work := ⟨fun index => layout.firstBit (secondWorkIndex large index)⟩
  source_source_ne _left _right different := fun same =>
    different ((secondSourceEquiv large).injective (layout.secondControl_injective same))
  source_output_ne index := layout.secondControl_output_ne (secondSourceEquiv large index)
  source_work_ne left right :=
    layout.secondControl_firstBit_ne (secondSourceEquiv large left) (secondWorkIndex large right)
  work_work_ne _left _right different := fun same =>
    different (secondWorkIndex_injective large (layout.firstBit_injective same))
  work_output_ne index := layout.source_output_ne (firstIndex (secondWorkIndex large index))

/-- The first sublayout tests exactly the original larger group. -/
lemma firstSubLayout_source_all (large : 3 ≤ controls) (state : Data) :
    (∀ index, ((layout.firstSubLayout large).source.bit index).get state = true) ↔
      ∀ index, (layout.firstBit index).get state = true := by
  constructor
  · intro allBits index
    have selected := allBits ((firstSourceEquiv large).symm index)
    change (layout.firstBit (firstSourceEquiv large
      ((firstSourceEquiv large).symm index))).get state = true at selected
    simpa only [Equiv.apply_symm_apply] using selected
  · intro allBits index
    exact allBits (firstSourceEquiv large index)

/-- The second sublayout tests the smaller group and the current actual dirty bit. -/
lemma secondSubLayout_source_all (large : 3 ≤ controls) (state : Data) :
    (∀ index, ((layout.secondSubLayout large).source.bit index).get state = true) ↔
      (∀ index, (layout.secondBit index).get state = true) ∧ layout.work.get state = true := by
  have allControls :
      (∀ index, ((layout.secondSubLayout large).source.bit index).get state = true) ↔
        ∀ index, (layout.secondControl index).get state = true := by
    constructor
    · intro allBits index
      have selected := allBits ((secondSourceEquiv large).symm index)
      change (layout.secondControl (secondSourceEquiv large
        ((secondSourceEquiv large).symm index))).get state = true at selected
      simpa only [Equiv.apply_symm_apply] using selected
    · intro allBits index
      exact allBits (secondSourceEquiv large index)
  rw [allControls]
  constructor
  · intro allBits
    exact ⟨fun index => allBits index.succ, allBits 0⟩
  · rintro ⟨second, work⟩ index
    exact Fin.cases work second index

end

end QuantumAlg.EncodedBit.Word.OneDirtyLayout
