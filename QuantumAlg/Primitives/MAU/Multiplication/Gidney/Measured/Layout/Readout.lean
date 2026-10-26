/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Layout.Reduction
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Comparison.Readout
import Batteries.Data.BitVec.Lemmas

/-!
# Original addressed multiplication words and exact selected-row readouts

Every modular row retains the same global control, current source selector,
target, clean helpers and flag. Its dirty outputs are the proven distinct
unselected original source bits [G25, main.tex:271-295,354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The complete original little-endian source word. -/
def sourceWord (layout : Layout encoding width) (state : Data) : BitVec width :=
  BitVec.ofFnLE fun index => (layout.source index).get state

/-- The complete original little-endian target accumulator word. -/
def targetWord (layout : Layout encoding width) (state : Data) : BitVec width :=
  BitVec.ofFnLE fun index => (layout.target index).get state

/-- Every bounded source bit is its original physical selector readout. -/
lemma multiplicationSourceWord_bit (layout : Layout encoding width) (state : Data)
    (index : Nat) (inside : index < width) :
    (layout.sourceWord state).toNat.testBit index =
      (layout.source ⟨index, inside⟩).get state := by
  rw [BitVec.testBit_toNat, sourceWord, BitVec.getLsbD_ofFnLE, dif_pos inside]

/-- Every bounded target bit is its original physical accumulator readout. -/
lemma multiplicationTargetWord_bit (layout : Layout encoding width) (state : Data)
    (index : Nat) (inside : index < width) :
    (layout.targetWord state).toNat.testBit index =
      (layout.target ⟨index, inside⟩).get state := by
  rw [BitVec.testBit_toNat, targetWord, BitVec.getLsbD_ofFnLE, dif_pos inside]

/-- The selected row's global control is the original multiplication control. -/
lemma reductionLayout_control (layout : Layout encoding width) (selector : Fin width) :
    (layout.reductionLayout selector).control = layout.control := rfl

/-- The row's second active control is exactly the current original source bit. -/
lemma reductionLayout_selector (layout : Layout encoding width) (selector : Fin width) :
    (layout.reductionLayout selector).selector = layout.source selector := rfl

/-- Every row target is the same original accumulator bit. -/
lemma reductionLayout_target (layout : Layout encoding width) (selector index : Fin width) :
    (layout.reductionLayout selector).target index = layout.target index := rfl

/-- Each row dirty output is its original unselected source bit. -/
lemma reductionLayout_dirty (layout : Layout encoding width) (selector : Fin width)
    (index : Fin (width - 2)) :
    (layout.reductionLayout selector).dirty index =
      layout.source (dirtySourceIndex selector index) := rfl

/-- Every row reuses the same original two clean helpers. -/
lemma reductionLayout_clean (layout : Layout encoding width) (selector : Fin width)
    (index : Fin 2) :
    (layout.reductionLayout selector).clean index = layout.clean index := rfl

/-- Every row reuses the same original reduction flag. -/
lemma reductionLayout_flag (layout : Layout encoding width) (selector : Fin width) :
    (layout.reductionLayout selector).flag = layout.flag := rfl

/-- The row's actual compared word is exactly the original target accumulator word. -/
lemma reductionLayout_sourceWord (layout : Layout encoding width) (selector : Fin width)
    (state : Data) :
    (layout.reductionLayout selector).sourceWord state = layout.targetWord state := rfl

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
