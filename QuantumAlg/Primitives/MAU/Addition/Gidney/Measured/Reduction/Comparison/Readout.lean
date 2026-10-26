/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Comparison.Layout
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Values
import Batteries.Data.BitVec.Lemmas

/-!
# Original physical comparison-source word and its exact arithmetic carry

The addressed target bits determine the little-endian input. The native
carry recurrence reads exactly those same physical bits and the actual
conjunction helper, with no premise on dirty outputs or the high flag
[G25, main.tex:209-239,253-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The complete original target word through its actual little-endian physical addresses. -/
def sourceWord (layout : Layout encoding width) (state : Data) : BitVec width :=
  BitVec.ofFnLE fun index => (layout.target index).get state

/-- Every bounded source-word bit is its original addressed physical target readout. -/
lemma comparisonSourceWord_bit (layout : Layout encoding width) (state : Data)
    (index : Nat) (inside : index < width) :
    (layout.sourceWord state).toNat.testBit index =
      (layout.target ⟨index, inside⟩).get state := by
  rw [BitVec.testBit_toNat, sourceWord, BitVec.getLsbD_ofFnLE, dif_pos inside]

private lemma selectedOffset_bit (layout : Layout encoding width) (constant : BitVec width)
    (state : Data) (index : Nat) :
    (if (layout.clean 1).get state then constant.toNat else 0).testBit index =
      (constant.getLsbD index && (layout.clean 1).get state) := by
  cases (layout.clean 1).get state <;> simp [BitVec.testBit_toNat]

/-- The native full-width carry is the arithmetic carry of those same original source reads. -/
lemma comparisonCarryValues_eq_nat (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (state : Data) (count : Nat) (bounded : count ≤ width) :
    (layout.comparisonLayout wide).carryValues constant state count =
      Nat.BinaryArithmetic.natAddCarry (layout.sourceWord state).toNat
        (if (layout.clean 1).get state then constant.toNat else 0) count := by
  revert bounded
  induction count with
  | zero => intro _; rfl
  | succ count ih =>
      intro bounded
      have inside : count < width := by omega
      rw [CarryLayout.carryValues, dif_pos inside, ih (by omega),
        Nat.BinaryArithmetic.natAddCarry, comparisonSourceWord_bit _ _ _ inside,
        selectedOffset_bit]
      rfl

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
