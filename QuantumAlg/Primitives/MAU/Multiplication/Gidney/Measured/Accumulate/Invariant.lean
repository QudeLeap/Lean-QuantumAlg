/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Frame
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Layout.Readout
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Stages.Second
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Stages.First
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Arithmetic

/-!
# Actual canonical target, clean flag and helper promises at every MAC row

The arithmetic promise is propagated through each literal modular-addition
row at its actual intermediate label. No source selector or dirty bit is
initialized, and source bits used by later rows retain their original values
[G25, main.tex:199-295,271-295,354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open Addition.Gidney.Measured.Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The actual arithmetic entry promise initializes exactly the helpers and flag. -/
structure Ready (layout : Layout encoding width) (modulus : BitVec width)
    (state : Data) : Prop where
  clean : ∀ helper, (layout.clean helper).get state = false
  flag : layout.flag.get state = false
  canonical : (layout.targetWord state).toNat < modulus.toNat

/-- The complete actual row computes the independently specified selected modular offset. -/
lemma modularRow_target_nat (layout : Layout encoding width) (wide : 2 ≤ width)
    (selector : Fin width) (modulus constant : BitVec width)
    (canonical : constant.toNat < modulus.toNat) (initial : Data)
    (ready : layout.Ready modulus initial) :
    (layout.targetWord
      (wordLabel ((layout.reductionLayout selector).modularWord wide modulus constant)
        initial)).toNat =
      if layout.control.get initial && (layout.source selector).get initial then
        ((layout.targetWord initial).toNat + constant.toNat) % modulus.toNat else
          (layout.targetWord initial).toNat := by
  have actual := Addition.Gidney.Measured.Reduction.Layout.modularWord_target_nat
    (layout.reductionLayout selector) wide modulus constant canonical initial ready.canonical
    ready.clean ready.flag
  have activeSame : (layout.reductionLayout selector).activeValue initial =
      (layout.control.get initial && (layout.source selector).get initial) := by
    rw [Addition.Gidney.Measured.Reduction.Layout.activeValue,
      reductionLayout_control, reductionLayout_selector]
  have targetSame :
      (layout.targetWord
        (wordLabel ((layout.reductionLayout selector).modularWord wide modulus constant)
          initial)).toNat =
        Addition.Gidney.Measured.Reduction.output modulus.toNat constant.toNat
          (layout.targetWord initial).toNat
          ((layout.reductionLayout selector).activeValue initial) := by
    simpa only [reductionLayout_sourceWord] using actual
  exact targetSame.trans (congrArg
    (Addition.Gidney.Measured.Reduction.output modulus.toNat constant.toNat
      (layout.targetWord initial).toNat) activeSame)

/-- One actual measured row returns the original helpers and flag and a canonical target. -/
lemma modularRow_ready (layout : Layout encoding width) (wide : 2 ≤ width)
    (selector : Fin width) (modulus constant : BitVec width)
    (canonical : constant.toNat < modulus.toNat) (initial : Data)
    (ready : layout.Ready modulus initial) :
    layout.Ready modulus
      (wordLabel ((layout.reductionLayout selector).modularWord wide modulus constant)
        initial) where
  clean := (modularRow_frame layout wide selector modulus constant initial ready.clean).clean
  flag := Addition.Gidney.Measured.Reduction.Layout.modularWord_flag_zero
    (layout.reductionLayout selector) wide modulus constant canonical initial ready.canonical
    ready.clean ready.flag
  canonical := by
    rw [modularRow_target_nat layout wide selector modulus constant canonical initial ready]
    split
    · exact Nat.mod_lt _ (by omega)
    · exact ready.canonical

/-- Every actual source-order prefix supplies the next row's real clean and canonical input. -/
lemma accumulatePrefixWord_ready (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (constants : Fin width → BitVec width)
    (canonical : ∀ index, (constants index).toNat < modulus.toNat)
    (count : Nat) (bounded : count ≤ width) (initial : Data)
    (ready : layout.Ready modulus initial) :
    layout.Ready modulus
      (wordLabel (layout.accumulatePrefixWord wide modulus constants count bounded) initial) := by
  induction count with
  | zero => exact ready
  | succ count ih =>
      rw [accumulatePrefixWord, wordLabel_append]
      exact modularRow_ready layout wide ⟨count, by omega⟩ modulus _
        (canonical ⟨count, by omega⟩) _ (ih (by omega))

/-- A purely arithmetic selected-offset scan, using the original source bits and global control. -/
def selectedPrefixValue (modulus : BitVec width) (constants : Fin width → BitVec width)
    (source : BitVec width) (enabled : Bool) (initial : Nat) :
    (count : Nat) → count ≤ width → Nat
  | 0, _ => initial
  | count + 1, bounded =>
      let earlier := selectedPrefixValue modulus constants source enabled initial count (by omega)
      if enabled && source.toNat.testBit count then
        (earlier + (constants ⟨count, by omega⟩).toNat) % modulus.toNat else earlier

/-- The actual chronological measured word realizes the independent selected-offset recurrence. -/
lemma accumulatePrefixWord_target_nat (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (constants : Fin width → BitVec width)
    (canonical : ∀ index, (constants index).toNat < modulus.toNat)
    (count : Nat) (bounded : count ≤ width) (initial : Data)
    (ready : layout.Ready modulus initial) :
    (layout.targetWord
      (wordLabel (layout.accumulatePrefixWord wide modulus constants count bounded)
        initial)).toNat =
      selectedPrefixValue modulus constants (layout.sourceWord initial) (layout.control.get initial)
        (layout.targetWord initial).toNat count bounded := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [accumulatePrefixWord, wordLabel_append]
      have earlierReady := accumulatePrefixWord_ready layout wide modulus constants canonical
        count (by omega) initial ready
      have frame := accumulatePrefixWord_frame layout wide modulus constants count (by omega)
        initial ready.clean
      rw [modularRow_target_nat layout wide ⟨count, by omega⟩ modulus _
        (canonical ⟨count, by omega⟩) _ earlierReady,
        frame.control, ← multiplicationSourceWord_bit layout _ count (by omega), frame.source,
        ih (by omega), selectedPrefixValue]

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
