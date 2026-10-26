/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Values
import Batteries.Data.BitVec.Lemmas

/-!
# Original addressed target-word carries and the actual native carry prefix

Little-endian target ports determine the complete finite word. The quantum
control selects either the same static constant or zero. These arithmetic
identities connect the actual native prefix's port recurrence to finite-word
addition, without any condition on dirty-output or reference values
[G25, main.tex:209-239,253-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Read the original target through the same addressed little-endian physical ports. -/
def targetWord (layout : Layout encoding width) (state : Data) : BitVec width :=
  BitVec.ofFnLE fun index => (layout.target index).get state

/-- The same coherent control label selects the static offset, including the zero-control case. -/
def selectedOffsetWord (layout : Layout encoding width) (constant : BitVec width)
    (state : Data) : BitVec width :=
  if layout.control.get state then constant else 0

/-- Every bounded read of the original target word is its actual addressed physical bit. -/
lemma targetWord_bit (layout : Layout encoding width) (state : Data)
    (index : Nat) (inside : index < width) :
    (layout.targetWord state).toNat.testBit index =
      (layout.target ⟨index, inside⟩).get state := by
  rw [BitVec.testBit_toNat, targetWord, BitVec.getLsbD_ofFnLE, dif_pos inside]

/-- The selected finite offset reads exactly the static bit conjoined with the quantum control. -/
lemma selectedOffsetWord_bit (layout : Layout encoding width) (constant : BitVec width)
    (state : Data) (index : Nat) :
    (layout.selectedOffsetWord constant state).toNat.testBit index =
      (constant.getLsbD index && layout.control.get state) := by
  cases control : layout.control.get state <;>
    simp [selectedOffsetWord, control, BitVec.testBit_toNat]

/-- Carry entering a source position of the original target and selected static offset. -/
def carryInto (layout : Layout encoding width) (constant : BitVec width) (state : Data) :
    Nat → Bool :=
  Nat.BinaryArithmetic.natAddCarry (layout.targetWord state).toNat
    (layout.selectedOffsetWord constant state).toNat

/-- The same original source/control values drive the finite-word carry recurrence. -/
lemma carryInto_succ (layout : Layout encoding width) (constant : BitVec width) (state : Data)
    (index : Nat) (inside : index < width) :
    layout.carryInto constant state (index + 1) =
      Bool.carry ((layout.target ⟨index, inside⟩).get state)
        (constant.getLsbD index && layout.control.get state)
        (layout.carryInto constant state index) := by
  rw [carryInto, Nat.BinaryArithmetic.natAddCarry, targetWord_bit _ _ _ inside,
    selectedOffsetWord_bit]

/-- The proved actual native carry-output recurrence computes these same original word carries. -/
lemma carryValues_eq_carryInto (layout : Layout encoding width) (constant : BitVec width)
    (state : Data) (count : Nat) (bounded : count ≤ width - 2) :
    layout.carryLayout.carryValues (constant.setWidth (width - 2)) state count =
      layout.carryInto constant state count := by
  revert bounded
  induction count with
  | zero => intro _; rfl
  | succ count ih =>
      intro bounded
      have inside : count < width - 2 := by omega
      rw [CarryLayout.carryValues, dif_pos inside, ih (by omega),
        carryInto_succ _ _ _ count (by omega), BitVec.getLsbD_setWidth]
      simp only [decide_eq_true inside, Bool.true_and, carryLayout]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
