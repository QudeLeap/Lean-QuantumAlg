/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Gates

/-!
# Complete encoded-label actions of the actual streaming native rows

The affine Toffoli computes the next carry before either incoming-carry
extraction. Both extraction targets are original addressed systems. The
equations retain arbitrary dirty values and every untouched encoded label
[G25, main.tex:199-251,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The actual carry-compute row flips only its addressed outgoing carry target. -/
lemma computeCarryGates_step (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) (state : Data) :
    let source : Fin width := ⟨index.val, by omega⟩
    stepList (layout.computeCarryGates wide constant index) state =
      if (layout.target source).get state &&
          (if index.val = 0 then constant.getLsbD index.val && layout.control.get state
           else (layout.carryHelper index.val).get state ^^
             (constant.getLsbD index.val && layout.control.get state)) then
        (layout.nextCarry wide index).flip state
      else state := by
  dsimp only
  unfold computeCarryGates
  by_cases first : index.val = 0
  · rw [if_pos first, if_pos first]
    cases bit : constant.getLsbD index.val <;>
      simp [stepList, step, toffoliStep]
  · rw [if_neg first, if_neg first]
    dsimp only [carryHelper]
    rw [affineToffoliGates_step layout.control _ _ _
      (layout.control_target_ne _) (layout.control_clean_ne _)
      (layout.control_nextCarry_ne wide index) (layout.target_clean_ne _ _)
      (layout.target_nextCarry_ne wide index) (layout.carryHelper_nextCarry_ne wide index)]
    simp only [Bool.false_and, Bool.xor_false]
    rfl

/-- Both actual extraction CNOTs share the retained incoming carry and pay their own events. -/
lemma extractCarryGates_step (layout : Layout encoding width)
    (index : Fin (width - 1)) (positive : 0 < index.val) (state : Data) :
    let source : Fin width := ⟨index.val, by omega⟩
    let output : Fin (width - 2) := ⟨index.val - 1, by omega⟩
    stepList (layout.extractCarryGates index) state =
      if (layout.carryHelper index.val).get state then
        (layout.dirty output).flip ((layout.target source).flip state)
      else state := by
  dsimp only
  rw [extractCarryGates, dif_pos positive]
  change cnotStep (layout.carryHelper index.val) _
    (cnotStep (layout.carryHelper index.val) _ state) = _
  cases incoming : (layout.carryHelper index.val).get state <;>
    simp [cnotStep, incoming, get_flip_of_wire_ne (layout.target _) (layout.carryHelper index.val)
      (layout.target_clean_ne _ _)]

/-- The zero-incoming row has no extraction CNOT or dirty-output write. -/
lemma extractCarryGates_step_zero (layout : Layout encoding width)
    (index : Fin (width - 1)) (first : index.val = 0) (state : Data) :
    stepList (layout.extractCarryGates index) state = state := by
  rw [extractCarryGates, dif_neg (by omega : ¬ 0 < index.val)]
  rfl

/-- The final actual CNOT completes the affine majority carry by xoring the selected offset. -/
lemma finishCarryGates_step (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) (state : Data) :
    stepList (layout.finishCarryGates wide constant index) state =
      if constant.getLsbD index.val && layout.control.get state then
        (layout.nextCarry wide index).flip state
      else state := by
  unfold finishCarryGates
  cases bit : constant.getLsbD index.val <;>
    simp [stepList, step, cnotStep]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
