/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Invariant.Step

/-!
# Original target sum through the final actual high-target carry row

The outgoing system in the final row is the original target high bit. Its
arbitrary current value is retained and xored with the original arithmetic
carry. No additional carry or output system is introduced
[G25, main.tex:239-251].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {layout : Layout encoding width} {constant : BitVec width} {initial current : Data}

/-- The actual outgoing system retains its original value xored with the next original carry. -/
lemma prefixInvariant_outgoing_xor (wide : 2 ≤ width) (index : Fin (width - 1))
    (invariant : layout.PrefixInvariant constant initial current index.val) :
    (layout.nextCarry wide index).get
        (wordLabel (layout.streamingStep wide constant index) current) =
      ((layout.nextCarry wide index).get current ^^
        layout.carryInto constant initial (index.val + 1)) := by
  rw [streamingStep_outgoing, prefixInvariant_source index invariant, invariant.control,
    prefixInvariant_incoming_helper invariant, Bool.xor_assoc]
  have firstChoice :
      (if index.val = 0 then constant.getLsbD index.val && layout.control.get initial
       else layout.carryInto constant initial index.val ^^
         (constant.getLsbD index.val && layout.control.get initial)) =
      (layout.carryInto constant initial index.val ^^
        (constant.getLsbD index.val && layout.control.get initial)) := by
    by_cases first : index.val = 0
    · rw [if_pos first, first]
      simp only [carryInto, Nat.BinaryArithmetic.natAddCarry, Bool.false_xor]
    · rw [if_neg first]
  rw [firstChoice, carry_eq_affine_toffoli, ← carryInto_succ layout constant initial
    index.val (by omega)]

/-- The final actual carry xors directly into the original most significant target system. -/
lemma prefixInvariant_final_high (wide : 2 ≤ width) (index : Fin (width - 1))
    (final : ¬ index.val + 1 < width - 1)
    (invariant : layout.PrefixInvariant constant initial current index.val) :
    (layout.target ⟨width - 1, by omega⟩).get
        (wordLabel (layout.streamingStep wide constant index) current) =
      ((layout.target ⟨width - 1, by omega⟩).get current ^^
        layout.carryInto constant initial (width - 1)) := by
  have carryIndex : index.val + 1 = width - 1 := by have inside := index.isLt; omega
  have outgoing := prefixInvariant_outgoing_xor wide index invariant
  rw [nextCarry, if_neg final, carryIndex] at outgoing
  exact outgoing

/-- After the final actual row, every original target is its input/offset/carry sum bit. -/
lemma prefixInvariant_final_target (wide : 2 ≤ width) (index : Fin (width - 1))
    (final : ¬ index.val + 1 < width - 1)
    (invariant : layout.PrefixInvariant constant initial current index.val)
    (observed : Fin width) :
    (layout.target observed).get
        (wordLabel (layout.streamingStep wide constant index) current) =
      (((layout.target observed).get initial ^^
        (constant.getLsbD observed.val && layout.control.get initial)) ^^
          layout.carryInto constant initial observed.val) := by
  have last : index.val + 1 = width - 1 := by have inside := index.isLt; omega
  by_cases high : observed.val = width - 1
  · have observedEq : observed = ⟨width - 1, by omega⟩ := Fin.ext high
    rw [observedEq, prefixInvariant_final_high wide index final invariant, invariant.target,
      if_neg (by omega : ¬ width - 1 < index.val), Bool.xor_false]
  · by_cases source : observed.val = index.val
    · have sourceEq : observed = ⟨index.val, by omega⟩ := Fin.ext source
      rw [sourceEq, streamingStep_target, prefixInvariant_source index invariant,
        prefixInvariant_incoming_helper invariant]
      by_cases positive : 0 < index.val
      · rw [if_pos positive]
      · have first : index.val = 0 := by omega
        have carryZero : layout.carryInto constant initial index.val = false := by
          rw [first]
          rfl
        rw [if_neg positive, carryZero]
    · have nextDifferent : (layout.nextCarry wide index).wire ≠
          (layout.target observed).wire := by
        rw [nextCarry, if_neg final]
        exact layout.target_target_ne (fun same => high (congrArg Fin.val same).symm)
      rw [streamingStep_target_other layout wide constant index observed
        (Ne.symm source) nextDifferent, invariant.target, if_pos (by
          have inside := observed.isLt
          omega : observed.val < index.val)]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
