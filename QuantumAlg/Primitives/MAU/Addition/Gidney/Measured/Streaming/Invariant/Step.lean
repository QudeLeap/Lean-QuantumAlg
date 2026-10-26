/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Invariant.Carry
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Retention

/-!
# Preservation of the original-data invariant by each actual nonfinal row

The proof uses the exact outgoing carry, target/dirty extraction, physical
incoming-helper reset and untouched-port laws of the literal source row
[G25, main.tex:209-251,271-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {layout : Layout encoding width} {constant : BitVec width} {initial current : Data}

/-- Every actual nonfinal row advances the same original-data and two-clean-helper invariant. -/
lemma prefixInvariant_step (wide : 2 ≤ width) (count : Nat)
    (bounded : count + 1 ≤ width - 2)
    (invariant : layout.PrefixInvariant constant initial current count) :
    layout.PrefixInvariant constant initial
      (wordLabel (layout.streamingStep wide constant ⟨count, by omega⟩) current) (count + 1) := by
  let index : Fin (width - 1) := ⟨count, by omega⟩
  have nonfinal : index.val + 1 < width - 1 := by dsimp [index]; omega
  constructor
  · exact (streamingStep_control_get layout wide constant index current).trans invariant.control
  · intro observed
    by_cases same : observed.val = count
    · have sourceEq : (⟨index.val, by omega⟩ : Fin width) = observed :=
        Fin.ext (by dsimp [index]; exact same.symm)
      rw [← sourceEq, streamingStep_target, prefixInvariant_source index invariant,
        prefixInvariant_incoming_helper invariant]
      change (((layout.target ⟨count, by omega⟩).get initial ^^
        (constant.getLsbD count && layout.control.get initial)) ^^
          (if 0 < count then layout.carryInto constant initial count else false)) = _
      rw [if_pos (Nat.lt_succ_self count)]
      by_cases positive : 0 < count
      · rw [if_pos positive]
      · have zero : count = 0 := by omega
        have carryZero : layout.carryInto constant initial count = false := by
          rw [zero]
          rfl
        rw [if_neg positive, carryZero]
    · have nextDifferent : (layout.nextCarry wide index).wire ≠
          (layout.target observed).wire := by
        rw [nextCarry, if_pos nonfinal]
        exact (layout.target_clean_ne _ _).symm
      rw [streamingStep_target_other layout wide constant index observed
        (by dsimp [index]; omega) nextDifferent, invariant.target]
      by_cases before : observed.val < count
      · rw [if_pos before, if_pos (by omega : observed.val < count + 1)]
      · rw [if_neg before, if_neg (by omega : ¬ observed.val < count + 1)]
  · intro observed
    by_cases active : 0 < count ∧ observed.val + 1 = count
    · have positive : 0 < index.val := active.1
      have outputEq : (⟨index.val - 1, by omega⟩ : Fin (width - 2)) = observed :=
        Fin.ext (by dsimp [index]; omega)
      have previous : index.val - 1 + 1 = count := by dsimp [index]; omega
      rw [← outputEq, streamingStep_dirty layout wide constant index positive, invariant.dirty,
        prefixInvariant_incoming_helper invariant, previous,
        if_neg (Nat.lt_irrefl count), if_pos (Nat.lt_succ_self count), Bool.xor_false]
    · have different : 0 < index.val → index.val - 1 ≠ observed.val := by
        intro positive equal
        apply active
        constructor
        · exact positive
        · dsimp [index] at equal positive
          omega
      rw [streamingStep_dirty_other layout wide constant index observed different,
        invariant.dirty]
      have boundary : observed.val + 1 ≠ count := by
        intro equal
        apply active
        exact ⟨by omega, equal⟩
      by_cases before : observed.val + 1 < count
      · rw [if_pos before, if_pos (by omega : observed.val + 1 < count + 1)]
      · rw [if_neg before, if_neg (by omega : ¬ observed.val + 1 < count + 1)]
  · intro helper
    by_cases next : helper.val = (count + 1) % 2
    · have helperEq : layout.clean helper = layout.nextCarry wide index := by
        rw [nextCarry, if_pos nonfinal, carryHelper]
        congr 1
        exact Fin.ext next
      rw [helperEq, prefixInvariant_next_carry wide index nonfinal invariant, if_pos next]
    · have currentHelper : helper.val = count % 2 := by
        have boundedHelper := helper.isLt
        omega
      have helperEq : layout.clean helper = layout.carryHelper count := by
        unfold carryHelper
        congr 1
        exact Fin.ext currentHelper
      rw [helperEq]
      change (layout.carryHelper index.val).get
        (wordLabel (layout.streamingStep wide constant index) current) = _
      rw [streamingStep_incoming layout wide constant index current, if_neg next]
      by_cases positive : 0 < count
      · rw [if_pos positive]
      · have zero : count = 0 := by omega
        rw [if_neg positive, prefixInvariant_incoming_helper invariant, zero]
        rfl

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
