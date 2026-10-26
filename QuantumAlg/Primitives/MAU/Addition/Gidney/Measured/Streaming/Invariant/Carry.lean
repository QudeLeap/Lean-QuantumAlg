/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Invariant
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Ports

/-!
# Original arithmetic carry in the next actual streaming helper

The two-helper invariant identifies the incoming carry and the zero outgoing
helper. The exact actual native/reset row then implements the same original
finite-word carry recurrence [G25, main.tex:209-251].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {layout : Layout encoding width} {constant : BitVec width} {initial current : Data}

/-- The currently addressed helper contains the original target/offset incoming carry. -/
lemma prefixInvariant_incoming_helper {count : Nat}
    (invariant : layout.PrefixInvariant constant initial current count) :
    (layout.carryHelper count).get current = layout.carryInto constant initial count := by
  rw [carryHelper, invariant.clean, if_pos rfl]

/-- The next untouched source bit still has only the original selected offset xor. -/
lemma prefixInvariant_source (index : Fin (width - 1))
    (invariant : layout.PrefixInvariant constant initial current index.val) :
    (layout.target ⟨index.val, by omega⟩).get current =
      ((layout.target ⟨index.val, by omega⟩).get initial ^^
        (constant.getLsbD index.val && layout.control.get initial)) := by
  rw [invariant.target, if_neg (Nat.lt_irrefl index.val), Bool.xor_false]

/-- Before the final high-target row, the next actual helper starts at physical zero. -/
lemma prefixInvariant_next_zero (wide : 2 ≤ width) (index : Fin (width - 1))
    (nonfinal : index.val + 1 < width - 1)
    (invariant : layout.PrefixInvariant constant initial current index.val) :
    (layout.nextCarry wide index).get current = false := by
  have different : (index.val + 1) % 2 ≠ index.val % 2 := by omega
  rw [nextCarry, if_pos nonfinal, carryHelper, invariant.clean, if_neg different]

/-- The complete actual nonfinal row computes the next original arithmetic carry. -/
lemma prefixInvariant_next_carry (wide : 2 ≤ width) (index : Fin (width - 1))
    (nonfinal : index.val + 1 < width - 1)
    (invariant : layout.PrefixInvariant constant initial current index.val) :
    (layout.nextCarry wide index).get
        (wordLabel (layout.streamingStep wide constant index) current) =
      layout.carryInto constant initial (index.val + 1) := by
  rw [streamingStep_outgoing, prefixInvariant_next_zero wide index nonfinal invariant,
    prefixInvariant_source index invariant, invariant.control,
    prefixInvariant_incoming_helper invariant, Bool.false_xor]
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
  rw [firstChoice, carry_eq_affine_toffoli]
  exact (carryInto_succ layout constant initial index.val (by omega)).symm

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
