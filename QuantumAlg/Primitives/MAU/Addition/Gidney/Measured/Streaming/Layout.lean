/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Layout

/-!
# Alternating clean carries and the original most significant target bit

Carry one occupies clean bit one, carry two clean bit zero, and subsequent
carries alternate after the preceding physical reset. The final carry xors
directly into the original target's most significant bit. No extra output or
carry wire is introduced [G25, main.tex:239-251].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Alternating physical helper for a positive carry index. -/
def carryHelper (layout : Layout encoding width) (index : Nat) : EncodedBit encoding :=
  layout.clean ⟨index % 2, Nat.mod_lt _ (by decide)⟩

/-- The next carry uses an existing helper until the final xor into the target high bit. -/
def nextCarry (layout : Layout encoding width) (wide : 2 ≤ width)
    (index : Fin (width - 1)) : EncodedBit encoding :=
  if index.val + 1 < width - 1 then layout.carryHelper (index.val + 1)
  else layout.target ⟨width - 1, by omega⟩

lemma control_nextCarry_ne (layout : Layout encoding width) (wide : 2 ≤ width)
    (index : Fin (width - 1)) :
    layout.control.wire ≠ (layout.nextCarry wide index).wire := by
  unfold nextCarry
  split_ifs
  · exact layout.control_clean_ne _
  · exact layout.control_target_ne _

lemma target_nextCarry_ne (layout : Layout encoding width) (wide : 2 ≤ width)
    (index : Fin (width - 1)) :
    (layout.target ⟨index.val, by omega⟩).wire ≠ (layout.nextCarry wide index).wire := by
  unfold nextCarry
  split_ifs
  · exact layout.target_clean_ne _ _
  · apply layout.target_target_ne
    intro equal
    have same := congrArg Fin.val equal
    change index.val = width - 1 at same
    have bounded := index.isLt
    omega

lemma carryHelper_nextCarry_ne (layout : Layout encoding width) (wide : 2 ≤ width)
    (index : Fin (width - 1)) :
    (layout.carryHelper index.val).wire ≠ (layout.nextCarry wide index).wire := by
  unfold nextCarry
  split_ifs
  · apply layout.clean_clean_ne
    intro equal
    have same := congrArg Fin.val equal
    change index.val % 2 = (index.val + 1) % 2 at same
    omega
  · exact (layout.target_clean_ne _ _).symm

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
