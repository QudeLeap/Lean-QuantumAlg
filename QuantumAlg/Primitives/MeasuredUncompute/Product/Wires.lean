/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.SplitIfs

/-!
# Exact three-word ports in a retained shared arithmetic frame

The actual frame is Work1, Work2, the retained small fields, and Y.
Work1 consists of the n-bit accumulator A followed by three retained
bits. Work2 consists of three retained bits followed by the n-bit X.
The native variable product uses X, Y, A, and then these same retained
bits. The explicit inverse below retains every physical system and
does not execute a SWAP or allocate an additional arithmetic word
[LYL+26, sec_point_add/sec_point_add.tex:51-79].
-/

namespace QuantumAlg.MeasuredUncompute.ProductWires

/-- Every live bit in the three large words and the complete retained small frame. -/
def width (wordWidth tailWidth : Nat) : Nat := 3 * wordWidth + 6 + tailWidth

/-- Source product coordinates X/Y/A/history address their actual existing frame positions. -/
def address (wordWidth tailWidth index : Nat) : Nat :=
  if index < wordWidth then wordWidth + 6 + index
  else if index < 2 * wordWidth then wordWidth + 6 + tailWidth + index
  else if index < 3 * wordWidth + 6 then index - 2 * wordWidth
  else index - wordWidth

private def sourceAddress (wordWidth tailWidth index : Nat) : Nat :=
  if index < wordWidth + 6 then 2 * wordWidth + index
  else if index < 2 * wordWidth + 6 then index - (wordWidth + 6)
  else if index < 2 * wordWidth + 6 + tailWidth then index + wordWidth
  else index - (wordWidth + 6 + tailWidth)

private theorem address_bound (wordWidth tailWidth : Nat)
    (index : Fin (width wordWidth tailWidth)) :
    address wordWidth tailWidth index.val < width wordWidth tailWidth := by
  have bound := index.isLt
  unfold width at *
  unfold address
  split_ifs <;> omega

private theorem sourceAddress_bound (wordWidth tailWidth : Nat)
    (index : Fin (width wordWidth tailWidth)) :
    sourceAddress wordWidth tailWidth index.val < width wordWidth tailWidth := by
  have bound := index.isLt
  unfold width at *
  unfold sourceAddress
  split_ifs <;> omega

/-- The complete actual wire bijection, valid even when a large word or the tail has width zero. -/
def permutation (wordWidth tailWidth : Nat) : Equiv.Perm (Fin (width wordWidth tailWidth)) where
  toFun index := ⟨address wordWidth tailWidth index.val, address_bound wordWidth tailWidth index⟩
  invFun index :=
    ⟨sourceAddress wordWidth tailWidth index.val, sourceAddress_bound wordWidth tailWidth index⟩
  left_inv index := by
    apply Fin.ext
    have bound := index.isLt
    change sourceAddress wordWidth tailWidth (address wordWidth tailWidth index.val) = index.val
    unfold width at bound
    unfold address sourceAddress
    split_ifs <;> omega
  right_inv index := by
    apply Fin.ext
    have bound := index.isLt
    change address wordWidth tailWidth (sourceAddress wordWidth tailWidth index.val) = index.val
    unfold width at bound
    unfold sourceAddress address
    split_ifs <;> omega

/-- The first product input reads precisely the original trailing Work2 data port. -/
theorem address_first (wordWidth tailWidth : Nat) (index : Fin wordWidth) :
    address wordWidth tailWidth index.val = wordWidth + 6 + index.val :=
  if_pos index.isLt

/-- The second product input reads precisely the existing Y word after the shared frame. -/
theorem address_second (wordWidth tailWidth : Nat) (index : Fin wordWidth) :
    address wordWidth tailWidth (wordWidth + index.val) =
      2 * wordWidth + 6 + tailWidth + index.val := by
  have bound := index.isLt
  unfold address
  rw [if_neg (by omega), if_pos (by omega)]
  omega

/-- The accumulator uses the first n existing Work1 wires, leaving its three history bits intact. -/
theorem address_target (wordWidth tailWidth : Nat) (index : Fin wordWidth) :
    address wordWidth tailWidth (2 * wordWidth + index.val) = index.val := by
  have bound := index.isLt
  unfold address
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  omega

/-- The six retained padding bits keep their exact original positions between A and X. -/
theorem address_padding (wordWidth tailWidth : Nat) (index : Fin 6) :
    address wordWidth tailWidth (3 * wordWidth + index.val) = wordWidth + index.val := by
  have bound := index.isLt
  unfold address
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  omega

/-- Every small arithmetic field keeps its exact original position following Work2. -/
theorem address_tail (wordWidth tailWidth : Nat) (index : Fin tailWidth) :
    address wordWidth tailWidth (3 * wordWidth + 6 + index.val) =
      2 * wordWidth + 6 + index.val := by
  unfold address
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  omega

end QuantumAlg.MeasuredUncompute.ProductWires
