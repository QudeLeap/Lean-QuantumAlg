/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.Modular.Word.Accumulate

/-!
# Independent reversible permutations for modular word arithmetic

The finite pivot is an involution. Three such pivots give the total modular
offset, including identity on noncanonical labels [G17, paper.tex:266-274,319-334].
Selected offsets then give a word-prefix equivalence. Preserving the source
turns that family into a reversible two-word accumulation map, with no
coefficient inverse, parity condition, or reference to a circuit implementation.
-/

namespace QuantumAlg.Nat.FixedWidth

/-- Each fitted pivot is its own inverse on the complete finite word. -/
def pivotWordEquiv {width : Nat} (pivot : Fin (2 ^ width + 1)) :
    Equiv.Perm (Fin (2 ^ width)) where
  toFun := pivotWordOutput pivot
  invFun := pivotWordOutput pivot
  left_inv input := Fin.ext (pivotFlip_involutive pivot.val input.val)
  right_inv input := Fin.ext (pivotFlip_involutive pivot.val input.val)

/-- Three finite involutions define the total modular-offset permutation independently. -/
def modularWordEquiv {width : Nat} (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) : Equiv.Perm (Fin (2 ^ width)) :=
  ((pivotWordEquiv (offsetFirstPivot modulus constant)).trans (pivotWordEquiv modulus)).trans
    (pivotWordEquiv (offsetLastPivot modulus constant))

lemma modularWordEquiv_apply {width : Nat} (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) (input : Fin (2 ^ width)) :
    modularWordEquiv modulus constant input = modularWordOutput modulus constant input :=
  gidneyModularWord_three_pivots modulus constant input

/-- A fixed source bit chooses one actual mathematical permutation or the identity. -/
def selectedWordEquiv {width : Nat} (modulus : Fin (2 ^ width + 1)) (coefficient : Nat)
    (source : Fin (2 ^ width)) (index : Nat) : Equiv.Perm (Fin (2 ^ width)) :=
  if source.val.testBit index then
    modularWordEquiv modulus (accumulateConstant modulus coefficient index)
  else Equiv.refl _

lemma selectedWordEquiv_apply {width : Nat} (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) (source : Fin (2 ^ width)) (index : Nat) (target : Fin (2 ^ width)) :
    selectedWordEquiv modulus coefficient source index target =
      selectedWordOffset modulus coefficient source index target := by
  unfold selectedWordEquiv selectedWordOffset
  split_ifs
  · exact modularWordEquiv_apply modulus _ target
  · rfl

/-- The complete selected-prefix permutation retains the same increasing-bit order. -/
def accumulateWordEquiv {width : Nat} (modulus : Fin (2 ^ width + 1)) (coefficient : Nat)
    (source : Fin (2 ^ width)) : Nat → Equiv.Perm (Fin (2 ^ width))
  | 0 => Equiv.refl _
  | index + 1 => (accumulateWordEquiv modulus coefficient source index).trans
      (selectedWordEquiv modulus coefficient source index)

lemma accumulateWordEquiv_apply {width : Nat} (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) (source target : Fin (2 ^ width)) (count : Nat) :
    accumulateWordEquiv modulus coefficient source count target =
      accumulateWordPrefix modulus coefficient source target count := by
  induction count with
  | zero => rfl
  | succ index ih =>
      change selectedWordEquiv modulus coefficient source index
        (accumulateWordEquiv modulus coefficient source index target) = _
      exact (selectedWordEquiv_apply modulus coefficient source index _).trans
        (congrArg (selectedWordOffset modulus coefficient source index) ih)

/-- Preserving the source gives a reversible family without any coefficient-unit premise. -/
def accumulatePairEquiv {width : Nat} (modulus : Fin (2 ^ width + 1)) (coefficient count : Nat) :
    Equiv.Perm (Fin (2 ^ width) × Fin (2 ^ width)) where
  toFun state := (state.1, accumulateWordEquiv modulus coefficient state.1 count state.2)
  invFun state := (state.1, (accumulateWordEquiv modulus coefficient state.1 count).symm state.2)
  left_inv := by
    rintro ⟨source, target⟩
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨source, target⟩
    simp only [Equiv.apply_symm_apply]

lemma accumulatePairEquiv_apply {width : Nat} (modulus : Fin (2 ^ width + 1))
    (coefficient count : Nat) (state : Fin (2 ^ width) × Fin (2 ^ width)) :
    accumulatePairEquiv modulus coefficient count state =
      (state.1, accumulateWordPrefix modulus coefficient state.1 state.2 count) :=
  congrArg (fun target => (state.1, target))
    (accumulateWordEquiv_apply modulus coefficient state.1 state.2 count)

end QuantumAlg.Nat.FixedWidth
