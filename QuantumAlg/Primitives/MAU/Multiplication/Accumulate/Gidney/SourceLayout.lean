/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.CanonicalStage
import all QuantumAlg.Util.FinPow.WirePermutation

/-!
# Borrow two existing source bits for a selected modular offset

The canonical stage orders its fields as selector, unused source coordinates,
flag, target, helper. Packing moves the helper before the target to form the
complete source word. A finite source-wire swap then places the selector at
the requested source coordinate. The basis-label equivalence and physical
map describe those same two permutations of the original two words.
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate.Gidney

noncomputable section

open Nat.FixedWidth

abbrev Registers (width : Nat) := Fin (2 ^ width) × Fin (2 ^ width)

def encoding (width : Nat) : BinaryLabelEncoding (Registers width) :=
  BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity width)
    (BinaryLabelEncoding.finIdentity width)

/-- All source fields, separated only to expose the internally borrowed coordinates. -/
abbrev SourceParts (extra : Nat) := Bool × (Fin (2 ^ extra) × (Bool × Bool))

private def pairBoolEquiv : (Bool × Bool) ≃ Fin (2 ^ (1 + 1)) :=
  (Equiv.prodCongr finTwoEquiv.symm finTwoEquiv.symm).trans (prodEquiv (m := 1) (n := 1))

/-- Join the selector, untouched source coordinates, flag, and helper in physical order. -/
def sourceLabelEquiv (extra : Nat) : SourceParts extra ≃ Fin (2 ^ (extra + 3)) :=
  ((Equiv.prodCongr finTwoEquiv.symm
    ((Equiv.prodCongr (Equiv.refl _) pairBoolEquiv).trans
      (prodEquiv (m := extra) (n := 1 + 1)))).trans
        (prodEquiv (m := 1) (n := extra + (1 + 1)))).trans
          (finCongr (congrArg (fun width : Nat => 2 ^ width) (by omega)))

/-- The leading source bit before the selector permutation is exactly the selector value. -/
theorem gidneySourceLabel_selector (extra : Nat) (state : SourceParts extra) :
    (sourceLabelEquiv extra state).val.testBit (extra + 2) = state.1 := by
  rcases state with ⟨selected, unused, flag, helper⟩
  change (prodEquiv (m := 1) (n := extra + (1 + 1))
    (finTwoEquiv.symm selected,
      prodEquiv (unused, pairBoolEquiv (flag, helper)))).val.testBit (extra + 2) = selected
  have h := prodEquiv_testBit_left (m := 1) (n := extra + (1 + 1))
    (finTwoEquiv.symm selected) (prodEquiv (unused, pairBoolEquiv (flag, helper)))
    (0 : Fin 1)
  change (prodEquiv (m := 1) (n := extra + (1 + 1))
    (finTwoEquiv.symm selected,
      prodEquiv (unused, pairBoolEquiv (flag, helper)))).val.testBit (extra + 2) =
    (finTwoEquiv.symm selected).val.testBit 0 at h
  exact h.trans (by cases selected <;> rfl)

/-- Separate the target from the complete source fields without changing any value. -/
def canonicalFieldsEquiv (extra : Nat) :
    CanonicalRegisters extra ≃ (SourceParts extra × Fin (2 ^ (extra + 3))) where
  toFun state := ((state.1, (state.2.1, (state.2.2.1, state.2.2.2.2))), state.2.2.2.1)
  invFun state := (state.1.1, (state.1.2.1, (state.1.2.2.1, (state.2, state.1.2.2.2))))
  left_inv := by rintro ⟨selected, unused, flag, target, helper⟩; rfl
  right_inv := by rintro ⟨⟨selected, unused, flag, helper⟩, target⟩; rfl

/-- The canonical register encoding is itself a full binary-label equivalence. -/
def canonicalLabelEquiv (extra : Nat) :
    CanonicalRegisters extra ≃ Fin (2 ^ (canonicalEncoding extra).width) :=
  (Equiv.prodCongr finTwoEquiv.symm
    ((Equiv.prodCongr (Equiv.refl _)
      ((Equiv.prodCongr finTwoEquiv.symm
        ((Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans
          (prodEquiv (m := extra + 3) (n := 1)))).trans
            (prodEquiv (m := 1) (n := (extra + 3) + 1)))).trans
              (prodEquiv (m := extra) (n := 1 + ((extra + 3) + 1))))).trans
                (prodEquiv (m := 1) (n := extra + (1 + ((extra + 3) + 1))))

theorem gidneyCanonicalLabel_encode (extra : Nat) (state : CanonicalRegisters extra) :
    canonicalLabelEquiv extra state = (canonicalEncoding extra).encode state := by
  rcases state with ⟨selected, unused, flag, target, helper⟩
  cases selected <;> cases flag <;> cases helper <;> rfl

/-- Move the canonical leading selector to the selected little-endian source bit. -/
def selectorPermutation (extra : Nat) (selected : Fin (extra + 3)) :
    Equiv.Perm (Fin (extra + 3)) :=
  Equiv.swap (0 : Fin (extra + 3)) selected.rev

/-- Pack the source and target, applying only the compile-time source-wire permutation. -/
def selectedWordsEquiv (extra : Nat) (selected : Fin (extra + 3)) :
    CanonicalRegisters extra ≃ Registers (extra + 3) :=
  (canonicalFieldsEquiv extra).trans
    (Equiv.prodCongr ((sourceLabelEquiv extra).trans
      (BinaryBasis.permuteLabel (selectorPermutation extra selected))) (Equiv.refl _))

/-- The chosen standard-word readout is exactly the canonical selector. -/
theorem gidneySelectedWords_selector (extra : Nat) (selected : Fin (extra + 3))
    (state : CanonicalRegisters extra) :
    (selectedWordsEquiv extra selected state).1.val.testBit selected.val = state.1 := by
  have h := BinaryBasis.binaryPermuteLabel_bit (selectorPermutation extra selected)
    (sourceLabelEquiv extra (canonicalFieldsEquiv extra state).1) (0 : Fin (extra + 3))
  have hsource := gidneySourceLabel_selector extra (canonicalFieldsEquiv extra state).1
  have hzero : (0 : Fin (extra + 3)).rev.val = extra + 2 := by
    change (extra + 3) - (0 + 1) = extra + 2
    omega
  rw [hzero] at h
  have hselected : selectorPermutation extra selected (0 : Fin (extra + 3)) = selected.rev :=
    Equiv.swap_apply_left _ _
  rw [hselected, Fin.rev_rev] at h
  change (BinaryBasis.permuteLabel (selectorPermutation extra selected)
    (sourceLabelEquiv extra (canonicalFieldsEquiv extra state).1)).val.testBit selected.val =
      state.1
  exact h.trans hsource

/-- Exact reindexing of the same carrier to the standard source/target encoding. -/
def stagePlacementIndex (extra : Nat) (selected : Fin (extra + 3)) :
    Fin (2 ^ (canonicalEncoding extra).width) ≃ Fin (2 ^ (encoding (extra + 3)).width) :=
  (canonicalLabelEquiv extra).symm |>.trans (selectedWordsEquiv extra selected) |>.trans
    (prodEquiv (m := extra + 3) (n := extra + 3))

theorem gidneyStagePlacementIndex_encode (extra : Nat) (selected : Fin (extra + 3))
    (state : CanonicalRegisters extra) :
    stagePlacementIndex extra selected ((canonicalEncoding extra).encode state) =
      (encoding (extra + 3)).encode (selectedWordsEquiv extra selected state) := by
  rw [← gidneyCanonicalLabel_encode]
  exact congrArg (fun label => prodEquiv (m := extra + 3) (n := extra + 3)
    (selectedWordsEquiv extra selected label))
      ((canonicalLabelEquiv extra).symm_apply_apply state)

/-- Move the trailing helper into the final source position, shifting the target right by one. -/
def packHelperWire (extra wire : Nat) : Nat :=
  if wire < extra + 2 then wire
  else if wire < extra + 2 + (extra + 3) then wire + 1
  else if wire = extra + 2 + (extra + 3) then extra + 2 else wire

private def unpackHelperWire (extra wire : Nat) : Nat :=
  if wire < extra + 2 then wire
  else if wire = extra + 2 then extra + 2 + (extra + 3)
  else if wire < 2 * (extra + 3) then wire - 1 else wire

private theorem unpack_packHelperWire (extra wire : Nat) :
    unpackHelperWire extra (packHelperWire extra wire) = wire := by
  unfold unpackHelperWire packHelperWire
  split_ifs <;> omega

theorem gidneyPackHelperWire_injective (extra : Nat) :
    Function.Injective (packHelperWire extra) := by
  intro first second h
  have h' := congrArg (unpackHelperWire extra) h
  simpa only [unpack_packHelperWire] using h'

/-- Compose the same helper-packing and source-selector permutations on physical identifiers. -/
def stagePlacementWire (extra : Nat) (selected : Fin (extra + 3)) (wire : Nat) : Nat :=
  BinaryBasis.extendWirePermutation (selectorPermutation extra selected) (packHelperWire extra wire)

theorem gidneyStagePlacementWire_injective (extra : Nat) (selected : Fin (extra + 3)) :
    Function.Injective (stagePlacementWire extra selected) :=
  (BinaryBasis.binaryExtendWirePermutation_injective
    (selectorPermutation extra selected)).comp (gidneyPackHelperWire_injective extra)

theorem gidneyStagePlacementWire_range (extra : Nat) (selected : Fin (extra + 3))
    (wire : Nat) (inside : wire < 2 * (extra + 3)) :
    stagePlacementWire extra selected wire < 2 * (extra + 3) := by
  have hpacked : packHelperWire extra wire < 2 * (extra + 3) := by
    unfold packHelperWire
    split_ifs <;> omega
  unfold stagePlacementWire
  by_cases hsource : packHelperWire extra wire < extra + 3
  · have h := BinaryBasis.binaryExtendWirePermutation_range
      (selectorPermutation extra selected) _ hsource
    omega
  · rw [BinaryBasis.binaryExtendWirePermutation_outside _ _ (by omega)]
    exact hpacked

end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney
