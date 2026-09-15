/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.OneDirty.Resources
import Mathlib.Tactic.Ring

/-!
# Shared target and two arbitrary bits for pivot-flip arithmetic

The first bit is the comparison target and the last bit is the HRS borrowed
bit. Their values need no initialization. Temporarily including the first
bit as the target word's most significant bit allows an actual extended
addition to expose overflow [G17, paper.tex:380-389]. Packing changes only
parentheses in the basis label; it neither adds a wire nor applies a gate.
-/

namespace QuantumAlg.MAU.Addition.Gidney

noncomputable section

open BinaryLabelEncoding

/-- An arbitrary flag, the target word, and one arbitrary helper bit. -/
abbrev Registers (width : Nat) := Bool × (Fin (2 ^ width) × Bool)

/-- The exact declared bit order is flag, target word, helper. -/
def encoding (width : Nat) : BinaryLabelEncoding (Registers width) :=
  prod bool (HRS.oneDirtyEncoding width)

/-- The leading comparison target. -/
def flagBit (width : Nat) : EncodedBit (encoding width) :=
  prodLeftBit bool (HRS.oneDirtyEncoding width) boolBit

/-- A little-endian bit of the target word, after the leading flag. -/
def wordBit (width : Nat) (bit : Fin width) : EncodedBit (encoding width) :=
  prodRightBit bool (HRS.oneDirtyEncoding width) (HRS.oneDirtyWordBit width bit)

/-- The trailing bit lent to an HRS addition. -/
def helperBit (width : Nat) : EncodedBit (encoding width) :=
  prodRightBit bool (HRS.oneDirtyEncoding width) (HRS.oneDirtyBit width)

theorem gidneyFlagBit_get (width : Nat) (state : Registers width) :
    (flagBit width).get state = state.1 := rfl

theorem gidneyWordBit_get (width : Nat) (bit : Fin width) (state : Registers width) :
    (wordBit width bit).get state = state.2.1.val.testBit bit.val :=
  HRS.hrsOneDirtyWordBit_get width bit state.2

theorem gidneyHelperBit_get (width : Nat) (state : Registers width) :
    (helperBit width).get state = state.2.2 := rfl

/-- Include the flag as the extended word's high bit, retaining the same helper. -/
def packingEquiv (width : Nat) : Registers width ≃ HRS.OneDirtyRegisters (1 + width) :=
  (Equiv.prodAssoc Bool (Fin (2 ^ width)) Bool).symm.trans
    (Equiv.prodCongr
      ((Equiv.prodCongr finTwoEquiv.symm (Equiv.refl (Fin (2 ^ width)))).trans
        (prodEquiv (m := 1) (n := width)))
      (Equiv.refl Bool))

theorem gidneyPackingEquiv_apply (width : Nat) (state : Registers width) :
    packingEquiv width state =
      (prodEquiv (m := 1) (n := width) (bool.encode state.1, state.2.1), state.2.2) := by
  rcases state with ⟨flag, input, helper⟩
  cases flag <;> rfl

/-- Reassociate the same carrier without permuting any basis or physical bit. -/
def packingIndex (width : Nat) :
    Fin (2 ^ ((1 + width) + 1)) ≃ Fin (2 ^ (1 + (width + 1))) :=
  finCongr (congrArg (fun size : Nat => 2 ^ size) (Nat.add_assoc 1 width 1))

/-- The extended HRS label is exactly the original flag/word/helper label. -/
theorem gidneyPackingIndex_encode (width : Nat) (state : Registers width) :
    packingIndex width
        ((HRS.oneDirtyEncoding (1 + width)).encode (packingEquiv width state)) =
      (encoding width).encode state := by
  rw [gidneyPackingEquiv_apply]
  apply Fin.ext
  change (bool.encode state.2.2).val +
      2 ^ 1 * (state.2.1.val + 2 ^ width * (bool.encode state.1).val) =
    ((bool.encode state.2.2).val + 2 ^ 1 * state.2.1.val) +
      2 ^ (width + 1) * (bool.encode state.1).val
  simp only [pow_add, pow_one]
  ring

/-- Actual HRS offset on the temporary extended word, with the helper restored. -/
def packedOffsetProgram (width : Nat) (constant : Fin (2 ^ (1 + width))) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  UnitaryCircuit.reindex (packingIndex width) (HRS.oneDirtyProgram (1 + width) constant)

/-- Independent word action transported through the exact field packing. -/
def packedOffsetOutput {width : Nat} (constant : Fin (2 ^ (1 + width)))
    (state : Registers width) : Registers width :=
  (packingEquiv width).symm (HRS.oneDirtyOutput constant (packingEquiv width state))

/-- The placed actual addition has exactly its packed finite-word action. -/
theorem gidneyPackedOffset_realizes (width : Nat) (constant : Fin (2 ^ (1 + width))) :
    UnitaryCircuit.Realizes (encoding width) (packedOffsetProgram width constant)
      (packedOffsetOutput constant) where
  apply_encoded_ket := by
    intro state
    have hrun := (HRS.hrsOneDirty_realizes (1 + width) constant).apply_encoded_ket
      (packingEquiv width state)
    have hplaced := UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
      (R := Qubits ((1 + width) + 1)) (S := Qubits (1 + (width + 1)))
      (packingIndex width) (HRS.oneDirtyProgram (1 + width) constant) _ _ hrun
    have houtput : HRS.oneDirtyOutput constant (packingEquiv width state) =
        packingEquiv width (packedOffsetOutput constant state) :=
      ((packingEquiv width).apply_symm_apply _).symm
    rw [houtput, gidneyPackingIndex_encode, gidneyPackingIndex_encode] at hplaced
    exact hplaced

/-- The complete footprint is exactly the original word and the two declared bits. -/
theorem gidneyPackedOffset_physical (width : Nat) (constant : Fin (2 ^ (1 + width))) :
    (packedOffsetProgram width constant).physical_idx = List.range (width + 2) := by
  change (HRS.oneDirtyProgram (1 + width) constant).physical_idx = _
  rw [HRS.hrsOneDirty_physical]
  congr 1
  omega

/-- Packing retains the same actual native events and scheduled depth. -/
theorem gidneyPackedOffset_resources (width : Nat) (constant : Fin (2 ^ (1 + width)))
    (assign : Resource.Event .quantum → Nat) :
    (packedOffsetProgram width constant).eventCost =
        (HRS.oneDirtyProgram (1 + width) constant).eventCost ∧
      (packedOffsetProgram width constant).evaluatedEventDepth assign =
        (HRS.oneDirtyProgram (1 + width) constant).evaluatedEventDepth assign := by
  constructor <;> rfl

end

end QuantumAlg.MAU.Addition.Gidney
