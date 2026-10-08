/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.OneDirty.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Width
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

/-- The extended HRS carrier and the public flag/word/helper carrier have the same width. -/
private theorem packingWidth (width : Nat) :
    (HRS.oneDirtyEncoding (1 + width)).width = (encoding width).width := by
  change (1 + width) + 1 = 1 + (width + 1)
  omega

/-- The extended HRS label is exactly the original flag/word/helper label. -/
theorem gidneyPackingIndex_encode (width : Nat) (state : Registers width) :
    UnitaryCircuit.castQubitWidthIndex (packingWidth width)
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
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  UnitaryCircuit.castCanonicalQubitWidth (packingWidth width)
    (HRS.oneDirtyProgram (1 + width) constant)

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
    let sourceInput := NormalizedVector.ket
      ((QubitLayout.canonical (HRS.oneDirtyEncoding (1 + width)).width).basisEquiv.symm
        ((HRS.oneDirtyEncoding (1 + width)).encode (packingEquiv width state)))
    let output := HRS.oneDirtyOutput constant (packingEquiv width state)
    let sourceOutput := NormalizedVector.ket
      ((QubitLayout.canonical (HRS.oneDirtyEncoding (1 + width)).width).basisEquiv.symm
        ((HRS.oneDirtyEncoding (1 + width)).encode output))
    have hrun := (HRS.hrsOneDirty_realizes (1 + width) constant).apply_encoded_ket
      (packingEquiv width state)
    have inputCast : packingWidth width ▸ sourceInput =
        NormalizedVector.ket
          ((QubitLayout.canonical (encoding width).width).basisEquiv.symm
            ((encoding width).encode state)) := by
      dsimp only [sourceInput]
      exact (UnitaryCircuit.castCanonicalQubitWidth_ket
        (packingWidth width)
        ((HRS.oneDirtyEncoding (1 + width)).encode (packingEquiv width state))).trans
          (congrArg (fun index => NormalizedVector.ket
            ((QubitLayout.canonical (encoding width).width).basisEquiv.symm index))
            (gidneyPackingIndex_encode width state))
    have outputCast : packingWidth width ▸ sourceOutput =
        NormalizedVector.ket
          ((QubitLayout.canonical (encoding width).width).basisEquiv.symm
            ((encoding width).encode (packedOffsetOutput constant state))) := by
      dsimp only [sourceOutput, output, packedOffsetOutput]
      exact (UnitaryCircuit.castCanonicalQubitWidth_ket
        (packingWidth width)
        ((HRS.oneDirtyEncoding (1 + width)).encode
          (HRS.oneDirtyOutput constant (packingEquiv width state)))).trans
          (congrArg (fun index => NormalizedVector.ket
            ((QubitLayout.canonical (encoding width).width).basisEquiv.symm index))
            (by
              simpa only [Equiv.apply_symm_apply] using
                gidneyPackingIndex_encode width
                  ((packingEquiv width).symm
                    (HRS.oneDirtyOutput constant (packingEquiv width state)))))
    calc
      _ = (packedOffsetProgram width constant).applyNormalized
          (packingWidth width ▸ sourceInput) :=
        congrArg (packedOffsetProgram width constant).applyNormalized inputCast.symm
      _ = packingWidth width ▸
          (HRS.oneDirtyProgram (1 + width) constant).applyNormalized sourceInput :=
        UnitaryCircuit.castCanonicalQubitWidth_applyNormalized
          (packingWidth width) (HRS.oneDirtyProgram (1 + width) constant) sourceInput
      _ = packingWidth width ▸ sourceOutput := by
        exact congrArg (fun value => packingWidth width ▸ value)
          (show (HRS.oneDirtyProgram (1 + width) constant).applyNormalized sourceInput =
              sourceOutput by simpa only [sourceInput, sourceOutput, output] using hrun)
      _ = _ := by
        simpa only [packedOffsetOutput] using outputCast

/-- The complete interface is exactly the original word and the two declared bits. -/
theorem gidneyPackedOffset_interface (width : Nat) (_constant : Fin (2 ^ (1 + width))) :
    (encoding width).width = width + 2 ∧
      (QubitLayout.canonical (encoding width).width).systemIdx =
        List.range (width + 2) := by
  have hwidth : (encoding width).width = width + 2 := by
    change 1 + (width + 1) = width + 2
    omega
  constructor
  · exact hwidth
  · rw [hwidth]
    exact QubitLayout.canonical_systemIdx (width + 2)

/-- Packing retains the same actual native events and scheduled depth. -/
theorem gidneyPackedOffset_resources (width : Nat) (constant : Fin (2 ^ (1 + width)))
    (assign : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    (packedOffsetProgram width constant).eventCost =
        (HRS.oneDirtyProgram (1 + width) constant).eventCost ∧
      (packedOffsetProgram width constant).evaluatedEventDepth assign =
        (HRS.oneDirtyProgram (1 + width) constant).evaluatedEventDepth assign := by
  exact ⟨UnitaryCircuit.castCanonicalQubitWidth_eventCost
      (packingWidth width) (HRS.oneDirtyProgram (1 + width) constant),
    UnitaryCircuit.castCanonicalQubitWidth_evaluatedEventDepth
      (packingWidth width) (HRS.oneDirtyProgram (1 + width) constant) assign⟩

end

end QuantumAlg.MAU.Addition.Gidney
