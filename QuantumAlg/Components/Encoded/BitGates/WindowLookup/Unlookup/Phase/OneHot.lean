/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Phase.Complete
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.OneHot.Observation

/-!
# Original measured character on the explicitly reused unary subspace

The exact physical phase remains valid on arbitrary dirty target values.
An explicit onehot promise specializes it to the selected original table
column's dot product with the actual original measurement mask. Preparation
preserves every existing high-address and high-prefix readout.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {resultWidth lowWidth highRemaining : Nat}
  (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)

/-- Actual unary preparation preserves every supplied high-address readout. -/
lemma lowStep_highAddress (index : Fin highRemaining) (state : Data) :
    (frame.high.address index).get (frame.low.step state) =
      (frame.high.address index).get state := by
  apply frame.low.step_observed
  intro target
  rw [frame.lowResultWire]
  exact Ne.symm (frame.highAddressResult index (frame.lowResult target))

/-- Actual unary preparation preserves every supplied high stack position, including the top bit. -/
lemma lowStep_highStack (index : Fin (highRemaining + 1)) (state : Data) :
    (frame.high.stack index).get (frame.low.step state) = (frame.high.stack index).get state :=
  frame.low.step_observed _ (fun target => Ne.symm (frame.highStack_lowWord index target)) state

/-- The original full high-address label survives every actual unary preparation stage. -/
lemma lowStep_highLabel (state : Data) :
    frame.high.addressLabelAt highRemaining 0 (by omega) 0 (by omega) (frame.low.step state) =
      frame.high.addressLabelAt highRemaining 0 (by omega) 0 (by omega) state :=
  frame.high.addressLabelAt_congr _ _ (fun index => frame.lowStep_highAddress index state) _ _ _ _ _

/-- Preparing the reused unary result slice preserves
the explicitly supplied clean high prefixes. -/
lemma lowStep_clean (state : Data) (clean : frame.high.CleanFrom 0 state) :
    frame.high.CleanFrom 0 (frame.low.step state) := by
  intro index later
  rw [frame.lowStep_highStack]
  exact clean index later

/-- A promised unary word selects exactly the original table column's measured-mask parity. -/
lemma rowPhase_oneHot
    (table : Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))
    (high : Fin (2 ^ highRemaining)) (low : Fin (2 ^ lowWidth))
    (value : CShape.Value (.bits resultWidth)) (state : Data)
    (oneHot : frame.low.OneHot low state) :
    frame.rowPhase table high value state =
      if MaskParity.maskValue value (table high low) then (-1 : ℂ) else 1 := by
  unfold rowPhase
  rw [wordMaskParity_oneHot frame.lowWord _ low state oneHot, MaskParity.rowConstant_testBit]

/-- The actual complete paid phase cancels the selected column's original measured character. -/
lemma phaseOperator_oneHot_applyVec (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits resultWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))
    (separate : ∀ index, (parity index).key ∉ measured.storageKeys)
    (environment : OracleModel.Interpretation .empty) (store : Store ctx) (state : Data)
    (low : Fin (2 ^ lowWidth)) (oneHot : frame.low.OneHot low state)
    (clean : frame.high.CleanFrom 0 state) :
    (frame.phaseOperator (services := services)
      physical sameWires measured parity table environment store).applyVec
        (SelectorFrame.ctxVector physical sameWires state) =
      (if MaskParity.maskValue (store.read measured)
        (table ((frame.high.stack ⟨0, by omega⟩).get state)
          (frame.high.addressLabelAt highRemaining 0 (by omega) 0 (by omega) state) low)
        then (-1 : ℂ) else 1) • SelectorFrame.ctxVector physical sameWires state := by
  rw [frame.phaseOperator_applyVec physical sameWires measured parity table separate
    environment store state clean, frame.rowPhase_oneHot _ _ low _ state oneHot]

end

end QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame
