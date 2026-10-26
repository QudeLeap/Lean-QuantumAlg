/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.StreamedSelector.Callback
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.FrameLaws

/-! # Full physical frame protection for moving-flag callbacks -/

namespace QuantumAlg.EncodedBit.StreamedSelector.ControlledPayload

noncomputable section

open GateSpec WindowLookup

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- The controlled source word preserves every disjoint coordinate. -/
lemma step_get (payload : ControlledPayload encoding) (observed : EncodedBit encoding)
    (disjoint : ∀ gate, gate ∈ payload.source → bitDisjoint observed gate) (state : Data) :
    observed.get (payload.step state) = observed.get state := by
  unfold step
  split
  · exact stepList_get_of_bitDisjoint payload.source observed disjoint state
  · rfl

/-- Disjoint flips commute with both branches of the original controlled source word. -/
lemma step_flip (payload : ControlledPayload encoding) (observed : EncodedBit encoding)
    (separate : payload.active.wire ≠ observed.wire)
    (disjoint : ∀ gate, gate ∈ payload.source → bitDisjoint observed gate) (state : Data) :
    payload.step (observed.flip state) = observed.flip (payload.step state) := by
  unfold step
  rw [get_flip_of_wire_ne observed payload.active separate.symm]
  split
  · exact stepList_flip_comm_of_bitDisjoint payload.source observed disjoint state
  · rfl

/-- A boundary toggle leaves every other protected wire at its original value. -/
lemma callbackStep_get (payload : ControlledPayload encoding) (observed : EncodedBit encoding)
    (separate : payload.active.wire ≠ observed.wire)
    (disjoint : ∀ gate, gate ∈ payload.source → bitDisjoint observed gate)
    (selected : Bool) (state : Data) :
    observed.get (payload.callbackStep selected state) = observed.get state := by
  cases selected with
  | false => exact payload.step_get observed disjoint state
  | true =>
      change observed.get (payload.active.flip (payload.step state)) = _
      rw [get_flip_of_wire_ne _ _ separate, payload.step_get observed disjoint state]

/-- Explicit selection cannot inspect an unused selector prefix. -/
lemma callbackStep_flip (payload : ControlledPayload encoding) (observed : EncodedBit encoding)
    (separate : payload.active.wire ≠ observed.wire)
    (disjoint : ∀ gate, gate ∈ payload.source → bitDisjoint observed gate)
    (selected : Bool) (state : Data) :
    payload.callbackStep selected (observed.flip state) =
      observed.flip (payload.callbackStep selected state) := by
  cases selected with
  | false => exact payload.step_flip observed separate disjoint state
  | true =>
      change payload.active.flip (payload.step (observed.flip state)) =
        observed.flip (payload.active.flip (payload.step state))
      rw [payload.step_flip observed separate disjoint state, flip_comm]

/-- All address and stack systems remain protected for each Boolean leaf action. -/
lemma callbackStep_preserves {width : Nat} (payload : ControlledPayload encoding)
    (frame : SelectorFrame encoding width)
    (activeAddress : ∀ index, payload.active.wire ≠ (frame.address index).wire)
    (activeStack : ∀ index, payload.active.wire ≠ (frame.stack index).wire)
    (sourceAddress : ∀ index gate, gate ∈ payload.source → bitDisjoint (frame.address index) gate)
    (sourceStack : ∀ index gate, gate ∈ payload.source → bitDisjoint (frame.stack index) gate)
    (selected : Bool) : frame.Preserves (payload.callbackStep selected) := by
  constructor
  · intro index state
    exact payload.callbackStep_get _ (activeAddress index) (sourceAddress index) selected state
  · intro index state
    exact payload.callbackStep_get _ (activeStack index) (sourceStack index) selected state

/-- Full prefix independence permits the same actual unary fork syntax to be reused. -/
lemma callbackStep_independent {width : Nat} (payload : ControlledPayload encoding)
    (frame : SelectorFrame encoding width)
    (activePrefix : ∀ index : Fin width,
      payload.active.wire ≠ (frame.stack index.succ).wire)
    (sourcePrefix : ∀ (index : Fin width) gate, gate ∈ payload.source →
      bitDisjoint (frame.stack index.succ) gate)
    (selected : Bool) : frame.IndependentPrefixes (payload.callbackStep selected) := by
  intro index state
  exact payload.callbackStep_flip _ (activePrefix index) (sourcePrefix index) selected state

end

end QuantumAlg.EncodedBit.StreamedSelector.ControlledPayload
