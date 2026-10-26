/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Dirty.Control

/-!
# Native streaming callbacks with restored dirty work

The moving flag controls the original ordered payload. A final actual CNOT
toggles that flag from the current leaf prefix. Dirty work is restored by
every lowered gate, including all four Toffolis of a controlled Toffoli.
Neither that work nor the payload requires a computational-basis input.
-/

namespace QuantumAlg.EncodedBit.StreamedSelector

noncomputable section

open GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- A source word and two distinct existing positions used for its native control. -/
structure ControlledPayload (encoding : BinaryLabelEncoding Data) where
  active : EncodedBit encoding
  work : EncodedBit encoding
  source : List (GateSpec encoding)
  activeDisjoint : ∀ gate, gate ∈ source → bitDisjoint active gate
  workDisjoint : ∀ gate, gate ∈ source → bitDisjoint work gate
  activeWork : active.wire ≠ work.wire

namespace ControlledPayload

/-- All native instructions are emitted on the unchanged physical carrier. -/
def gates (payload : ControlledPayload encoding) : List (GateSpec encoding) :=
  listWithDirtyControl payload.active payload.work payload.source
    payload.activeDisjoint payload.workDisjoint payload.activeWork

/-- The source word keeps its order on the active branch and is absent on the other branch. -/
def step (payload : ControlledPayload encoding) (state : Data) : Data :=
  if payload.active.get state then GateSpec.stepList payload.source state else state

/-- Dirty restoration is exact on the whole encoded label. -/
lemma gates_step (payload : ControlledPayload encoding) (state : Data) :
    GateSpec.stepList payload.gates state = payload.step state :=
  listWithDirtyControl_step payload.active payload.work payload.source
    payload.activeDisjoint payload.workDisjoint payload.activeWork state

/-- The prefix toggle follows the controlled source gates. -/
def callbackGates (payload : ControlledPayload encoding) (leafBit : EncodedBit encoding)
    (separate : leafBit.wire ≠ payload.active.wire) : List (GateSpec encoding) :=
  payload.gates ++ [.cnot leafBit payload.active separate]

/-- The explicit selection bit is consumed only after the current payload action. -/
def callbackStep (payload : ControlledPayload encoding) (selected : Bool)
    (state : Data) : Data :=
  if selected then payload.active.flip (payload.step state) else payload.step state

/-- A real callback reads the original prefix, after exact dirty-work restoration. -/
lemma callbackGates_step (payload : ControlledPayload encoding) (leafBit : EncodedBit encoding)
    (separate : leafBit.wire ≠ payload.active.wire)
    (prefixDisjoint : ∀ gate, gate ∈ payload.source → bitDisjoint leafBit gate)
    (state : Data) :
    GateSpec.stepList (payload.callbackGates leafBit separate) state =
      payload.callbackStep (leafBit.get state) state := by
  have kept : leafBit.get (payload.step state) = leafBit.get state := by
    unfold step
    split
    · exact stepList_get_of_bitDisjoint payload.source leafBit prefixDisjoint state
    · rfl
  rw [callbackGates, stepList_append, gates_step]
  change (if leafBit.get (payload.step state) then
    payload.active.flip (payload.step state) else payload.step state) = _
  rw [kept]
  rfl

/-- Exact native semantics retain arbitrary superpositions and all surrounding correlations. -/
lemma callback_realizes (payload : ControlledPayload encoding) (leafBit : EncodedBit encoding)
    (separate : leafBit.wire ≠ payload.active.wire)
    (prefixDisjoint : ∀ gate, gate ∈ payload.source → bitDisjoint leafBit gate)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding
      (programList physical oracles (payload.callbackGates leafBit separate)) environment
      (fun state => payload.callbackStep (leafBit.get state) state) :=
  realizesList_congrStep physical oracles _
    (payload.callbackGates_step leafBit separate prefixDisjoint) environment

/-- Coherent lifting emits no physical X, and the boundary adds exactly one CNOT. -/
lemma callback_counts (payload : ControlledPayload encoding) (leafBit : EncodedBit encoding)
    (separate : leafBit.wire ≠ payload.active.wire) :
    ((payload.callbackGates leafBit separate).map xMultiplicity).sum = 0 ∧
      ((payload.callbackGates leafBit separate).map cnotMultiplicity).sum =
        (payload.source.map xMultiplicity).sum + 1 ∧
      ((payload.callbackGates leafBit separate).map toffoliMultiplicity).sum =
        (payload.source.map cnotMultiplicity).sum +
          4 * (payload.source.map toffoliMultiplicity).sum := by
  simp only [callbackGates, gates, List.map_append, List.sum_append,
    listWithDirtyControl_xMultiplicity_sum, listWithDirtyControl_cnotMultiplicity_sum,
    listWithDirtyControl_toffoliMultiplicity_sum, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, xMultiplicity, cnotMultiplicity, toffoliMultiplicity,
    Nat.add_zero, and_self]

end ControlledPayload

end

end QuantumAlg.EncodedBit.StreamedSelector
