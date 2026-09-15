/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.PreparedFrame
import all QuantumAlg.Components.Encoded.BitGates.Realization

/-!
# Exact native control placement between Phase2 and the existing Ctrl

The source has distinct Phase2 and Ctrl wires
[LYL+26, sec_EEA/sub_regshare.tex:25-26]. This coordinate transport lets an
existing Phase2-controlled elementary program use the actual Ctrl wire.
Both its complete logical basis and its native physical addresses are
transported through the same exchange. Every event of the existing program
is retained, without declaring a new controlled-operation primitive.

The exchange is proved to be exactly the two-wire permutation represented
by the ordinary three-CNOT swap. That proof identifies the coordinates;
the placement does not execute that swap circuit. Subsequent predicate
computation and inverse cleanup must themselves be actual native programs.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ControlPlacement

noncomputable section

open EncodedBit

/-- Exchange only the two retained Boolean fields when naming the same physical coordinates. -/
def exchange {width : Nat} (state : Registers width) : Registers width :=
  { state with
    flags := { state.flags with second := state.control }
    control := state.flags.second }

theorem exchange_exchange (width : Nat) (state : Registers width) :
    exchange (exchange state) = state := by
  cases state
  rfl

private def fieldEquiv (width : Nat) : Registers width ≃ Registers width where
  toFun := exchange
  invFun := exchange
  left_inv := exchange_exchange width
  right_inv := exchange_exchange width

private theorem separate (width : Nat) : (phase2Bit width).wire ≠ (controlBit width).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [phase2Bit_wire, controlBit_wire] at values
  omega

/-- The complete named-field exchange is exactly the actual two-wire swap's basis permutation. -/
private theorem swap_step (width : Nat) (state : Registers width) :
    swapStep (phase2Bit width) (controlBit width) (separate width) state = exchange state := by
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨p1, p2, sign, iter⟩, control⟩
  cases p2 <;> cases control <;> rfl

/-- Exact amplitude identification of the coordinate exchange with those two physical wires. -/
theorem exchange_coordinate_swap (width : Nat) :
    UnitaryCircuit.Realizes (encoding width)
      (swapProgram (phase2Bit width) (controlBit width) (separate width)) exchange :=
  (swap_realizes (phase2Bit width) (controlBit width) (separate width)).congrStep (swap_step width)

/-- Transport through the actual full binary encoding, preserving every unexchanged field. -/
def indexEquiv (width : Nat) :
    (Qubits (encoding width).width).Index ≃ (Qubits (encoding width).width).Index :=
  (PreparedFrame.registerLabelEquiv width).symm.trans
    ((fieldEquiv width).trans (PreparedFrame.registerLabelEquiv width))

theorem indexEquiv_encode (width : Nat) (state : Registers width) :
    indexEquiv width ((encoding width).encode state) =
      (encoding width).encode (exchange state) := by
  change PreparedFrame.registerLabelEquiv width
    (exchange ((PreparedFrame.registerLabelEquiv width).symm
      (PreparedFrame.registerLabelEquiv width state))) =
    PreparedFrame.registerLabelEquiv width (exchange state)
  rw [Equiv.symm_apply_apply]

/-- The native wire map exchanges those same physical identities and leaves all others fixed. -/
def physicalEquiv (width : Nat) : Equiv.Perm Nat :=
  Equiv.swap (phase2Bit width).wire.val (controlBit width).wire.val

private def transported (width : Nat)
    (body : UnitaryCircuit (Qubits (encoding width).width)) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  UnitaryCircuit.reindex (indexEquiv width) body

/-- Apply the exact logical and native physical control-coordinate change to the existing body. -/
def place (width : Nat) (body : UnitaryCircuit (Qubits (encoding width).width)) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  UnitaryCircuit.relabel (transported width body)
    { toFun := physicalEquiv width
      map_layout := rfl
      old_nodup := (transported width body).physical_idx_nodup
      new_nodup := (transported width body).physical_idx_nodup.map
        (physicalEquiv width).injective }

/-- Conjugate the complete state action by the same explicit named-field exchange. -/
def placedStep {width : Nat} (action : Registers width → Registers width)
    (state : Registers width) : Registers width :=
  exchange (action (exchange state))

/-- The placed actual program realizes the full exchanged action with exact amplitudes. -/
theorem place_realizes (width : Nat)
    {body : UnitaryCircuit (Qubits (encoding width).width)}
    {action : Registers width → Registers width}
    (realizes : UnitaryCircuit.Realizes (encoding width) body action) :
    UnitaryCircuit.Realizes (encoding width) (place width body) (placedStep action) where
  apply_encoded_ket := by
    intro state
    have original := realizes.apply_encoded_ket (exchange state)
    have reindexed := UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
      (R := Qubits (encoding width).width) (S := Qubits (encoding width).width)
      (indexEquiv width) body _ _ original
    rw [indexEquiv_encode, indexEquiv_encode, exchange_exchange] at reindexed
    unfold place
    rw [UnitaryCircuit.Realizes.applyNormalized_relabel]
    exact reindexed

/-- Placement retains the original native event order and adds no swap events. -/
theorem place_eventTrace (width : Nat) (body : UnitaryCircuit (Qubits (encoding width).width)) :
    (place width body).eventTrace = body.eventTrace := by
  rw [place, UnitaryCircuit.relabel_eventTrace, transported, UnitaryCircuit.reindex_eventTrace]

/-- Every changed native identity is exactly the corresponding exchanged original address. -/
theorem place_physical (width : Nat) (body : UnitaryCircuit (Qubits (encoding width).width)) :
    (place width body).physical_idx = body.physical_idx.map (physicalEquiv width) := rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.ControlPlacement
