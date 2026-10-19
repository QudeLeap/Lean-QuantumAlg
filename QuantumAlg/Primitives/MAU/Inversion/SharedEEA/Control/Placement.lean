/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.PreparedFrame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.RegisterFrame
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement

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

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit

/-- Exchange only the two retained Boolean fields when naming the same physical coordinates. -/
def exchange {width : Nat} (state : Registers width) : Registers width :=
  { state with
    flags := { state.flags with second := state.control }
    control := state.flags.second }

lemma exchange_exchange (width : Nat) (state : Registers width) :
    exchange (exchange state) = state := by
  cases state
  rfl

private def fieldEquiv (width : Nat) : Registers width ≃ Registers width where
  toFun := exchange
  invFun := exchange
  left_inv := exchange_exchange width
  right_inv := exchange_exchange width

private lemma separate (width : Nat) : (phase2Bit width).wire ≠ (controlBit width).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [phase2Bit_wire, controlBit_wire] at values
  omega

/-- The complete named-field exchange is exactly the actual two-wire swap's basis permutation. -/
private lemma swap_step (width : Nat) (state : Registers width) :
    swapStep (phase2Bit width) (controlBit width) (separate width) state = exchange state := by
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨p1, p2, sign, iter⟩, control⟩
  cases p2 <;> cases control <;> rfl

/-- Exact amplitude identification of the coordinate exchange with those two physical wires. -/
lemma exchange_coordinate_swap (width : Nat) :
    UnitaryCircuit.Realizes (encoding width)
      (swapProgram (QubitLayout.canonical _) .empty
        (phase2Bit width) (controlBit width) (separate width)) environment exchange :=
  (swap_realizes (QubitLayout.canonical _) .empty
    (phase2Bit width) (controlBit width) (separate width)).congrStep (swap_step width)

/-- Transport through the actual full binary encoding, preserving every unexchanged field. -/
def indexEquiv (width : Nat) :
    (Qubits (encoding width).width).Index ≃ (Qubits (encoding width).width).Index :=
  (PreparedFrame.registerLabelEquiv width).symm.trans
    ((fieldEquiv width).trans (PreparedFrame.registerLabelEquiv width))

lemma indexEquiv_encode (width : Nat) (state : Registers width) :
    indexEquiv width ((encoding width).encode state) =
      (encoding width).encode (exchange state) := by
  change PreparedFrame.registerLabelEquiv width
    (exchange ((PreparedFrame.registerLabelEquiv width).symm
      (PreparedFrame.registerLabelEquiv width state))) =
    PreparedFrame.registerLabelEquiv width (exchange state)
  rw [Equiv.symm_apply_apply]

/-- The two named original wires are exchanged by one exact physical bijection. -/
def wireEquiv (width : Nat) :
    Fin (encoding width).width ≃ Fin (encoding width).width :=
  Equiv.swap (phase2Bit width).wire (controlBit width).wire

/-- The actual full-frame placement derives its basis action from those same wires. -/
def placement (width : Nat) : EncodedBit.FullPlacement (encoding width) (encoding width) :=
  EncodedBit.FullPlacement.ofWires (encoding width) (encoding width)
    (encoding_surjective width) (encoding_surjective width) (wireEquiv width)

private lemma placed_read (width : Nat) (state : Registers width)
    (source target : EncodedBit (encoding width))
    (same : wireEquiv width source.wire = target.wire) :
    source.get ((placement width).grouping state) = target.get state :=
  EncodedBit.FullPlacement.ofWires_read (encoding width) (encoding width)
    (encoding_surjective width) (encoding_surjective width)
    (wireEquiv width) source target same state

private lemma fixed_read (width : Nat) (state : Registers width)
    (bit : EncodedBit (encoding width))
    (notPhase : bit.wire ≠ (phase2Bit width).wire)
    (notControl : bit.wire ≠ (controlBit width).wire) :
    bit.get ((placement width).grouping state) = bit.get state := by
  apply placed_read width state bit bit
  exact Equiv.swap_apply_of_ne_of_ne notPhase notControl

/-- Every unchanged field and both exchanged controls agree with the source grouping. -/
lemma placement_grouping (width : Nat) (state : Registers width) :
    (placement width).grouping state = exchange state := by
  apply Registers.ext_fields
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin (width + 3) := ⟨index, within⟩
    have actual := fixed_read width state (firstWordBit width selected)
      (by intro same; have values := congrArg Fin.val same
          rw [firstWordBit_wire, phase2Bit_wire] at values; omega)
      (by intro same; have values := congrArg Fin.val same
          rw [firstWordBit_wire, controlBit_wire] at values; omega)
    rw [firstWordBit_get, firstWordBit_get] at actual
    exact actual
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin (width + 3) := ⟨index, within⟩
    have actual := fixed_read width state (secondWordBit width selected)
      (by intro same; have values := congrArg Fin.val same
          rw [secondWordBit_wire, phase2Bit_wire] at values; omega)
      (by intro same; have values := congrArg Fin.val same
          rw [secondWordBit_wire, controlBit_wire] at values; omega)
    rw [secondWordBit_get, secondWordBit_get] at actual
    exact actual
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin width.size := ⟨index, within⟩
    have actual := fixed_read width state (coefficientLengthBit width selected)
      (by intro same; have values := congrArg Fin.val same
          rw [coefficientLengthBit_wire, phase2Bit_wire] at values; omega)
      (by intro same; have values := congrArg Fin.val same
          rw [coefficientLengthBit_wire, controlBit_wire] at values; omega)
    rw [coefficientLengthBit_get, coefficientLengthBit_get] at actual
    exact actual
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin width.size := ⟨index, within⟩
    have actual := fixed_read width state (quotientLengthBit width selected)
      (by intro same; have values := congrArg Fin.val same
          rw [quotientLengthBit_wire, phase2Bit_wire] at values; omega)
      (by intro same; have values := congrArg Fin.val same
          rw [quotientLengthBit_wire, controlBit_wire] at values; omega)
    rw [quotientLengthBit_get, quotientLengthBit_get] at actual
    exact actual
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin width.size := ⟨index, within⟩
    have actual := fixed_read width state (divisorLengthBit width selected)
      (by intro same; have values := congrArg Fin.val same
          rw [divisorLengthBit_wire, phase2Bit_wire] at values; omega)
      (by intro same; have values := congrArg Fin.val same
          rw [divisorLengthBit_wire, controlBit_wire] at values; omega)
    rw [divisorLengthBit_get, divisorLengthBit_get] at actual
    exact actual
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin width.size := ⟨index, within⟩
    have actual := fixed_read width state (shiftBit width selected)
      (by intro same; have values := congrArg Fin.val same
          rw [shiftBit_wire, phase2Bit_wire] at values; omega)
      (by intro same; have values := congrArg Fin.val same
          rw [shiftBit_wire, controlBit_wire] at values; omega)
    rw [shiftBit_get, shiftBit_get] at actual
    exact actual
  · have actual := fixed_read width state (phase1Bit width)
      (by intro same; have values := congrArg Fin.val same
          rw [phase1Bit_wire, phase2Bit_wire] at values; omega)
      (by intro same; have values := congrArg Fin.val same
          rw [phase1Bit_wire, controlBit_wire] at values; omega)
    rw [phase1Bit_get, phase1Bit_get] at actual
    exact actual
  · have actual := placed_read width state (phase2Bit width) (controlBit width)
      (by exact Equiv.swap_apply_left _ _)
    rw [phase2Bit_get, controlBit_get] at actual
    exact actual
  · have actual := fixed_read width state (signBit width)
      (by intro same; have values := congrArg Fin.val same
          rw [signBit_wire, phase2Bit_wire] at values; omega)
      (by intro same; have values := congrArg Fin.val same
          rw [signBit_wire, controlBit_wire] at values; omega)
    rw [signBit_get, signBit_get] at actual
    exact actual
  · have actual := fixed_read width state (iterationBit width)
      (by intro same; have values := congrArg Fin.val same
          rw [iterationBit_wire, phase2Bit_wire] at values; omega)
      (by intro same; have values := congrArg Fin.val same
          rw [iterationBit_wire, controlBit_wire] at values; omega)
    rw [iterationBit_get, iterationBit_get] at actual
    exact actual
  · have actual := placed_read width state (controlBit width) (phase2Bit width)
      (by exact Equiv.swap_apply_right _ _)
    rw [controlBit_get, phase2Bit_get] at actual
    exact actual

lemma placement_grouping_eq (width : Nat) :
    (placement width).grouping = fieldEquiv width := by
  apply Equiv.ext
  exact placement_grouping width

/-- Apply the actual native body at the exchanged original physical addresses. -/
def place (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (placement width).place body

/-- Conjugate the complete state action by the same explicit named-field exchange. -/
def placedStep {width : Nat} (action : Registers width → Registers width)
    (state : Registers width) : Registers width :=
  exchange (action (exchange state))

/-- The placed actual program realizes the full exchanged action with exact amplitudes. -/
lemma place_realizes (width : Nat)
    {body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum}
    {action : Registers width → Registers width}
    (realizes : UnitaryCircuit.Realizes (encoding width) body environment action) :
    UnitaryCircuit.Realizes (encoding width) (place width body) environment (placedStep action) :=
      by
  apply ((placement width).place_realizes realizes).congrStep
  intro state
  simp only [EncodedBit.FullPlacement.step, placement_grouping_eq, fieldEquiv,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, placedStep]

/-- Placement retains the original native event order and adds no swap events. -/
lemma place_eventTrace (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum) :
    (place width body).eventTrace = body.eventTrace := by
  exact (placement width).place_eventTrace body

end

end QuantumAlg.MAU.Inversion.SharedEEA.ControlPlacement
