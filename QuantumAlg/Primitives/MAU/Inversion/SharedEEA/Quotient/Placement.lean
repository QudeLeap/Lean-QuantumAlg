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
# Exact low-shift to quotient-length native placement

Both retained finite fields have the same source width, while occupying
distinct actual blocks of wires [LYL+26, sec_EEA/sub_regshare.tex:22-26].
This owner exchanges their names through the complete binary encoding and
the corresponding explicit physical interval permutation. It lets the
existing low-shift incrementer execute on the actual quotient length used
by [LYL+26, sec_EEA/sub_opt.tex:52-59].

The transport changes placement, not the native event list. Both shared
words, the other lengths, and all controls keep their original identities.
Every finite label, including width zero and arbitrary borrowed contents,
is retained by the exact inverse. No swap gate, auxiliary register, or
input-dependent preparation is introduced by this coordinate change.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.QuotientPlacement

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

/-- Exchange only quotient length and the original low shift field. -/
def exchange {width : Nat} (state : Registers width) : Registers width :=
  { state with quotientLength := state.shift, shift := state.quotientLength }

lemma exchange_exchange (width : Nat) (state : Registers width) :
    exchange (exchange state) = state := by
  cases state
  rfl

private def fieldEquiv (width : Nat) : Registers width ≃ Registers width where
  toFun := exchange
  invFun := exchange
  left_inv := exchange_exchange width
  right_inv := exchange_exchange width

/-- Every field outside the two exchanged lengths is exactly retained. -/
lemma exchange_retained (width : Nat) (state : Registers width) :
    (exchange state).firstWord = state.firstWord ∧
      (exchange state).secondWord = state.secondWord ∧
      (exchange state).coefficientLength = state.coefficientLength ∧
      (exchange state).divisorLength = state.divisorLength ∧
      (exchange state).flags = state.flags ∧ (exchange state).control = state.control :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The quotient lens reads the corresponding actual shift bit through this exchange. -/
lemma exchange_quotient_bit (width : Nat) (index : Fin width.size) (state : Registers width) :
    (quotientLengthBit width index).get (exchange state) = (shiftBit width index).get state := rfl

/-- The shift lens reads the corresponding actual quotient bit through the same exchange. -/
lemma exchange_shift_bit (width : Nat) (index : Fin width.size) (state : Registers width) :
    (shiftBit width index).get (exchange state) = (quotientLengthBit width index).get state := rfl

/-- Transport the exact complete binary label, not merely its dimension. -/
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

/-- Exchange the actual two equal-width intervals and fix all remaining physical identities. -/
def physicalMap (width wire : Nat) : Nat :=
  if 2 * (width + 3) + width.size ≤ wire ∧ wire < 2 * (width + 3) + 2 * width.size
  then wire + 2 * width.size
  else if 2 * (width + 3) + 3 * width.size ≤ wire ∧ wire < 2 * (width + 3) + 4 * width.size
  then wire - 2 * width.size else wire

/-- The same actual interval map is its inverse, including empty length blocks. -/
lemma physicalMap_twice (width wire : Nat) :
    physicalMap width (physicalMap width wire) = wire := by
  unfold physicalMap
  split_ifs <;> omega

/-- Certified bijective placement on the complete set of native physical identities. -/
def physicalEquiv (width : Nat) : Equiv.Perm Nat where
  toFun := physicalMap width
  invFun := physicalMap width
  left_inv := physicalMap_twice width
  right_inv := physicalMap_twice width

lemma physical_quotient (width : Nat) (index : Fin width.size) :
    physicalEquiv width (quotientLengthBit width index).wire.val =
      (shiftBit width index).wire.val := by
  rw [quotientLengthBit_wire, shiftBit_wire]
  change physicalMap width (2 * (width + 3) + width.size + index.val) = _
  have within := index.isLt
  unfold physicalMap
  split_ifs <;> omega

lemma physical_shift (width : Nat) (index : Fin width.size) :
    physicalEquiv width (shiftBit width index).wire.val =
      (quotientLengthBit width index).wire.val := by
  rw [shiftBit_wire, quotientLengthBit_wire]
  change physicalMap width (2 * (width + 3) + 3 * width.size + index.val) = _
  have within := index.isLt
  unfold physicalMap
  split_ifs <;> omega

/-- Every actual wire outside both exchanged intervals keeps its original identity. -/
lemma physical_fixed (width wire : Nat)
    (outsideQuotient : ¬(2 * (width + 3) + width.size ≤ wire ∧
      wire < 2 * (width + 3) + 2 * width.size))
    (outsideShift : ¬(2 * (width + 3) + 3 * width.size ≤ wire ∧
      wire < 2 * (width + 3) + 4 * width.size)) :
    physicalEquiv width wire = wire := by
  change physicalMap width wire = wire
  simp only [physicalMap, if_neg outsideQuotient, if_neg outsideShift]

/-- The entire original dirty Work1 keeps its physical positions. -/
lemma physical_firstWord (width : Nat) (index : Fin (width + 3)) :
    physicalEquiv width (firstWordBit width index).wire.val =
      (firstWordBit width index).wire.val := by
  apply physical_fixed <;> rw [firstWordBit_wire]
  all_goals
    have within := index.isLt
    omega

/-- Work2 also keeps all of its original physical positions. -/
lemma physical_secondWord (width : Nat) (index : Fin (width + 3)) :
    physicalEquiv width (secondWordBit width index).wire.val =
      (secondWordBit width index).wire.val := by
  apply physical_fixed <;> rw [secondWordBit_wire]
  all_goals
    have within := index.isLt
    omega

lemma physical_coefficientLength (width : Nat) (index : Fin width.size) :
    physicalEquiv width (coefficientLengthBit width index).wire.val =
      (coefficientLengthBit width index).wire.val := by
  apply physical_fixed <;> rw [coefficientLengthBit_wire]
  all_goals
    have within := index.isLt
    omega

lemma physical_divisorLength (width : Nat) (index : Fin width.size) :
    physicalEquiv width (divisorLengthBit width index).wire.val =
      (divisorLengthBit width index).wire.val := by
  apply physical_fixed <;> rw [divisorLengthBit_wire]
  all_goals
    have within := index.isLt
    omega

/-- All five original controls lie after both exchanged length blocks and are fixed. -/
lemma physical_control_region (width wire : Nat)
    (afterLengths : 2 * (width + 3) + 4 * width.size ≤ wire) :
    physicalEquiv width wire = wire := by
  apply physical_fixed <;> omega

/-- Placement never moves an original frame wire outside the original complete frame. -/
lemma physical_lt (width wire : Nat) (within : wire < (encoding width).width) :
    physicalEquiv width wire < (encoding width).width := by
  rw [encoding_width] at within ⊢
  change physicalMap width wire < _
  unfold physicalMap
  split_ifs <;> omega

/-- The interval exchange is a bijection on every physical bit of the original frame. -/
def wireEquiv (width : Nat) :
    Fin (encoding width).width ≃ Fin (encoding width).width where
  toFun index := ⟨physicalMap width index.val, physical_lt width index.val index.isLt⟩
  invFun index := ⟨physicalMap width index.val, physical_lt width index.val index.isLt⟩
  left_inv index := Fin.ext (physicalMap_twice width index.val)
  right_inv index := Fin.ext (physicalMap_twice width index.val)

/-- Complete semantic and physical placement derived from the same interval exchange. -/
def placement (width : Nat) :
    EncodedBit.FullPlacement (encoding width) (encoding width) :=
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
    (fixed : physicalEquiv width bit.wire.val = bit.wire.val) :
    bit.get ((placement width).grouping state) = bit.get state := by
  apply placed_read width state bit bit
  exact Fin.ext fixed

/-- The full wire-derived grouping exchanges exactly the quotient and shift fields. -/
lemma placement_grouping (width : Nat) (state : Registers width) :
    (placement width).grouping state = exchange state := by
  apply Registers.ext_fields
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin (width + 3) := ⟨index, within⟩
    have actual := fixed_read width state (firstWordBit width selected)
      (physical_firstWord width selected)
    rw [firstWordBit_get, firstWordBit_get] at actual
    exact actual
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin (width + 3) := ⟨index, within⟩
    have actual := fixed_read width state (secondWordBit width selected)
      (physical_secondWord width selected)
    rw [secondWordBit_get, secondWordBit_get] at actual
    exact actual
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin width.size := ⟨index, within⟩
    have actual := fixed_read width state (coefficientLengthBit width selected)
      (physical_coefficientLength width selected)
    rw [coefficientLengthBit_get, coefficientLengthBit_get] at actual
    exact actual
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin width.size := ⟨index, within⟩
    have same : wireEquiv width (quotientLengthBit width selected).wire =
        (shiftBit width selected).wire := Fin.ext (physical_quotient width selected)
    have actual := placed_read width state (quotientLengthBit width selected)
      (shiftBit width selected) same
    rw [quotientLengthBit_get, shiftBit_get] at actual
    exact actual
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin width.size := ⟨index, within⟩
    have actual := fixed_read width state (divisorLengthBit width selected)
      (physical_divisorLength width selected)
    rw [divisorLengthBit_get, divisorLengthBit_get] at actual
    exact actual
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    let selected : Fin width.size := ⟨index, within⟩
    have same : wireEquiv width (shiftBit width selected).wire =
        (quotientLengthBit width selected).wire := Fin.ext (physical_shift width selected)
    have actual := placed_read width state (shiftBit width selected)
      (quotientLengthBit width selected) same
    rw [shiftBit_get, quotientLengthBit_get] at actual
    exact actual
  · have actual := fixed_read width state (phase1Bit width)
      (physical_control_region width _ (by rw [phase1Bit_wire]; try omega))
    rw [phase1Bit_get, phase1Bit_get] at actual
    exact actual
  · have actual := fixed_read width state (phase2Bit width)
      (physical_control_region width _ (by rw [phase2Bit_wire]; try omega))
    rw [phase2Bit_get, phase2Bit_get] at actual
    exact actual
  · have actual := fixed_read width state (signBit width)
      (physical_control_region width _ (by rw [signBit_wire]; try omega))
    rw [signBit_get, signBit_get] at actual
    exact actual
  · have actual := fixed_read width state (iterationBit width)
      (physical_control_region width _ (by rw [iterationBit_wire]; try omega))
    rw [iterationBit_get, iterationBit_get] at actual
    exact actual
  · have actual := fixed_read width state (controlBit width)
      (physical_control_region width _ (by rw [controlBit_wire]; try omega))
    rw [controlBit_get, controlBit_get] at actual
    exact actual

lemma placement_grouping_eq (width : Nat) :
    (placement width).grouping = fieldEquiv width := by
  apply Equiv.ext
  exact placement_grouping width

/-- Place the supplied actual body at the exchanged original physical addresses. -/
def place (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (placement width).place body

/-- Exact conjugation of the complete original state action. -/
def placedStep {width : Nat} (action : Registers width → Registers width)
    (state : Registers width) : Registers width :=
  exchange (action (exchange state))

/-- Actual native action under the complete physical field placement. -/
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

/-- Placement preserves the exact ordered native event trace. -/
lemma place_eventTrace (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum) :
    (place width body).eventTrace = body.eventTrace :=
  (placement width).place_eventTrace body

end

end QuantumAlg.MAU.Inversion.SharedEEA.QuotientPlacement
