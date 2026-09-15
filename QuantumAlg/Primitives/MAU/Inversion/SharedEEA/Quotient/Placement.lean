/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.PreparedFrame
import all QuantumAlg.Components.Encoded.BitGates.Realization

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

/-- Exchange only quotient length and the original low shift field. -/
def exchange {width : Nat} (state : Registers width) : Registers width :=
  { state with quotientLength := state.shift, shift := state.quotientLength }

theorem exchange_exchange (width : Nat) (state : Registers width) :
    exchange (exchange state) = state := by
  cases state
  rfl

private def fieldEquiv (width : Nat) : Registers width ≃ Registers width where
  toFun := exchange
  invFun := exchange
  left_inv := exchange_exchange width
  right_inv := exchange_exchange width

/-- Every field outside the two exchanged lengths is exactly retained. -/
theorem exchange_retained (width : Nat) (state : Registers width) :
    (exchange state).firstWord = state.firstWord ∧
      (exchange state).secondWord = state.secondWord ∧
      (exchange state).coefficientLength = state.coefficientLength ∧
      (exchange state).divisorLength = state.divisorLength ∧
      (exchange state).flags = state.flags ∧ (exchange state).control = state.control :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The quotient lens reads the corresponding actual shift bit through this exchange. -/
theorem exchange_quotient_bit (width : Nat) (index : Fin width.size) (state : Registers width) :
    (quotientLengthBit width index).get (exchange state) = (shiftBit width index).get state := rfl

/-- The shift lens reads the corresponding actual quotient bit through the same exchange. -/
theorem exchange_shift_bit (width : Nat) (index : Fin width.size) (state : Registers width) :
    (shiftBit width index).get (exchange state) = (quotientLengthBit width index).get state := rfl

/-- Transport the exact complete binary label, not merely its dimension. -/
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

/-- Exchange the actual two equal-width intervals and fix all remaining physical identities. -/
def physicalMap (width wire : Nat) : Nat :=
  if 2 * (width + 3) + width.size ≤ wire ∧ wire < 2 * (width + 3) + 2 * width.size
  then wire + 2 * width.size
  else if 2 * (width + 3) + 3 * width.size ≤ wire ∧ wire < 2 * (width + 3) + 4 * width.size
  then wire - 2 * width.size else wire

/-- The same actual interval map is its inverse, including empty length blocks. -/
theorem physicalMap_twice (width wire : Nat) :
    physicalMap width (physicalMap width wire) = wire := by
  unfold physicalMap
  split_ifs <;> omega

/-- Certified bijective placement on the complete set of native physical identities. -/
def physicalEquiv (width : Nat) : Equiv.Perm Nat where
  toFun := physicalMap width
  invFun := physicalMap width
  left_inv := physicalMap_twice width
  right_inv := physicalMap_twice width

theorem physical_quotient (width : Nat) (index : Fin width.size) :
    physicalEquiv width (quotientLengthBit width index).wire.val =
      (shiftBit width index).wire.val := by
  rw [quotientLengthBit_wire, shiftBit_wire]
  change physicalMap width (2 * (width + 3) + width.size + index.val) = _
  have within := index.isLt
  unfold physicalMap
  split_ifs <;> omega

theorem physical_shift (width : Nat) (index : Fin width.size) :
    physicalEquiv width (shiftBit width index).wire.val =
      (quotientLengthBit width index).wire.val := by
  rw [shiftBit_wire, quotientLengthBit_wire]
  change physicalMap width (2 * (width + 3) + 3 * width.size + index.val) = _
  have within := index.isLt
  unfold physicalMap
  split_ifs <;> omega

/-- Every actual wire outside both exchanged intervals keeps its original identity. -/
theorem physical_fixed (width wire : Nat)
    (outsideQuotient : ¬(2 * (width + 3) + width.size ≤ wire ∧
      wire < 2 * (width + 3) + 2 * width.size))
    (outsideShift : ¬(2 * (width + 3) + 3 * width.size ≤ wire ∧
      wire < 2 * (width + 3) + 4 * width.size)) :
    physicalEquiv width wire = wire := by
  change physicalMap width wire = wire
  simp only [physicalMap, if_neg outsideQuotient, if_neg outsideShift]

/-- The entire original dirty Work1 keeps its physical positions. -/
theorem physical_firstWord (width : Nat) (index : Fin (width + 3)) :
    physicalEquiv width (firstWordBit width index).wire.val =
      (firstWordBit width index).wire.val := by
  apply physical_fixed <;> rw [firstWordBit_wire]
  all_goals
    have within := index.isLt
    omega

/-- Work2 also keeps all of its original physical positions. -/
theorem physical_secondWord (width : Nat) (index : Fin (width + 3)) :
    physicalEquiv width (secondWordBit width index).wire.val =
      (secondWordBit width index).wire.val := by
  apply physical_fixed <;> rw [secondWordBit_wire]
  all_goals
    have within := index.isLt
    omega

theorem physical_coefficientLength (width : Nat) (index : Fin width.size) :
    physicalEquiv width (coefficientLengthBit width index).wire.val =
      (coefficientLengthBit width index).wire.val := by
  apply physical_fixed <;> rw [coefficientLengthBit_wire]
  all_goals
    have within := index.isLt
    omega

theorem physical_divisorLength (width : Nat) (index : Fin width.size) :
    physicalEquiv width (divisorLengthBit width index).wire.val =
      (divisorLengthBit width index).wire.val := by
  apply physical_fixed <;> rw [divisorLengthBit_wire]
  all_goals
    have within := index.isLt
    omega

/-- All five original controls lie after both exchanged length blocks and are fixed. -/
theorem physical_control_region (width wire : Nat)
    (afterLengths : 2 * (width + 3) + 4 * width.size ≤ wire) :
    physicalEquiv width wire = wire := by
  apply physical_fixed <;> omega

/-- Placement never moves an original frame wire outside the original complete frame. -/
theorem physical_lt (width wire : Nat) (within : wire < (encoding width).width) :
    physicalEquiv width wire < (encoding width).width := by
  rw [encoding_width] at within ⊢
  change physicalMap width wire < _
  unfold physicalMap
  split_ifs <;> omega

private def transported (width : Nat)
    (body : UnitaryCircuit (Qubits (encoding width).width)) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  UnitaryCircuit.reindex (indexEquiv width) body

/-- Place the existing program by the same exact logical and physical field exchange. -/
def place (width : Nat) (body : UnitaryCircuit (Qubits (encoding width).width)) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  UnitaryCircuit.relabel (transported width body)
    { toFun := physicalEquiv width
      map_layout := rfl
      old_nodup := (transported width body).physical_idx_nodup
      new_nodup := (transported width body).physical_idx_nodup.map
        (physicalEquiv width).injective }

/-- Exact conjugation of the complete original state action. -/
def placedStep {width : Nat} (action : Registers width → Registers width)
    (state : Registers width) : Registers width :=
  exchange (action (exchange state))

/-- Actual circuit action under the proved field placement, preserving complete amplitudes. -/
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

/-- The event order is retained exactly: placement adds no word-swap events. -/
theorem place_eventTrace (width : Nat) (body : UnitaryCircuit (Qubits (encoding width).width)) :
    (place width body).eventTrace = body.eventTrace := by
  rw [place, UnitaryCircuit.relabel_eventTrace, transported, UnitaryCircuit.reindex_eventTrace]

/-- Every native address is transformed by the same actual interval permutation. -/
theorem place_physical (width : Nat) (body : UnitaryCircuit (Qubits (encoding width).width)) :
    (place width body).physical_idx = body.physical_idx.map (physicalEquiv width) := rfl

/-- Programs originally placed within this frame remain within it after the field exchange. -/
theorem place_physical_idx_subset (width : Nat)
    (body : UnitaryCircuit (Qubits (encoding width).width))
    (inside : body.physical_idx ⊆ List.range (encoding width).width) :
    (place width body).physical_idx ⊆ List.range (encoding width).width := by
  rw [place_physical]
  intro wire present
  obtain ⟨old, oldPresent, rfl⟩ := List.mem_map.mp present
  exact List.mem_range.mpr (physical_lt width old (List.mem_range.mp (inside oldPresent)))

end

end QuantumAlg.MAU.Inversion.SharedEEA.QuotientPlacement
