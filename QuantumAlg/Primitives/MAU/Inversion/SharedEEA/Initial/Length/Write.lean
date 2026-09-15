/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Initial.Length.Semantics
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor

/-!
# An actual native initialization circuit for the divisor length

Every possible leading position controls a fixed binary length label. These
controls are the actual leading-bit X/CNOT/Toffoli lists, and their dirty work
is restored before proceeding to the next position. The resulting literal
list reads the current Work2 payload and xors its ordinary binary length into
the existing divisor-length field [LYL+26, sec_EEA/sub_4phase.tex:108-117].

The length used in the correctness statement is computed from the state;
it is not a classical parameter used to select or initialize this circuit.
The gate list itself depends only on the register width. Arbitrary incoming
length values and Work1 values are allowed, enabling exact reversal later.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InitialLengthWrite

noncomputable section

open EncodedBit InitialLengthPredicate InitialLengthSemantics

/-- The existing divisor-length field in the least-significant-first word API. -/
def target (width : Nat) : Word (encoding width) width.size :=
  ⟨fun index => divisorLengthBit width index.rev⟩

private theorem target_get (width : Nat) (index : Fin width.size) (state : Registers width) :
    ((target width).bit index).get state = state.divisorLength.getLsbD index.val := by
  change (divisorLengthBit width index.rev).get state = _
  rw [divisorLengthBit_get]
  have reverse : width.size - 1 - index.rev.val = index.val := by
    rw [Fin.val_rev]
    have bound := index.isLt
    omega
  simp only [BitVec.getMsbD_eq_getLsbD, index.rev.isLt, decide_true, Bool.true_and, reverse]

private theorem target_distinct (width : Nat) (left right : Fin width.size)
    (different : left ≠ right) :
    ((target width).bit left).wire ≠ ((target width).bit right).wire := by
  intro same
  have values := congrArg Fin.val same
  change (divisorLengthBit width left.rev).wire.val =
    (divisorLengthBit width right.rev).wire.val at values
  rw [divisorLengthBit_wire, divisorLengthBit_wire, Fin.val_rev, Fin.val_rev] at values
  apply different
  apply Fin.ext
  have leftBound := left.isLt
  have rightBound := right.isLt
  omega

/-- A bounded mathematical length represented in the source's existing finite field. -/
def constant (width value : Nat) (bounded : value ≤ width) : Fin (2 ^ width.size) :=
  ⟨value, bounded.trans_lt (Nat.lt_size_self width)⟩

/-- Static length label associated with one possible leading payload position. -/
def positionConstant (width : Nat) (index : Fin width) : Fin (2 ^ width.size) :=
  constant width (width - index.val) (Nat.sub_le _ _)

private theorem constant_preserves_payload (width : Nat) (value : Fin (2 ^ width.size))
    (state : Registers width) :
    payloadValue (Word.xorConstantStep (target width) value state) = payloadValue state := by
  rw [Word.xorConstantStep_eq_indicesStep]
  generalize Word.constantOneIndices value = indices
  induction indices generalizing state with
  | nil => rfl
  | cons bit rest ih =>
      change payloadValue (Word.xorConstantIndicesStep (target width) rest
        ((divisorLengthBit width bit.rev).flip state)) = payloadValue state
      rw [ih, payloadValue_flip]

/-- Each candidate writes only the set bits of its static length label using the actual gates. -/
def positionGates (width : Nat) (index : Fin width) : List (GateSpec (encoding width)) :=
  (Word.constantOneIndices (positionConstant width index)).flatMap fun bit =>
    firstOneGates width index bit.rev

private theorem position_indices_step (width : Nat) (index : Fin width)
    (bits : List (Fin width.size)) (state : Registers width) :
    GateSpec.stepList (bits.flatMap fun bit => firstOneGates width index bit.rev) state =
      if (payloadValue state).size = width - index.val
      then Word.xorConstantIndicesStep (target width) bits state else state := by
  induction bits generalizing state with
  | nil => simp [Word.xorConstantIndicesStep, GateSpec.stepList]
  | cons bit rest ih =>
      rw [List.flatMap_cons, GateSpec.stepList_append, firstOneGates_step_size]
      by_cases selected : (payloadValue state).size = width - index.val
      · rw [if_pos selected, ih, payloadValue_flip, if_pos selected]
        rw [if_pos selected]
        simp only [Word.xorConstantIndicesStep, List.foldl_cons, target]
      · rw [if_neg selected, ih, if_neg selected]
        rw [if_neg selected]

/-- Every candidate call has a full-register conditional constant-xor action. -/
theorem positionGates_step (width : Nat) (index : Fin width) (state : Registers width) :
    GateSpec.stepList (positionGates width index) state =
      if (payloadValue state).size = width - index.val
      then Word.xorConstantStep (target width) (positionConstant width index) state
      else state := by
  rw [positionGates, position_indices_step, Word.xorConstantStep_eq_indicesStep]

/-- The complete width-dependent initialization program visits every possible leading bit once. -/
def gates (width : Nat) : List (GateSpec (encoding width)) :=
  (List.ofFn fun index : Fin width => index).flatMap (positionGates width)

private theorem indices_step (width value : Nat) (bounded : value ≤ width)
    (indices : List (Fin width)) (distinct : indices.Nodup) (state : Registers width)
    (input : (payloadValue state).size = value) :
    GateSpec.stepList (indices.flatMap (positionGates width)) state =
      if ∃ index ∈ indices, width - index.val = value
      then Word.xorConstantStep (target width) (constant width value bounded) state else state := by
  induction indices generalizing state with
  | nil => simp [GateSpec.stepList]
  | cons head rest ih =>
      rw [List.flatMap_cons, GateSpec.stepList_append, positionGates_step, input]
      by_cases selected : width - head.val = value
      · rw [if_pos selected.symm]
        have labels : positionConstant width head = constant width value bounded :=
          Fin.ext selected
        rw [labels]
        have preserved :
            (payloadValue (Word.xorConstantStep (target width)
              (constant width value bounded) state)).size = value := by
          rw [constant_preserves_payload, input]
        rw [ih distinct.tail _ preserved]
        have noMore : ¬∃ index ∈ rest, width - index.val = value := by
          rintro ⟨index, present, selectedAgain⟩
          have same : index = head := by
            apply Fin.ext
            have indexBound := index.isLt
            have headBound := head.isLt
            omega
          exact distinct.notMem (same ▸ present)
        have present : ∃ index ∈ head :: rest, width - index.val = value :=
          ⟨head, List.mem_cons_self, selected⟩
        rw [if_neg noMore, if_pos present]
      · rw [if_neg (Ne.symm selected), ih distinct.tail state input]
        have selection :
            (∃ index ∈ head :: rest, width - index.val = value) ↔
              ∃ index ∈ rest, width - index.val = value := by
          constructor
          · rintro ⟨index, present, chosen⟩
            rcases List.mem_cons.mp present with same | later
            · subst index
              exact False.elim (selected chosen)
            · exact ⟨index, later, chosen⟩
          · rintro ⟨index, present, chosen⟩
            exact ⟨index, List.mem_cons_of_mem head present, chosen⟩
        simp only [selection]

private theorem xor_zero (width : Nat) (state : Registers width) :
    Word.xorConstantStep (target width) (constant width 0 (Nat.zero_le width)) state = state := by
  simp [Word.xorConstantStep, Word.xorConstantGates, Word.constantOneIndices,
    constant, GateSpec.stepList]

/-- The literal initialization circuit xors the exact current divisor length on every full input. -/
theorem gates_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (gates width) state =
      Word.xorConstantStep (target width)
        (constant width (payloadValue state).size (Nat.size_le.mpr (payloadValue_fits state)))
        state := by
  let length := (payloadValue state).size
  have bounded : length ≤ width := Nat.size_le.mpr (payloadValue_fits state)
  rw [gates, indices_step width length bounded _
    (List.nodup_ofFn_ofInjective (fun _ _ same => same)) state rfl]
  by_cases positive : 0 < length
  · have present : ∃ index ∈ List.ofFn (fun index : Fin width => index),
        width - index.val = length := by
      let chosen : Fin width := ⟨width - length, by omega⟩
      refine ⟨chosen, ?_, ?_⟩
      · exact List.mem_ofFn.mpr ⟨chosen, rfl⟩
      · change width - (width - length) = length
        omega
    exact if_pos present
  · have zero : length = 0 := by omega
    have absent : ¬∃ index ∈ List.ofFn (fun index : Fin width => index),
        width - index.val = length := by
      rintro ⟨index, _, chosen⟩
      have indexBound := index.isLt
      omega
    rw [if_neg absent]
    have labels : constant width (payloadValue state).size
        (Nat.size_le.mpr (payloadValue_fits state)) = constant width 0 (Nat.zero_le width) :=
      Fin.ext zero
    rw [labels, xor_zero]

/-- The actual finite length field receives the binary length by bitwise xor. -/
theorem gates_divisorLength (width : Nat) (state : Registers width) :
    (GateSpec.stepList (gates width) state).divisorLength =
      state.divisorLength ^^^ BitVec.ofNat width.size (payloadValue state).size := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit within
  rw [gates_step]
  have actual := Word.xorConstantStep_get_target (target width)
    (constant width (payloadValue state).size (Nat.size_le.mpr (payloadValue_fits state)))
    ⟨bit, within⟩ (fun other different => target_distinct width other _ different) state
  rw [target_get, target_get] at actual
  simpa only [BitVec.getLsbD_xor, BitVec.getLsbD_ofNat, within, decide_true,
    Bool.true_and, constant] using actual

/-- An internally prepared zero length field becomes the current payload length exactly. -/
theorem gates_divisorLength_of_zero (width : Nat) (state : Registers width)
    (zero : state.divisorLength = 0#width.size) :
    (GateSpec.stepList (gates width) state).divisorLength =
      BitVec.ofNat width.size (payloadValue state).size := by
  rw [gates_divisorLength, zero, BitVec.zero_xor]

/-- The same elementary gate list compiles directly to its native unitary circuit. -/
def program (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  GateSpec.programList (gates width)

/-- Correctness holds as exact normalized-vector action, including every work coordinate. -/
theorem program_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (program width)
      (fun state => Word.xorConstantStep (target width)
        (constant width (payloadValue state).size (Nat.size_le.mpr (payloadValue_fits state)))
        state) :=
  GateSpec.realizesList_congrStep (gates width) (gates_step width)

end

end QuantumAlg.MAU.Inversion.SharedEEA.InitialLengthWrite
