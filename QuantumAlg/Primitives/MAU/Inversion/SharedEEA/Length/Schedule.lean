/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Length.Field

/-!
# Actual finite native schedule for a dynamic-boundary length XOR

The emitted schedule enumerates all values of the existing finite boundary
register, with no input-dependent classical choice of a circuit. Exactly
one fixed-key gate list matches the actual retained value. That list reads
the proper original work-word region and XORs its size into the existing
target length field [LYL+26, sec_EEA/sub_regshare.tex:309-313;
sec_circuit/sub_block_new.tex:211-219,338-341].

Each gate list restores arbitrary Iter and all its source values. Complete
record correctness holds for every finite input, including oversized keys,
zero regions, and nonzero initial lengths. The literal reverse of the same
emitted list performs the exact inverse on the entire original frame.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.LengthSchedule

noncomputable section

open EncodedBit LengthCoordinates LengthRead LengthField

/-- All possible values of the real retained boundary field, each occurring exactly once. -/
def keys (width : Nat) : List (BitVec width.size) :=
  List.ofFn fun label : Fin (2 ^ width.size) => BitVec.ofFin label

theorem keys_nodup (width : Nat) : (keys width).Nodup :=
  List.nodup_ofFn_ofInjective fun _ _ same =>
    congrArg (fun word : BitVec width.size => word.toFin) same

theorem mem_keys (width : Nat) (key : BitVec width.size) : key ∈ keys width :=
  List.mem_ofFn.mpr ⟨key.toFin, rfl⟩

/-- This is the literal number of static boundary calls, without any semantic branch discount. -/
theorem keys_length (width : Nat) : (keys width).length = 2 ^ width.size := by
  simp only [keys, List.length_ofFn]

/-- Mathematical full-frame action of the actual dynamic read and finite length XOR. -/
def step (width : Nat) (field : Field) (firstWord : Bool) (state : Registers width) :
    Registers width :=
  xorLength field (BitVec.ofNat width.size
    (payloadValue field (boundaryValue field state) firstWord state).size) state

/-- The actual retained boundary remains available to every later static selector. -/
theorem step_boundary (width : Nat) (field : Field) (firstWord : Bool) (state : Registers width) :
    boundaryValue field (step width field firstWord state) = boundaryValue field state :=
  boundary_xorLength field _ state

/-- The complete original work word is retained by the full schedule action. -/
theorem step_sourceWord (width : Nat) (field : Field) (firstWord observed : Bool)
    (state : Registers width) :
    sourceWord observed (step width field firstWord state) = sourceWord observed state :=
  sourceWord_xorLength field _ observed state

private theorem payload_xorLength {width : Nat} (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (mask : BitVec width.size) (state : Registers width) :
    payloadValue field key firstWord (xorLength field mask state) =
      payloadValue field key firstWord state := by
  unfold payloadValue
  rw [sourceWord_xorLength]

/-- Repeating the same dynamic read and finite XOR restores all original fields exactly. -/
theorem step_involutive (width : Nat) (field : Field) (firstWord : Bool) :
    Function.Involutive (step width field firstWord) := by
  intro state
  simp only [step, boundary_xorLength, payload_xorLength]
  exact xorLength_involutive field _ state

private theorem matching_step (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (state : Registers width) (matched : boundaryValue field state = key) :
    GateSpec.stepList (LengthWrite.gates width field key firstWord) state =
      step width field firstWord state := by
  rw [LengthField.gates_step_eq, if_pos matched]
  unfold step
  rw [matched]

private theorem keys_step (width : Nat) (field : Field) (firstWord : Bool)
    (selected : List (BitVec width.size)) (distinct : selected.Nodup) (state : Registers width) :
    GateSpec.stepList (selected.flatMap fun key => LengthWrite.gates width field key firstWord)
        state =
      if boundaryValue field state ∈ selected then step width field firstWord state else state := by
  induction selected generalizing state with
  | nil => simp [GateSpec.stepList]
  | cons head rest ih =>
      rw [List.flatMap_cons, GateSpec.stepList_append]
      by_cases matched : boundaryValue field state = head
      · rw [matching_step width field head firstWord state matched, ih distinct.tail,
          step_boundary]
        have absent : boundaryValue field state ∉ rest := by
          intro present
          exact distinct.notMem (matched ▸ present)
        have present : boundaryValue field state ∈ head :: rest :=
          List.mem_cons.mpr (Or.inl matched)
        rw [if_neg absent, if_pos present]
      · rw [LengthField.gates_step_eq, if_neg matched, ih distinct.tail state]
        simp only [List.mem_cons, matched, false_or]

/-- Actual native gate list for every retained key and its complete leading-position writer. -/
def gates (width : Nat) (field : Field) (firstWord : Bool) : List (GateSpec (encoding width)) :=
  (keys width).flatMap fun key => LengthWrite.gates width field key firstWord

/-- The complete static gate list reads the current boundary and writes the actual region's size. -/
theorem gates_step (width : Nat) (field : Field) (firstWord : Bool) (state : Registers width) :
    GateSpec.stepList (gates width field firstWord) state = step width field firstWord state := by
  rw [gates, keys_step width field firstWord _ (keys_nodup width) state,
    if_pos (mem_keys width _)]

/-- Literal reversal of every emitted elementary gate has the precise complete inverse action. -/
theorem gates_reverse_step (width : Nat) (field : Field) (firstWord : Bool)
    (state : Registers width) :
    GateSpec.stepList (gates width field firstWord).reverse state =
      step width field firstWord state := by
  have forward : GateSpec.stepList (gates width field firstWord)
      (step width field firstWord state) = state :=
    (gates_step width field firstWord _).trans (step_involutive width field firstWord state)
  calc
    _ = GateSpec.stepList (gates width field firstWord).reverse
        (GateSpec.stepList (gates width field firstWord) (step width field firstWord state)) :=
      congrArg (GateSpec.stepList (gates width field firstWord).reverse) forward.symm
    _ = _ := GateSpec.stepList_reverse_stepList _ _

/-- The unitary circuit is compiled directly from the same actual native gate list. -/
def program (width : Nat) (field : Field) (firstWord : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates width field firstWord)

/-- Complete basis-vector correctness retains every field and all relative amplitudes. -/
theorem program_realizes (width : Nat) (field : Field) (firstWord : Bool) :
    UnitaryCircuit.Realizes (encoding width) (program width field firstWord)
      (step width field firstWord) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
    (gates width field firstWord) (gates_step width field firstWord)

/-- The actual trace contains every emitted elementary gate, including all nonmatching keys. -/
theorem program_eventTrace (width : Nat) (field : Field) (firstWord : Bool) :
    (program width field firstWord).eventTrace =
      (gates width field firstWord).map (GateSpec.event .empty) := by
  rw [program, GateSpec.programList_eventTrace]

end

end QuantumAlg.MAU.Inversion.SharedEEA.LengthSchedule
