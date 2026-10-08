/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.BorrowedIncrement
import all QuantumAlg.Primitives.MAU.Addition.HRS.DirtyControl

/-!
# HRS controlled increment with an internally borrowed word

The target and borrowed words each have `n` bits, followed by one control
bit. Every gate is an actual CNOT or Toffoli. A controlled Toffoli borrows
an idle wire inside those same two words and restores it immediately.
There is no extra work register and no clean-input promise
[HRS16, paper.tex:187-195,219-224].

The Boolean component of the reused TTK overflow layout is a preserved
control here. Its unknown initial value is not treated as a predicate.
The recursive HRS bridge later cancels that initial value explicitly.
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

open EncodedBit.GateSpec

/-- Lower one controlled operand Toffoli using an idle existing operand wire. -/
def controlledOperandToffoli (n : Nat) (a b target : EncodedBit (TTK.encoding n))
    (hab : a.wire ≠ b.wire) (hat : a.wire ≠ target.wire)
    (hbt : b.wire ≠ target.wire) : List (EncodedBit.GateSpec (TTK.overflowEncoding n)) :=
  let hn := hrsTwoLe_of_toffoli n a b target hab hat hbt
  let work := spareOperandBit n hn a b target
  let hwork := hrsSpareOperandBit_disjoint n hn a b target
  dirtyControlledToffoliGates (TTK.overflowBit n) (TTK.withOverflowBit a)
    (TTK.withOverflowBit b) (TTK.withOverflowBit target) (TTK.withOverflowBit work)
    (TTK.ttkWithOverflowBit_output_disjoint a).symm
    (TTK.ttkWithOverflowBit_output_disjoint work).symm
    (TTK.ttkWithOverflowBit_disjoint a work hwork.1.symm)
    (TTK.ttkWithOverflowBit_disjoint b work hwork.2.1.symm)
    (TTK.ttkWithOverflowBit_disjoint b target hbt)
    (TTK.ttkWithOverflowBit_disjoint work target hwork.2.2)

/-- Add the trailing control to one actual operand gate without increasing
the two-word workspace. -/
def controlledBorrowedGate (n : Nat) : EncodedBit.GateSpec (TTK.encoding n) →
    List (EncodedBit.GateSpec (TTK.overflowEncoding n))
  | .x target =>
      [.cnot (TTK.overflowBit n) (TTK.withOverflowBit target)
        (TTK.ttkWithOverflowBit_output_disjoint target).symm]
  | .cnot source target hst =>
      [.toffoli (TTK.overflowBit n) (TTK.withOverflowBit source) (TTK.withOverflowBit target)
        (TTK.ttkWithOverflowBit_output_disjoint source).symm
        (TTK.ttkWithOverflowBit_output_disjoint target).symm
        (TTK.ttkWithOverflowBit_disjoint source target hst)]
  | .toffoli a b target hab hat hbt => controlledOperandToffoli n a b target hab hat hbt

/-- Every lowered gate preserves the control and conditionally executes the
original gate, with the temporary dirty wire fully restored. -/
theorem hrsControlledBorrowedGate_step (n : Nat) (gate : EncodedBit.GateSpec (TTK.encoding n))
    (state : TTK.OverflowRegisters n) :
    stepList (controlledBorrowedGate n gate) state =
      if state.2 then (gate.step state.1, state.2) else state := by
  cases gate with
  | x target => rfl
  | cnot source target hst =>
      change (if state.2 && source.get state.1 then (target.flip state.1, state.2) else state) =
        if state.2 then
          ((if source.get state.1 then target.flip state.1 else state.1), state.2)
        else state
      rcases state with ⟨words, control⟩
      cases control <;> cases source.get words <;> rfl
  | toffoli a b target hab hat hbt =>
      let hn := hrsTwoLe_of_toffoli n a b target hab hat hbt
      let work := spareOperandBit n hn a b target
      have hwork := hrsSpareOperandBit_disjoint n hn a b target
      have hstep := hrsDirtyControlledToffoli_step (TTK.overflowBit n) (TTK.withOverflowBit a)
        (TTK.withOverflowBit b) (TTK.withOverflowBit target) (TTK.withOverflowBit work)
        (TTK.ttkWithOverflowBit_output_disjoint a).symm
        (TTK.ttkWithOverflowBit_output_disjoint work).symm
        (TTK.ttkWithOverflowBit_disjoint a work hwork.1.symm)
        (TTK.ttkWithOverflowBit_disjoint b work hwork.2.1.symm)
        (TTK.ttkWithOverflowBit_disjoint b target hbt)
        (TTK.ttkWithOverflowBit_disjoint work target hwork.2.2)
        (TTK.ttkWithOverflowBit_output_disjoint b).symm
        (TTK.ttkWithOverflowBit_output_disjoint target).symm
        (TTK.ttkWithOverflowBit_disjoint a b hab)
        (TTK.ttkWithOverflowBit_disjoint a target hat) state
      change stepList (controlledBorrowedGate n (.toffoli a b target hab hat hbt)) state =
        if (state.2 && a.get state.1) && b.get state.1 then
          (target.flip state.1, state.2) else state at hstep
      rw [hstep]
      change (if (state.2 && a.get state.1) && b.get state.1 then
          (target.flip state.1, state.2) else state) =
        if state.2 then
          ((if a.get state.1 && b.get state.1 then target.flip state.1 else state.1), state.2)
        else state
      rcases state with ⟨words, control⟩
      cases control <;> cases a.get words <;> cases b.get words <;> rfl

/-- Controlled primitive expansion of an actual operand list. -/
def controlledBorrowedList (n : Nat) (gates : List (EncodedBit.GateSpec (TTK.encoding n))) :
    List (EncodedBit.GateSpec (TTK.overflowEncoding n)) :=
  (gates.map (controlledBorrowedGate n)).flatten

/-- The lowered list has the exact conditional action of the original list. -/
theorem hrsControlledBorrowedList_step (n : Nat)
    (gates : List (EncodedBit.GateSpec (TTK.encoding n))) (state : TTK.OverflowRegisters n) :
    stepList (controlledBorrowedList n gates) state =
      if state.2 then (stepList gates state.1, state.2) else state := by
  induction gates generalizing state with
  | nil =>
      rcases state with ⟨words, control⟩
      cases control <;> rfl
  | cons gate rest ih =>
      change stepList ((controlledBorrowedGate n gate) ++ controlledBorrowedList n rest) state = _
      rw [stepList_append, hrsControlledBorrowedGate_step]
      rcases state with ⟨words, control⟩
      cases control with
      | false => exact ih (words, false)
      | true => exact ih (gate.step words, true)

/-- Preserve the borrowed word and control, and increment exactly on a true control. -/
def controlledBorrowedIncrementOutput {n : Nat} (state : TTK.OverflowRegisters n) :
    TTK.OverflowRegisters n :=
  if state.2 then (borrowedIncrementOutput state.1, state.2) else state

/-- The actual CNOT/Toffoli list for the HRS controlled incrementer. -/
def controlledBorrowedIncrementGates (n : Nat) :
    List (EncodedBit.GateSpec (TTK.overflowEncoding n)) :=
  controlledBorrowedList n (borrowedIncrementGates n)

/-- Compile on exactly two operand words and one preserved control bit. -/
def controlledBorrowedIncrementProgram (n : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (TTK.overflowEncoding n).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (controlledBorrowedIncrementGates n)

/-- Exact all-width controlled increment, with arbitrary borrowed and control values. -/
theorem hrsControlledBorrowedIncrement_step (n : Nat) (state : TTK.OverflowRegisters n) :
    stepList (controlledBorrowedIncrementGates n) state =
      controlledBorrowedIncrementOutput state := by
  rw [controlledBorrowedIncrementGates, hrsControlledBorrowedList_step, hrsBorrowedIncrement_step]
  rfl

/-- Exact amplitudes retain joint coherence without an initialization promise. -/
theorem hrsControlledBorrowedIncrement_realizes (n : Nat) :
    UnitaryCircuit.Realizes (TTK.overflowEncoding n) (controlledBorrowedIncrementProgram n)
      controlledBorrowedIncrementOutput :=
  realizesList_congrStep (QubitLayout.canonical _) .empty
    (controlledBorrowedIncrementGates n)
    (hrsControlledBorrowedIncrement_step n)

/-- The entire borrowed word and the control bit are restored. -/
theorem hrsControlledBorrowedIncrement_restores (n : Nat) (state : TTK.OverflowRegisters n) :
    (stepList (controlledBorrowedIncrementGates n) state).1.1 = state.1.1 ∧
      (stepList (controlledBorrowedIncrementGates n) state).2 = state.2 := by
  rw [hrsControlledBorrowedIncrement_step]
  unfold controlledBorrowedIncrementOutput
  cases h : state.2 <;> simp [h, borrowedIncrementOutput]

/-- The implementation uses `n` borrowed bits, `n` target bits, and its control only. -/
theorem hrsControlledBorrowedIncrement_interface (n : Nat) :
    (TTK.overflowEncoding n).width = 2 * n + 1 ∧
      (QubitLayout.canonical (TTK.overflowEncoding n).width).systemIdx =
        List.range (2 * n + 1) := by
  constructor
  · exact TTK.ttkOverflowEncoding_width n
  · rw [TTK.ttkOverflowEncoding_width]
    exact QubitLayout.canonical_systemIdx (2 * n + 1)

end

end QuantumAlg.MAU.Addition.HRS
