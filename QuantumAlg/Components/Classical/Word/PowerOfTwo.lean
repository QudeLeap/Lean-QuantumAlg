/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Model.BitWord.Iteration
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Actual native loading of a fixed power of two

Self-XOR and increment initialize the supplied word before a prescribed number
of native one-bit left shifts. The result is exactly the low-word encoding of
the power for every width, with no initial-value premise or additional cell.
-/

namespace QuantumAlg.ClassicalRoutines.Word.PowerOfTwo

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

section Descriptor

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Native self-XOR of the actual supplied word. -/
def clearOp (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .bitXor width ctx
    (.product (.storage output.toCStorageRef) (.storage output.toCStorageRef)) output

/-- Native increment of the actual supplied word. -/
def incrementOp (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .increment width ctx (.storage output.toCStorageRef) output

/-- Native one-bit left shift of the actual supplied word. -/
def shiftOp (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .shiftLeft width ctx (.storage output.toCStorageRef) output

/-- The chronological actual store after the prescribed native shifts. -/
def shiftStore (count : Nat) (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx := (fun current => current.applyOp (shiftOp output))^[count] store

/-- Native self-XOR writes zero independently of the incoming word, including width zero. -/
theorem clear_read (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((store.applyOp (clearOp output)).read (.storage output.toCStorageRef)).toNat = 0 := by
  simp only [Store.applyOp, clearOp, ClassicalOp.outputRef, Store.read_write_same,
    ClassicalOp.inputRef, ClassicalOp.eval_wordBinary]
  change (((store.read (.storage output.toCStorageRef)).toNat ^^^
    (store.read (.storage output.toCStorageRef)).toNat) % 2 ^ width) = 0
  rw [Nat.xor_self, Nat.zero_mod]

/-- One actual native left shift doubles the original low-word value modulo the supplied width. -/
theorem shift_read (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((store.applyOp (shiftOp output)).read (.storage output.toCStorageRef)).toNat =
      (2 * (store.read (.storage output.toCStorageRef)).toNat) % 2 ^ width := by
  simp only [Store.applyOp, shiftOp, ClassicalOp.outputRef, Store.read_write_same,
    ClassicalOp.inputRef, ClassicalOp.eval_wordUnary]
  rfl

private theorem mod_mul (a b modulus : Nat) :
    (a % modulus * b) % modulus = (a * b) % modulus :=
  (Nat.mod_modEq a modulus).mul (Nat.ModEq.refl b)

/-- The actual repeated shifts multiply by the exact requested power modulo the word width. -/
theorem shiftInto_read (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    ((shiftStore count output store).read (.storage output.toCStorageRef)).toNat =
      ((store.read (.storage output.toCStorageRef)).toNat * 2 ^ count) % 2 ^ width := by
  change (((fun current => current.applyOp (shiftOp output))^[count] store).read
    (.storage output.toCStorageRef)).toNat = _
  induction count generalizing store with
  | zero => simp [Nat.mod_eq_of_lt (store.read (.storage output.toCStorageRef)).toNat_lt]
  | succ count ih =>
    rw [Function.iterate_succ_apply, ih, shift_read, mod_mul, pow_succ]
    congr 1
    ring

/-- Every actual native shift retains all structural reads outside the original output word. -/
theorem shiftInto_callerFrame (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoids : output.key ∉ other.storageKeys) :
    (shiftStore count output store).read other = store.read other := by
  change ((fun current => current.applyOp (shiftOp output))^[count] store).read other = _
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
    rw [Function.iterate_succ_apply, ih]
    exact Store.read_applyOp_of_not_mem_storageKeys store (shiftOp output) other avoids

end Descriptor

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The prescribed number of actual selected native one-bit left shifts. -/
def shiftInto (count : Nat) (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit model ctx ctx :=
  BitWord.repeatInstruction (execution := model) (shiftOp output) count

/-- The actual shift store and every chronological native output. -/
def shiftStep (count : Nat) (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (shiftInto (model := model) count output).Path :=
  BitWord.repeatStep (execution := model) (shiftOp output) count store

/-- Actual self-XOR followed by increment initializes the low-word encoding of one. -/
def seedInto (output : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (clearOp output))
    (BitWord.instruction (execution := model) (incrementOp output))

/-- The actual initialized store and both computed native outputs. -/
def seedStep (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (seedInto (model := model) output).Path :=
  let first := BitWord.instructionStep (execution := model) (clearOp output) store
  let last := BitWord.instructionStep (execution := model) (incrementOp output) first.1
  (last.1, (first.2, last.2))

/-- Initialize the original word and perform the actual fixed number of native shifts. -/
def into (count : Nat) (output : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .seq (seedInto (model := model) output) (shiftInto (model := model) count output)

/-- The actual power-loading store and its full chronological native path. -/
def step (count : Nat) (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (into (model := model) count output).Path :=
  let seeded := seedStep (model := model) output store
  let shifted := shiftStep (model := model) count output seeded.1
  (shifted.1, (seeded.2, shifted.2))

/-- Native repeated shifts retain the service state and every quantum-reference block. -/
theorem shiftInto_execute (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (shiftInto (model := model) count output).execute Reference state =
      state.mapClassical (fun entry =>
        let result := shiftStep (model := model) count output entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) :=
  BitWord.bitWord_repeatInstruction_execute (execution := model) (shiftOp output) count state

/-- Actual native initialization preserves the complete incoming service and reference state. -/
theorem seedInto_execute (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (seedInto (model := model) output).execute Reference state =
      state.mapClassical (fun entry =>
        let result := seedStep (model := model) output entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  simp only [seedInto, Circuit.execute_seq, BitWord.bitWord_instruction_execute, State.mapHistory]
  repeat' rw [ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The complete loader preserves all original service, quantum and reference correlations. -/
theorem into_execute (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) count output).execute Reference state =
      state.mapClassical (fun entry =>
        let result := step (model := model) count output entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (seedInto (model := model) output) (shiftInto (model := model) count output)
    (fun before =>
      let result := seedStep (model := model) output before.1
      ((result.1, before.2), result.2))
    (fun before =>
      let result := shiftStep (model := model) count output before.1
      ((result.1, before.2), result.2)) ?_ ?_ Reference state).trans ?_
  · intro reference history _ input
    exact (seedInto_execute (model := model) output reference input).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · intro reference history _ input
    exact (shiftInto_execute (model := model) count output reference input).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual native initialization writes the exact low-word encoding of one. -/
theorem seed_read (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((seedStep (model := model) output store).1.read (.storage output.toCStorageRef)).toNat =
      1 % 2 ^ width := by
  change (((store.applyOp (clearOp output)).applyOp (incrementOp output)).read
    (.storage output.toCStorageRef)).toNat = _
  simp only [Store.applyOp, incrementOp, ClassicalOp.outputRef, Store.read_write_same,
    ClassicalOp.inputRef, ClassicalOp.eval_wordUnary]
  change (((store.applyOp (clearOp output)).read (.storage output.toCStorageRef)).toNat + 1) %
    2 ^ width = _
  rw [clear_read, Nat.zero_add]

/-- Arbitrary initial words load precisely the low-word encoding of the prescribed power of two. -/
theorem into_read (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    ((step (model := model) count output store).1.read (.storage output.toCStorageRef)).toNat =
      2 ^ count % 2 ^ width := by
  change ((shiftStore count output (seedStep (model := model) output store).1).read
    (.storage output.toCStorageRef)).toNat = _
  rw [shiftInto_read, seed_read, mod_mul, Nat.one_mul]

/-- Initialization and every actual native shift preserve the complete nonoutput caller frame. -/
theorem into_callerFrame (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoids : output.key ∉ other.storageKeys) :
    (step (model := model) count output store).1.read other = store.read other := by
  change (shiftStore count output (seedStep (model := model) output store).1).read other = _
  rw [shiftInto_callerFrame _ _ _ other avoids]
  change ((store.applyOp (clearOp output)).applyOp (incrementOp output)).read other = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (incrementOp output) other avoids,
    Store.read_applyOp_of_not_mem_storageKeys _ (clearOp output) other avoids]

end

end QuantumAlg.ClassicalRoutines.Word.PowerOfTwo
