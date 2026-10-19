/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Word.PowerOfTwo.Resources
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord

/-!
# Actual signed constant loading by native unit steps

The original self-XOR and sign-selected unit-step loop load any compile-time
integer modulo the supplied word width, from arbitrary initial storage.
No extra quantum or classical storage is allocated.
-/

namespace QuantumAlg.ClassicalRoutines.ConstantWord.Signed

open Execution
open NumberTheory.SignedWord

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

section Descriptor

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Compilation-time increment or decrement selected by the integer's sign. -/
def opcode (value : Int) : Resource.WordUnaryOpcode :=
  if 0 ≤ value then .increment else .decrement

/-- The corresponding exact integer change of one native instruction. -/
def unitChange (value : Int) : Int := if 0 ≤ value then 1 else -1

/-- One actual in-place signed loading instruction. -/
def stepOp (value : Int) (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary (opcode value) width ctx (.storage output.toCStorageRef) output

/-- The actual chronological native store updates of the signed loop. -/
def loopStore (value : Int) (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) : Store ctx :=
  (fun current => current.applyOp (stepOp value output))^[count] store

/-- Each actual increment or decrement has the exact original modular signed effect. -/
lemma stepOp_correct (value : Int) (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) (current : Int)
    (rep : RawSignedRepresents (store.read (.storage output.toCStorageRef)) current) :
    RawSignedRepresents ((store.applyOp (stepOp value output)).read
      (.storage output.toCStorageRef)) (current + unitChange value) := by
  change RawSignedRepresents ((store.applyOp (stepOp value output)).read
    (.storage (stepOp value output).outputRef.toCStorageRef)) _
  rw [Store.read_applyOp_output]
  change RawSignedRepresents (Resource.WordUnaryOpcode.eval (opcode value) width
    (store.read (.storage output.toCStorageRef))) _
  by_cases nonnegative : 0 ≤ value
  · simpa only [opcode, unitChange, if_pos nonnegative] using
      rawSignedWordRepresents_increment _ current rep
  · simpa only [opcode, unitChange, if_neg nonnegative, sub_eq_add_neg] using
      rawSignedWordRepresents_decrement _ current rep

/-- The actual signed loop preserves the original exact modular affine invariant. -/
lemma loopInto_correct (value : Int) (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) (current : Int)
    (rep : RawSignedRepresents (store.read (.storage output.toCStorageRef)) current) :
    RawSignedRepresents ((loopStore value count output store).read
      (.storage output.toCStorageRef)) (current + (count : Int) * unitChange value) := by
  induction count generalizing store current with
  | zero => simpa only [loopStore, Function.iterate_zero, id_eq, Nat.cast_zero, zero_mul, add_zero]
      using rep
  | succ count ih =>
    change RawSignedRepresents
      (((fun current => current.applyOp (stepOp value output))^[count + 1] store).read
        (.storage output.toCStorageRef)) _
    rw [Function.iterate_succ_apply]
    have next := ih (store.applyOp (stepOp value output)) (current + unitChange value)
      (stepOp_correct value output store current rep)
    have arithmetic : current + ((count + 1 : Nat) : Int) * unitChange value =
        current + unitChange value + (count : Int) * unitChange value := by
      push_cast
      ring
    rw [arithmetic]
    exact next

/-- The original absolute-value loop with the selected sign reconstructs its integer parameter. -/
lemma signed_count (value : Int) : (value.natAbs : Int) * unitChange value = value := by
  rw [Int.natCast_natAbs]
  by_cases nonnegative : 0 ≤ value
  · simp [unitChange, nonnegative, abs_of_nonneg nonnegative]
  · simp [unitChange, nonnegative, abs_of_neg (lt_of_not_ge nonnegative)]

/-- Every actual loop iteration preserves all structural reads outside its destination. -/
lemma loopInto_callerFrame (value : Int) (count : Nat)
    (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoids : output.key ∉ other.storageKeys) :
    (loopStore value count output store).read other = store.read other := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
    change (((fun current => current.applyOp (stepOp value output))^[count + 1] store).read
      other) = _
    rw [Function.iterate_succ_apply]
    exact (ih _).trans (Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoids)

end Descriptor

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Execute the prescribed native instructions with the compilation-time sign. -/
def loopInto (value : Int) (count : Nat) (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit model ctx ctx :=
  BitWord.repeatInstruction (execution := model) (stepOp value output) count

/-- Actual signed-loop store and every chronological native result. -/
def loopStep (value : Int) (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) : Store ctx × (loopInto (model := model) value count output).Path :=
  BitWord.repeatStep (execution := model) (stepOp value output) count store

/-- Explicit native self-XOR initializes the destination before the original signed loop. -/
def into (value : Int) (output : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (Word.PowerOfTwo.clearOp output))
    (loopInto (model := model) value value.natAbs output)

/-- Actual initialized store and both chronological paths of signed constant loading. -/
def step (value : Int) (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (into (model := model) value output).Path :=
  let first := BitWord.instructionStep (execution := model) (Word.PowerOfTwo.clearOp output) store
  let loop := loopStep (model := model) value value.natAbs output first.1
  (loop.1, (first.2, loop.2))

/-- The actual signed loop retains the shared service and all original reference correlations. -/
lemma loopInto_execute (value : Int) (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (loopInto (model := model) value count output).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := loopStep (model := model) value count output entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) :=
  BitWord.bitWord_repeatInstruction_execute
    (environment := environment) (execution := model) (stepOp value output) count state

/-- Complete actual signed loading preserves every original service and quantum-reference block. -/
lemma into_execute (value : Int) (output : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) value output).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := step (model := model) value output entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    (BitWord.instruction (execution := model) (Word.PowerOfTwo.clearOp output))
    (loopInto (model := model) value value.natAbs output)
    (fun before =>
      let result := BitWord.instructionStep (execution := model)
        (Word.PowerOfTwo.clearOp output) before.1
      ((result.1, before.2), result.2))
    (fun before =>
      let result := loopStep (model := model) value value.natAbs output before.1
      ((result.1, before.2), result.2)) ?_ ?_ Reference state).trans ?_
  · intro reference history _ input
    exact (BitWord.bitWord_instruction_execute (environment := environment) (execution := model)
      (Word.PowerOfTwo.clearOp output) input).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  · intro reference history _ input
    exact (loopInto_execute (model := model) value value.natAbs output reference input).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual self-initialization and the original signed loop load the requested raw integer. -/
lemma into_correct (value : Int) (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    RawSignedRepresents
      ((step (model := model) value output store).1.read
        (.storage output.toCStorageRef)) value := by
  have zero : RawSignedRepresents ((store.applyOp (Word.PowerOfTwo.clearOp output)).read
      (.storage output.toCStorageRef)) 0 := by
    change Int.ModEq _
      ((((store.applyOp (Word.PowerOfTwo.clearOp output)).read
        (.storage output.toCStorageRef)).toNat : Nat) : Int) 0
    rw [Word.PowerOfTwo.clear_read]
    rfl
  change RawSignedRepresents ((loopStore value value.natAbs output
    (store.applyOp (Word.PowerOfTwo.clearOp output))).read (.storage output.toCStorageRef)) value
  simpa only [zero_add, signed_count] using loopInto_correct value value.natAbs output
    (store.applyOp (Word.PowerOfTwo.clearOp output)) 0 zero

/-- The actual initialized loader changes only its original supplied destination. -/
lemma into_callerFrame (value : Int) (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoids : output.key ∉ other.storageKeys) :
    (step (model := model) value output store).1.read other = store.read other := by
  change (loopStore value value.natAbs output
    (store.applyOp (Word.PowerOfTwo.clearOp output))).read other = _
  rw [loopInto_callerFrame _ _ _ _ other avoids,
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoids]

end

end QuantumAlg.ClassicalRoutines.ConstantWord.Signed
