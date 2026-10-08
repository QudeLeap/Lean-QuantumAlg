/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Components.Classical.Model.BitWord.Execution
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.Borrowed.Preservation

/-!
# Actual one-word initialization after materializing both candidates

The old center word is no longer an input to the candidate checks. A real
self-XOR followed by increment loads one into this same writable cell.
The zero-width equation remains the actual residue modulo its word capacity;
the quadratic candidate width is always positive. The separate zero operand
comes from its real enclosing workspace allocation.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.CheckConstants

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Clear the reusable old center using one actual unsigned self-XOR. -/
def clearOp (one : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .bitXor width ctx
    (.product (.storage one.toCStorageRef) (.storage one.toCStorageRef)) one

/-- Increment the same actual word after clearing it. -/
def incrementOp (one : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .increment width ctx (.storage one.toCStorageRef) one

/-- The two actual native writes to the same physical cell. -/
def storeStep (one : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) : Store ctx :=
  (store.applyOp (clearOp one)).applyOp (incrementOp one)

/-- Self-XOR clears every previous value, including the unique word of width zero. -/
theorem nativeQuadratic_check_clear_read (one : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    ((store.applyOp (clearOp one)).read (.storage one.toCStorageRef)).toNat = 0 := by
  have actual := congrArg CShape.Value.toNat (Store.read_applyOp_output store (clearOp one))
  change ((store.applyOp (clearOp one)).read (.storage one.toCStorageRef)).toNat =
    ((store.read (.storage one.toCStorageRef)).toNat ^^^
      (store.read (.storage one.toCStorageRef)).toNat) % 2 ^ width at actual
  simpa only [Nat.xor_self, Nat.zero_mod] using actual

/-- The actual initialized word is one reduced by the exact declared width. -/
theorem nativeQuadratic_check_one_read (one : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    ((storeStep one store).read (.storage one.toCStorageRef)).toNat = 1 % 2 ^ width := by
  let cleared := store.applyOp (clearOp one)
  have actual := congrArg CShape.Value.toNat
    (Store.read_applyOp_output cleared (incrementOp one))
  change ((storeStep one store).read (.storage one.toCStorageRef)).toNat =
    ((cleared.read (.storage one.toCStorageRef)).toNat + 1) % 2 ^ width at actual
  exact actual.trans (congrArg (fun value : Nat => (value + 1) % 2 ^ width)
    (nativeQuadratic_check_clear_read one store))

/-- Initializing the reused center preserves every other actual structural input completely. -/
theorem nativeQuadratic_check_one_read_other (one : CWriteRef ctx (.unsignedWord width))
    {shape : CShape} (other : CInputRef ctx shape)
    (different : one.key ∉ other.storageKeys) (store : Store ctx) :
    (storeStep one store).read other = store.read other :=
  (Store.read_applyOp_of_not_mem_storageKeys (store.applyOp (clearOp one))
    (incrementOp one) other different).trans
    (Store.read_applyOp_of_not_mem_storageKeys store (clearOp one) other different)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Actual two-instruction initialization, independent of the word's previous value. -/
def code (one : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (clearOp one))
    (BitWord.instruction (execution := model) (incrementOp one))

/-- The actual returned values of both native writes, with the unchanged pure store update. -/
def step (one : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (code (model := model) one).Path :=
  let cleared := BitWord.instructionStep (execution := model) (clearOp one) store
  let incremented := BitWord.instructionStep (execution := model) (incrementOp one) cleared.1
  (incremented.1, (cleared.2, incremented.2))

/-- The two real writes preserve the incoming complete quantum-reference matrix blocks. -/
theorem nativeQuadratic_check_one_execute (one : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (code (model := model) one).execute Reference state = state.mapClassical (fun entry =>
      ((step (model := model) one entry.1).1,
        (entry.2.1, (entry.2.2, (step (model := model) one entry.1).2)))) := by
  simp only [code, Circuit.execute_seq, BitWord.bitWord_instruction_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Both intrinsically writable native operations restore every borrowed joint state. -/
theorem nativeQuadratic_check_one_borrowedRestored
    (one : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (code (model := model) one).BorrowedRestored Reference state
      ((code (model := model) one).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (Circuit.borrowedRestored_classical _ state) (Circuit.borrowedRestored_classical _ _)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.CheckConstants
