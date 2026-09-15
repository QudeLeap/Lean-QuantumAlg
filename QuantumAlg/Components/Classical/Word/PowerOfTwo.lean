/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Iteration
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

/-- The prescribed number of native one-bit left shifts. -/
def shiftInto (count : Nat) (output : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .iterate count (.classical (shiftOp output))

/-- The chronological actual store after the prescribed native shifts. -/
def shiftStore (count : Nat) (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx := (fun current => current.applyOp (shiftOp output))^[count] store

/-- The actual shift store and its complete fixed-length instruction path. -/
def shiftStep (count : Nat) (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (shiftInto count output).Path := (shiftStore count output store, fun _ => ())

/-- Actual self-XOR followed by increment initializes the low-word encoding of one. -/
def seedInto (output : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (.classical (clearOp output)) (.classical (incrementOp output))

/-- The actual initialized store and both native instruction paths. -/
def seedStep (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (seedInto output).Path :=
  ((store.applyOp (clearOp output)).applyOp (incrementOp output), ((), ()))

/-- Initialize the original word and perform the actual fixed number of native shifts. -/
def into (count : Nat) (output : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (seedInto output) (shiftInto count output)

/-- The actual power-loading store and its full chronological native path. -/
def step (count : Nat) (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (into count output).Path :=
  let seeded := seedStep output store
  let shifted := shiftStep count output seeded.1
  (shifted.1, (seeded.2, shifted.2))

set_option maxHeartbeats 800000 in
-- Normalize the fixed finite iteration path and constant native instruction paths.
/-- Native repeated left shifting retains the entire quantum-reference state and history. -/
theorem shiftInto_execute (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (shiftInto count output).execute Reference state = state.mapClassical (fun entry =>
      ((shiftStep count output entry.1).1, (entry.2, (shiftStep count output entry.1).2))) := by
  refine (Circuit.execute_iterate_mapClassical (.classical (shiftOp output))
    (fun store => (store.applyOp (shiftOp output), ())) (by
      intro Reference History _ state
      refine (Circuit.execute_classical_mapClassical (shiftOp output) Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _) count Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Actual native initialization preserves every original state block. -/
theorem seedInto_execute (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (seedInto output).execute Reference state = state.mapClassical (fun entry =>
      ((seedStep output entry.1).1, (entry.2, (seedStep output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (.classical (clearOp output))
    (.classical (incrementOp output)) (fun store => (store.applyOp (clearOp output), ()))
    (fun store => (store.applyOp (incrementOp output), ())) (by
      intro Reference History _ state
      refine (Circuit.execute_classical_mapClassical (clearOp output) Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _) (by
      intro Reference History _ state
      refine (Circuit.execute_classical_mapClassical (incrementOp output) Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The complete actual constant loader preserves every original quantum-reference correlation. -/
theorem into_execute (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (into count output).execute Reference state = state.mapClassical (fun entry =>
      ((step count output entry.1).1, (entry.2, (step count output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (seedInto output) (shiftInto count output)
    (seedStep output) (shiftStep count output) (seedInto_execute output)
    (shiftInto_execute count output) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Native self-XOR writes zero independently of the incoming word, including width zero. -/
theorem clear_read (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((store.applyOp (clearOp output)).read (.storage output.toCStorageRef)).toNat = 0 := by
  simp only [Store.applyOp, clearOp, ClassicalOp.outputRef, Store.read_write_same,
    ClassicalOp.inputRef, ClassicalOp.eval_wordBinary]
  change (((store.read (.storage output.toCStorageRef)).toNat ^^^
    (store.read (.storage output.toCStorageRef)).toNat) % 2 ^ width) = 0
  rw [Nat.xor_self, Nat.zero_mod]

/-- Actual native initialization writes the exact low-word encoding of one. -/
theorem seed_read (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((seedStep output store).1.read (.storage output.toCStorageRef)).toNat =
      1 % 2 ^ width := by
  change (((store.applyOp (clearOp output)).applyOp (incrementOp output)).read
    (.storage output.toCStorageRef)).toNat = _
  simp only [Store.applyOp, incrementOp, ClassicalOp.outputRef, Store.read_write_same,
    ClassicalOp.inputRef, ClassicalOp.eval_wordUnary]
  change (((store.applyOp (clearOp output)).read (.storage output.toCStorageRef)).toNat + 1) %
    2 ^ width = _
  rw [clear_read, Nat.zero_add]

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

/-- Arbitrary initial words load precisely the low-word encoding of the prescribed power of two. -/
theorem into_read (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    ((step count output store).1.read (.storage output.toCStorageRef)).toNat =
      2 ^ count % 2 ^ width := by
  change ((shiftStore count output (seedStep output store).1).read
    (.storage output.toCStorageRef)).toNat = _
  rw [shiftInto_read, seed_read, mod_mul, Nat.one_mul]

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

/-- Initialization and every actual native shift preserve the complete nonoutput caller frame. -/
theorem into_callerFrame (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoids : output.key ∉ other.storageKeys) :
    (step count output store).1.read other = store.read other := by
  change (shiftStore count output (seedStep output store).1).read other = _
  rw [shiftInto_callerFrame _ _ _ other avoids]
  change ((store.applyOp (clearOp output)).applyOp (incrementOp output)).read other = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (incrementOp output) other avoids,
    Store.read_applyOp_of_not_mem_storageKeys _ (clearOp output) other avoids]

end

end QuantumAlg.ClassicalRoutines.Word.PowerOfTwo
