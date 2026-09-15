/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.SignedWord
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Actual comparison with a doubled unsigned word

A native left shift, unsigned comparison and Boolean complement decide whether
the left input is at most twice the right input. The raw trace uses modular
word arithmetic; explicit capacity bounds recover the original integer test.
-/

namespace QuantumAlg.ClassicalRoutines.Comparison.Doubled

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Caller-owned inputs, doubled-word scratch and actual comparison output. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  left : CInputRef ctx (.unsignedWord width)
  right : CInputRef ctx (.unsignedWord width)
  doubled : CWriteRef ctx (.unsignedWord width)
  passes : CWriteRef ctx .bit

/-- Both original inputs survive, and the actual doubled word survives the decision write. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  leftAvoidsDoubled : refs.doubled.key ∉ refs.left.storageKeys
  rightAvoidsDoubled : refs.doubled.key ∉ refs.right.storageKeys
  leftAvoidsPass : refs.passes.key ∉ refs.left.storageKeys
  rightAvoidsPass : refs.passes.key ∉ refs.right.storageKeys
  doubledAvoidsPass : refs.passes.key ≠ refs.doubled.key

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual modular shift writes the doubled right input. -/
def doubleOp (refs : Refs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .shiftLeft width ctx refs.right refs.doubled

/-- The actual strict comparison reads the newly written doubled word. -/
def compareOp (refs : Refs ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit ctx ctx :=
  .wordBinary .lessThan width ctx (.product (.storage refs.doubled.toCStorageRef) refs.left)
    refs.passes

/-- The actual complement turns the strict test into the required non-strict inequality. -/
def complementOp (refs : Refs ctx width) : ClassicalOp .bit .bit ctx ctx :=
  .bit .not ctx (.storage refs.passes.toCStorageRef) refs.passes

/-- Execute the three native operations in their data-dependent order. -/
def compareInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (.classical (doubleOp refs))
    (.seq (.classical (compareOp refs)) (.classical (complementOp refs)))

/-- The actual three-write store, including the compared value and the complemented result. -/
def comparedStore (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  ((store.applyOp (doubleOp refs)).applyOp (compareOp refs)).applyOp (complementOp refs)

/-- Full actual execution preserves history and quantum-reference blocks. -/
theorem compareInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (compareInto refs).execute Reference state = state.mapClassical (fun entry =>
      (comparedStore refs entry.1, (entry.2, ((), ((), ()))))) := by
  simp only [compareInto, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Reads outside the two actual writable cells are unchanged by the comparison. -/
theorem compareInto_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (doubled : refs.doubled.key ∉ other.storageKeys)
    (passes : refs.passes.key ∉ other.storageKeys) :
    (comparedStore refs store).read other = store.read other := by
  unfold comparedStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (complementOp refs) other passes,
    Store.read_applyOp_of_not_mem_storageKeys _ (compareOp refs) other passes,
    Store.read_applyOp_of_not_mem_storageKeys _ (doubleOp refs) other doubled]

end

end QuantumAlg.ClassicalRoutines.Comparison.Doubled
