/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Initialization

/-!
# Full execution of the initialized square-root body

The actual widening, literal loader, finite round schedule and final copy
compose on the same complete quantum-reference state. The store equation
records every path from the existing instructions. Its final read is the
exact square root after the real scratch allocations, even when the caller
reads and writes the same original cell.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The store and real nested path produced by the four actual body stages. -/
def bodyStep (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store (context ctx width)) :
    Store (context ctx width) × (body (model := model) input output).Path :=
  let saved := BitWord.instructionStep (execution := model) (widenOp input) store
  let loaded := ConstantWord.foldStep (model := model) (halfCell ctx width)
    (List.ofFn (ConstantWord.constantBits width (initialHalf width))) saved.1
  let iterated := iteratedRoundStep (model := model) (.storage (wideCell ctx width).toCStorageRef)
    (roundRefs ctx width) width loaded.1
  let finished := BitWord.instructionStep (execution := model) (finishOp output) iterated.1
  (finished.1, (saved.2, (loaded.2, (iterated.2, finished.2))))

/-- Every actual stage retains the complete incoming reference, history and service state. -/
theorem nativeSqrt_body_execute (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (context ctx width) Reference (model.HiddenState × History)) :
    (body (model := model) input output).execute Reference state = state.mapClassical (fun entry =>
      let actual := bodyStep (model := model) input output entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [body, bodyStep, rounds, ConstantWord.circuit, Circuit.execute_seq,
    BitWord.bitWord_instruction_execute, ConstantWord.constantWord_fold_execute,
    nativeSqrt_iteration_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The final real copy returns exactly the square root after actual scope initialization. -/
theorem nativeSqrt_body_read_output (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((bodyStep (model := model) input output (pushStore width store)).1.read
      (.storage (underWrite output width).toCStorageRef)).toNat =
      Nat.sqrt (store.read input).toNat := by
  let final := iteratedRoundStep (model := model) (.storage (wideCell ctx width).toCStorageRef)
    (roundRefs ctx width) width (initializeStore (model := model) input (pushStore width store))
  have copied : (final.1.applyOp (finishOp output)).read
      (.storage (underWrite output width).toCStorageRef) =
      final.1.read (.storage (rootCell ctx width).toCStorageRef) :=
    Store.read_applyOp_output final.1 (finishOp output)
  exact (congrArg CShape.Value.toNat copied).trans
    (nativeSqrt_initialized_iteration_root (model := model) input store)

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt
