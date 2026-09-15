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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The store and real nested path produced by the four actual body stages. -/
def bodyStep (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store (context ctx width)) :
    Store (context ctx width) × (body input output).Path :=
  let saved := store.applyOp (widenOp input)
  let loaded := ConstantWord.foldStep (halfCell ctx width)
    (List.ofFn (ConstantWord.constantBits width (initialHalf width))) saved
  let iterated := iteratedRoundStep (.storage (wideCell ctx width).toCStorageRef)
    (roundRefs ctx width) width loaded.1
  (iterated.1.applyOp (finishOp output), ((), (loaded.2, (iterated.2, ()))))

private def classicalStep {current : RuntimeCtx kind} {source target : CShape}
    (op : ClassicalOp source target current current) (store : Store current) :
    Store current × (Circuit.classical op).Path := (store.applyOp op, ())

private theorem classical_equation {current : RuntimeCtx kind} {source target : CShape}
    (op : ClassicalOp source target current current) (Reference : Register)
    {History : Type} [Fintype History] (state : State current Reference History) :
    (Circuit.classical op).execute Reference state = state.mapClassical (fun entry =>
      ((classicalStep op entry.1).1, (entry.2, (classicalStep op entry.1).2))) := by
  refine (Circuit.execute_classical_mapClassical op Reference state).trans ?_
  let update : Store current × History → Store current × (History × Unit) :=
    fun entry => (entry.1.applyOp op, (entry.2, ()))
  exact congrArg
    (fun decision : DecidableEq (Store current × (History × Unit)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod current.register Reference)
        decision state update) (Subsingleton.elim _ _)

/-- Every actual stage composes while preserving complete incoming quantum-reference blocks. -/
theorem nativeSqrt_body_execute (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State (context ctx width) Reference History) :
    (body input output).execute Reference state = state.mapClassical (fun entry =>
      ((bodyStep input output entry.1).1, (entry.2, (bodyStep input output entry.1).2))) := by
  let loader := ConstantWord.circuit (halfCell ctx width) (initialHalf width)
  let load := ConstantWord.foldStep (halfCell ctx width)
    (List.ofFn (ConstantWord.constantBits width (initialHalf width)))
  let loop := rounds ctx width
  let loopStep := iteratedRoundStep (.storage (wideCell ctx width).toCStorageRef)
    (roundRefs ctx width) width
  let tail := Circuit.seq loop (.classical (finishOp output))
  let tailStep : Store (context ctx width) → Store (context ctx width) × tail.Path :=
    fun current =>
    ((loopStep current).1.applyOp (finishOp output), ((loopStep current).2, ()))
  have tailEquation : ∀ (reference : Register) {Past : Type} [Fintype Past]
      (initial : State (context ctx width) reference Past),
      tail.execute reference initial = initial.mapClassical (fun entry =>
        ((tailStep entry.1).1, (entry.2, (tailStep entry.1).2))) := by
    intro reference Past pastFinite initial
    refine (Circuit.execute_seq_mapClassical loop (.classical (finishOp output)) loopStep
      (classicalStep (finishOp output))
      (nativeSqrt_iteration_execute _ _ width) (classical_equation (finishOp output))
      reference initial).trans ?_
    exact congrArg
      (fun decision : DecidableEq (Store (context ctx width) × (Past × tail.Path)) =>
        @ExecutionState.mapClassical _ _ _ _
          (Register.prod (context ctx width).register reference) decision initial
          (fun entry => ((tailStep entry.1).1, (entry.2, (tailStep entry.1).2))))
      (Subsingleton.elim _ _)
  let middle := Circuit.seq loader tail
  let middleStep : Store (context ctx width) → Store (context ctx width) × middle.Path :=
    fun current =>
    ((tailStep (load current).1).1, ((load current).2, (tailStep (load current).1).2))
  have middleEquation : ∀ (reference : Register) {Past : Type} [Fintype Past]
      (initial : State (context ctx width) reference Past),
      middle.execute reference initial = initial.mapClassical (fun entry =>
        ((middleStep entry.1).1, (entry.2, (middleStep entry.1).2))) := by
    intro reference Past pastFinite initial
    refine (Circuit.execute_seq_mapClassical loader tail load tailStep
      (ConstantWord.constantWord_fold_execute _ _) tailEquation reference initial).trans ?_
    exact congrArg
      (fun decision : DecidableEq (Store (context ctx width) × (Past × middle.Path)) =>
        @ExecutionState.mapClassical _ _ _ _
          (Register.prod (context ctx width).register reference) decision initial
          (fun entry => ((middleStep entry.1).1, (entry.2, (middleStep entry.1).2))))
      (Subsingleton.elim _ _)
  refine (Circuit.execute_seq_mapClassical (.classical (widenOp input)) middle
    (classicalStep (widenOp input)) middleStep
    (classical_equation (widenOp input)) middleEquation Reference state).trans ?_
  let update : Store (context ctx width) × History →
      Store (context ctx width) × (History × (body input output).Path) :=
    fun entry => ((bodyStep input output entry.1).1,
      (entry.2, (bodyStep input output entry.1).2))
  exact congrArg
    (fun decision : DecidableEq (Store (context ctx width) ×
        (History × (body input output).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod (context ctx width).register Reference)
        decision state update) (Subsingleton.elim _ _)

/-- The final real copy returns exactly the square root after actual scope initialization. -/
theorem nativeSqrt_body_read_output (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((bodyStep input output (pushStore width store)).1.read
      (.storage (underWrite output width).toCStorageRef)).toNat =
      Nat.sqrt (store.read input).toNat := by
  let final := iteratedRoundStep (.storage (wideCell ctx width).toCStorageRef)
    (roundRefs ctx width) width (initializeStore input (pushStore width store))
  have copied : (final.1.applyOp (finishOp output)).read
      (.storage (underWrite output width).toCStorageRef) =
      final.1.read (.storage (rootCell ctx width).toCStorageRef) :=
    Store.read_applyOp_output final.1 (finishOp output)
  exact (congrArg CShape.Value.toNat copied).trans
    (nativeSqrt_initialized_iteration_root input store)

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt
