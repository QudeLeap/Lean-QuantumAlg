/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Construction
import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Round.Arithmetic
import all QuantumAlg.Core.Execution.Classical.Iteration

/-!
# Exact actual iteration of binary square-root refinement

The stored original, lower-root interval, finite-word capacity and current
increment form one internal invariant. Each real round preserves it with
one fewer remaining bit. The actual iterate instruction therefore returns
the exact natural square root, including zero rounds, while its full state
equation retains every incoming quantum-reference block and every real path.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The compilation-time increment at a nonempty width is its highest binary place. -/
theorem nativeSqrt_initialHalf_succ (remaining : Nat) :
    initialHalf (remaining + 1) = 2 ^ remaining := by
  simp [initialHalf]

/-- One actual right shift produces the next compilation-time increment, including the last bit. -/
theorem nativeSqrt_initialHalf_div (remaining : Nat) :
    2 ^ remaining / 2 = initialHalf remaining := by
  cases remaining with
  | zero => rfl
  | succ remaining =>
      rw [nativeSqrt_initialHalf_succ, Nat.pow_succ]
      omega

/-- Internal store invariant established by the routine's real scratch initialization. -/
structure LoopInvariant (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : RoundRefs ctx width) (original remaining : Nat) (store : Store ctx) : Prop where
  /-- The actual widened input still contains the original value. -/
  source : (store.read input).toNat = original
  /-- The original square root is in the exact remaining interval. -/
  interval : Nat.BinarySqrt.Interval original remaining
    (store.read (.storage refs.root.toCStorageRef)).toNat
  /-- The next midpoint and every later midpoint fit the real root word. -/
  capacity : (store.read (.storage refs.root.toCStorageRef)).toNat + 2 ^ remaining ≤ 2 ^ width
  /-- The actual increment cell contains the next binary place. -/
  half : (store.read (.storage refs.half.toCStorageRef)).toNat = initialHalf remaining

/-- One real round preserves the complete internal invariant with one fewer remaining bit. -/
theorem nativeSqrt_round_invariant
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : RoundRefs ctx width)
    (separated : Separated input refs) (original remaining : Nat) (store : Store ctx)
    (ready : LoopInvariant input refs original (remaining + 1) store) :
    LoopInvariant input refs original remaining (roundStep input refs store).1 := by
  have halfValue : (store.read (.storage refs.half.toCStorageRef)).toNat = 2 ^ remaining :=
    ready.half.trans (nativeSqrt_initialHalf_succ remaining)
  have fits : (store.read (.storage refs.root.toCStorageRef)).toNat +
      (store.read (.storage refs.half.toCStorageRef)).toNat < 2 ^ width := by
    rw [halfValue]
    exact Nat.BinarySqrt.midpoint_lt_capacity ready.capacity
  have rootValue := nativeSqrt_round_root input refs separated store fits
  rw [ready.source, halfValue] at rootValue
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (congrArg CShape.Value.toNat
      (nativeSqrt_round_input input refs separated store)).trans ready.source
  · rw [rootValue]
    exact Nat.BinarySqrt.refine_interval ready.interval
  · rw [rootValue]
    exact Nat.BinarySqrt.refine_capacity ready.capacity
  · exact (nativeSqrt_round_half input refs separated store).trans
      ((congrArg (fun value : Nat => value / 2) halfValue).trans
        (nativeSqrt_initialHalf_div remaining))

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Actual final store and finite path vector from repeating the real round. -/
def iteratedRoundStep (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : RoundRefs ctx width) (count : Nat) (store : Store ctx) :
    Store ctx × (Circuit.iterate count (round input refs)).Path :=
  let step := roundStep input refs
  ((fun current => (step current).1)^[count] store,
    fun index => (step ((fun current => (step current).1)^[index.val] store)).2)

/-- The real iteration preserves complete incoming quantum-reference blocks and actual paths. -/
theorem nativeSqrt_iteration_execute
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : RoundRefs ctx width)
    (count : Nat) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.iterate count (round input refs)).execute Reference state =
      state.mapClassical (fun entry =>
        ((iteratedRoundStep input refs count entry.1).1,
          (entry.2, (iteratedRoundStep input refs count entry.1).2))) := by
  refine (Circuit.execute_iterate_mapClassical (round input refs) (roundStep input refs)
    (nativeSqrt_round_execute input refs) count Reference state).trans ?_
  let update : Store ctx × History → Store ctx ×
      (History × (Circuit.iterate count (round input refs)).Path) :=
    fun entry => ((iteratedRoundStep input refs count entry.1).1,
      (entry.2, (iteratedRoundStep input refs count entry.1).2))
  exact congrArg
    (fun decision : DecidableEq (Store ctx ×
        (History × (Circuit.iterate count (round input refs)).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference)
        decision state update)
    (Subsingleton.elim _ _)

/-- Exhausting the actual remaining rounds leaves exactly the natural square root. -/
theorem nativeSqrt_iteration_root
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : RoundRefs ctx width)
    (separated : Separated input refs) (original remaining : Nat) (store : Store ctx)
    (ready : LoopInvariant input refs original remaining store) :
    ((iteratedRoundStep input refs remaining store).1.read
      (.storage refs.root.toCStorageRef)).toNat = Nat.sqrt original := by
  change (((fun current => (roundStep input refs current).1)^[remaining] store).read
    (.storage refs.root.toCStorageRef)).toNat = Nat.sqrt original
  induction remaining generalizing store with
  | zero => exact ready.interval.finished
  | succ remaining inductionHypothesis =>
      rw [Function.iterate_succ_apply]
      exact inductionHypothesis _
        (nativeSqrt_round_invariant input refs separated original remaining store ready)

/-- Repetition retains every original structural value outside the five actual write keys. -/
theorem nativeSqrt_iteration_read_unchanged
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : RoundRefs ctx width)
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : ∀ key ∈ writeKeys refs, key ∉ other.storageKeys)
    (count : Nat) (store : Store ctx) :
    (iteratedRoundStep input refs count store).1.read other = store.read other := by
  change (((fun current => (roundStep input refs current).1)^[count] store).read other) = _
  induction count generalizing store with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [Function.iterate_succ_apply]
      exact (inductionHypothesis _).trans
        (nativeSqrt_round_read_unchanged input refs other separate store)

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt
