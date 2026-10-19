/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Layout.Store
import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Iteration
import all QuantumAlg.Components.Classical.ConstantWord.Semantics

/-!
# Establishing square-root invariants from actual fresh storage

The original word is read beneath the real six workspace heads, widened
without truncation, and saved before the result can be written. The actual
constant loader sets the increment and preserves the root's allocation
zero. These facts establish the complete iteration invariant for every
original store, including the empty word and aliased caller operands.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The first compilation-time increment fits its real target word at every width. -/
lemma nativeSqrt_initialHalf_lt (width : Nat) : initialHalf width < 2 ^ width := by
  cases width with
  | zero => decide
  | succ width =>
      rw [nativeSqrt_initialHalf_succ, Nat.pow_succ]
      have positive := Nat.two_pow_pos width
      omega

/-- The actual widening operation preserves the complete original unsigned value. -/
lemma nativeSqrt_widen_read (input : CInputRef ctx (.unsignedWord width))
    (store : Store (context ctx width)) :
    ((store.applyOp (widenOp input)).read (.storage (wideCell ctx width).toCStorageRef)).toNat =
      (store.read (underRead input width)).toNat := by
  have value := congrArg CShape.Value.toNat (Store.read_applyOp_output store (widenOp input))
  change ((store.applyOp (widenOp input)).read
    (.storage (wideCell ctx width).toCStorageRef)).toNat =
      (store.read (underRead input width)).toNat % 2 ^ (width + width) at value
  refine value.trans (Nat.mod_eq_of_lt ?_)
  exact (store.read (underRead input width)).toNat_lt.trans_le
    (Nat.pow_le_pow_right (by decide) (Nat.le_add_right width width))

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Actual store after widening and the existing literal constant-word loader. -/
noncomputable def initializeStore (input : CInputRef ctx (.unsignedWord width))
    (store : Store (context ctx width)) : Store (context ctx width) :=
  (ConstantWord.foldStep (model := model) (halfCell ctx width)
    (List.ofFn (ConstantWord.constantBits width (initialHalf width)))
    (store.applyOp (widenOp input))).1

/-- The saved input, real zero root and literal increment establish every internal invariant. -/
lemma nativeSqrt_initial_invariant (input : CInputRef ctx (.unsignedWord width))
    (store : Store ctx) :
    LoopInvariant (.storage (wideCell ctx width).toCStorageRef) (roundRefs ctx width)
      (store.read input).toNat width (initializeStore (model := model) input (pushStore width
        store)) := by
  let pushed := pushStore width store
  let saved := pushed.applyOp (widenOp input)
  let rootRead : CInputRef (context ctx width) (.unsignedWord width) :=
    .storage (rootCell ctx width).toCStorageRef
  let wideRead : CInputRef (context ctx width) (.unsignedWord (width + width)) :=
    .storage (wideCell ctx width).toCStorageRef
  have separated := nativeSqrt_round_separated ctx width
  have halfWide : (halfCell ctx width).key ∉ wideRead.storageKeys :=
    separated.inputFree _ (by simp [writeKeys, roundRefs])
  have rootWide : (rootCell ctx width).key ≠ (wideCell ctx width).key := by
    have free := separated.inputFree (rootCell ctx width).key
      (by simp [writeKeys, roundRefs])
    simpa only [CInputRef.storageKeys, List.mem_singleton] using free
  have halfRoot : (halfCell ctx width).key ∉ rootRead.storageKeys := by
    change (halfCell ctx width).key ∉ [(rootCell ctx width).key]
    exact fun present => separated.rootHalf.symm (List.mem_singleton.mp present)
  have wideRoot : (widenOp input).outputRef.key ∉ rootRead.storageKeys := by
    change (wideCell ctx width).key ∉ [(rootCell ctx width).key]
    exact fun present => rootWide.symm (List.mem_singleton.mp present)
  have inputValue : (initializeStore (model := model) input pushed).read wideRead = saved.read
    wideRead :=
    ConstantWord.constantWord_fold_read_other (model := model) (halfCell ctx width)
      (List.ofFn (ConstantWord.constantBits width (initialHalf width))) wideRead halfWide saved
  have savedValue : (saved.read wideRead).toNat = (store.read input).toNat :=
    (nativeSqrt_widen_read input pushed).trans
      (congrArg CShape.Value.toNat (nativeSqrt_push_read input width store))
  have rootValue : ((initializeStore (model := model) input pushed).read rootRead).toNat = 0 :=
    (congrArg CShape.Value.toNat
      ((ConstantWord.constantWord_fold_read_other (model := model) (halfCell ctx width)
        (List.ofFn (ConstantWord.constantBits width (initialHalf width)))
        rootRead halfRoot saved).trans
        (Store.read_applyOp_of_not_mem_storageKeys pushed (widenOp input) rootRead wideRoot))).trans
      (nativeSqrt_push_root_zero width store)
  have halfValue : ((initializeStore (model := model) input pushed).read
      (.storage (halfCell ctx width).toCStorageRef)).toNat = initialHalf width :=
    (ConstantWord.constantWord_read (model := model) (halfCell ctx width) (initialHalf width)
      saved).trans
      (Nat.mod_eq_of_lt (nativeSqrt_initialHalf_lt width))
  refine ⟨(congrArg CShape.Value.toNat inputValue).trans savedValue, ?_, ?_, halfValue⟩
  · change Nat.BinarySqrt.Interval (store.read input).toNat width
      ((initializeStore (model := model) input pushed).read rootRead).toNat
    rw [rootValue]
    exact Nat.BinarySqrt.initial_interval (store.read input).toNat_lt
  · change ((initializeStore (model := model) input pushed).read rootRead).toNat +
      2 ^ width ≤ 2 ^ width
    rw [rootValue, Nat.zero_add]

/-- Real allocation and initialization followed by the real rounds produce the exact root. -/
lemma nativeSqrt_initialized_iteration_root
    (input : CInputRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((iteratedRoundStep (model := model) (.storage (wideCell ctx width).toCStorageRef) (roundRefs
      ctx width)
      width (initializeStore (model := model) input (pushStore width store))).1.read
      (.storage (rootCell ctx width).toCStorageRef)).toNat = Nat.sqrt (store.read input).toNat :=
  nativeSqrt_iteration_root _ _ (nativeSqrt_round_separated ctx width) _ _ _
    (nativeSqrt_initial_invariant (model := model) input store)

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt
