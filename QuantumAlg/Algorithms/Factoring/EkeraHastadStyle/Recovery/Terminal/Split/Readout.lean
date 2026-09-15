/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Terminal.Split

/-!
# The actual two terminal words equal the original source sample

The low resize reads the decoded word before any shifts. Each actual right
shift then changes only that temporary word, and the final high resize
preserves the earlier low result. Scope release exposes both original
destinations. Their sole positional distinction is discharged by the actual
sample layout; neither destination needs an initial value.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.TerminalSplit

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {m ell : Nat}

private theorem fresh_free {shape : CShape} (input : CInputRef ctx shape) (m ell : Nat) :
    ctx.canonicalFreshKey ∉ (underRead input m ell).storageKeys := by
  have support := CInputRef.storageKeys_underWorkspace input ctx.canonicalFreshKey
    (.unsignedWord ((ell + m) + ell)) ctx.canonicalFreshKey_fresh
  exact fun present => ctx.canonicalFreshKey_fresh
    (input.storageKeys_subset_context (support ▸ present))

private theorem original_ne_fresh {shape : CShape} (output : CWriteRef ctx shape) :
    output.key ≠ ctx.canonicalFreshKey := by
  intro same
  have present := (CInputRef.storage output.toCStorageRef).storageKeys_subset_context
    (List.mem_singleton.mpr rfl)
  exact ctx.canonicalFreshKey_fresh (same ▸ present)

/-- The actual low extraction does not alter the full word subsequently reused by the shifts. -/
theorem nativeRecovery_terminal_low_full (refs : Refs ctx m ell)
    (store : Store (context ctx m ell)) :
    (store.applyOp (lowOp refs)).read (.storage (full ctx m ell).toCStorageRef) =
      store.read (.storage (full ctx m ell).toCStorageRef) :=
  Store.read_applyOp_of_not_mem_storageKeys store (lowOp refs)
    (.storage (full ctx m ell).toCStorageRef)
    (fun present => original_ne_fresh refs.k (List.mem_singleton.mp present))

/-- Real decoding, low extraction, shifts and high extraction store the exact source pair. -/
theorem nativeRecovery_terminal_split_read
    (input : CInputRef ctx (.bits ((ell + m) + ell))) (refs : Refs ctx m ell)
    (separate : refs.j.key ≠ refs.k.key) (store : Store ctx) :
    let sample := BatchRecovery.decodeTerminalSample m ell (terminalValue (store.read input))
    (((step input refs store).1.read (.storage refs.j.toCStorageRef)).toNat,
      ((step input refs store).1.read (.storage refs.k.toCStorageRef)).toNat) =
        (sample.1.val, sample.2.val) := by
  let entered : Store (context ctx m ell) := store.pushWorkspace ctx.canonicalFreshKey
    (.unsignedWord ((ell + m) + ell)) ctx.canonicalFreshKey_fresh
  let decoded : Store (context ctx m ell) :=
    (terminalStep (underRead input m ell) (full ctx m ell) entered).1
  let low : Store (context ctx m ell) := decoded.applyOp (lowOp refs)
  let shifted : Store (context ctx m ell) := TerminalShift.storeStep ell (full ctx m ell) low
  let sample := BatchRecovery.decodeTerminalSample m ell (terminalValue (store.read input))
  have inputRead : entered.read (underRead input m ell) = store.read input :=
    Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey
      (.unsignedWord ((ell + m) + ell)) ctx.canonicalFreshKey_fresh input
  have first : (decoded.read (.storage (full ctx m ell).toCStorageRef)).toNat / 2 ^ ell =
      sample.1.val :=
    (nativeRecovery_terminal_first (underRead input m ell) (full ctx m ell) entered
      (fresh_free input m ell)).trans
      (congrArg (fun value : CShape.Value (.bits ((ell + m) + ell)) =>
        (BatchRecovery.decodeTerminalSample m ell (terminalValue value)).1.val) inputRead)
  have second : (decoded.read (.storage (full ctx m ell).toCStorageRef)).toNat % 2 ^ ell =
      sample.2.val :=
    (nativeRecovery_terminal_second (underRead input m ell) (full ctx m ell) entered
      (fresh_free input m ell)).trans
      (congrArg (fun value : CShape.Value (.bits ((ell + m) + ell)) =>
        (BatchRecovery.decodeTerminalSample m ell (terminalValue value)).2.val) inputRead)
  have lowRead : (low.read (underRead (.storage refs.k.toCStorageRef) m ell)).toNat =
      sample.2.val :=
    (congrArg CShape.Value.toNat (Store.read_applyOp_output decoded (lowOp refs))).trans second
  have shiftedRead : (shifted.read (.storage (full ctx m ell).toCStorageRef)).toNat =
      sample.1.val :=
    (TerminalShift.nativeRecovery_terminal_shifts_read ell (full ctx m ell) low).trans
      ((congrArg (fun value : CShape.Value (.unsignedWord ((ell + m) + ell)) =>
        value.toNat / 2 ^ ell) (nativeRecovery_terminal_low_full refs decoded)).trans first)
  have highRead : ((shifted.applyOp (highOp refs)).read
      (underRead (.storage refs.j.toCStorageRef) m ell)).toNat = sample.1.val :=
    (congrArg CShape.Value.toNat (Store.read_applyOp_output shifted (highOp refs))).trans
      ((congrArg (fun value : Nat => value % 2 ^ (ell + m)) shiftedRead).trans
        (Nat.mod_eq_of_lt sample.1.isLt))
  have keptLow : ((shifted.applyOp (highOp refs)).read
      (underRead (.storage refs.k.toCStorageRef) m ell)).toNat = sample.2.val :=
    (congrArg CShape.Value.toNat
      (Store.read_applyOp_of_not_mem_storageKeys shifted (highOp refs)
        (underRead (.storage refs.k.toCStorageRef) m ell)
        (fun present => separate (List.mem_singleton.mp present)))).trans
      ((congrArg CShape.Value.toNat
        (TerminalShift.nativeRecovery_terminal_shifts_read_other ell (full ctx m ell)
          (underRead (.storage refs.k.toCStorageRef) m ell)
          (fresh_free (.storage refs.k.toCStorageRef) m ell) low)).trans lowRead)
  have highExit := congrArg CShape.Value.toNat
    (Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey
      (.unsignedWord ((ell + m) + ell)) ctx.canonicalFreshKey_fresh
      (shifted.applyOp (highOp refs)) (.storage refs.j.toCStorageRef))
  have lowExit := congrArg CShape.Value.toNat
    (Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey
      (.unsignedWord ((ell + m) + ell)) ctx.canonicalFreshKey_fresh
      (shifted.applyOp (highOp refs)) (.storage refs.k.toCStorageRef))
  exact congrArg₂ Prod.mk (highExit.trans highRead) (lowExit.trans keptLow)

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.TerminalSplit
