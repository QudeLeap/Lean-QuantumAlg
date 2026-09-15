/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Terminal.Split.Readout

/-!
# Original structural reads survive terminal splitting

Only the two actual sample destinations survive the full-index scope. Every
original read outside those destinations has exactly its incoming value,
including the retained second terminal and all previously decoded fields.
This is a law of the same decoder, extraction instructions and actual shifts.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.TerminalSplit

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {m ell : Nat}

/-- The full actual extraction preserves each original structural read outside its two outputs. -/
theorem nativeRecovery_terminal_split_read_other
    (input : CInputRef ctx (.bits ((ell + m) + ell))) (refs : Refs ctx m ell)
    {shape : CShape} (other : CInputRef ctx shape)
    (highFree : refs.j.key ∉ other.storageKeys) (lowFree : refs.k.key ∉ other.storageKeys)
    (store : Store ctx) :
    (step input refs store).1.read other = store.read other := by
  let entered : Store (context ctx m ell) := store.pushWorkspace ctx.canonicalFreshKey
    (.unsignedWord ((ell + m) + ell)) ctx.canonicalFreshKey_fresh
  let decoded : Store (context ctx m ell) :=
    (terminalStep (underRead input m ell) (full ctx m ell) entered).1
  let low : Store (context ctx m ell) := decoded.applyOp (lowOp refs)
  let shifted : Store (context ctx m ell) := TerminalShift.storeStep ell (full ctx m ell) low
  have support := CInputRef.storageKeys_underWorkspace other ctx.canonicalFreshKey
    (.unsignedWord ((ell + m) + ell)) ctx.canonicalFreshKey_fresh
  have high : (shifted.applyOp (highOp refs)).read (underRead other m ell) =
      shifted.read (underRead other m ell) :=
    Store.read_applyOp_of_not_mem_storageKeys shifted (highOp refs) (underRead other m ell)
      (fun present => highFree (support ▸ present))
  have shifts : shifted.read (underRead other m ell) = low.read (underRead other m ell) :=
    TerminalShift.nativeRecovery_terminal_shifts_read_other ell (full ctx m ell)
      (underRead other m ell) (fresh_free other m ell) low
  have lowRead : low.read (underRead other m ell) = decoded.read (underRead other m ell) :=
    Store.read_applyOp_of_not_mem_storageKeys decoded (lowOp refs) (underRead other m ell)
      (fun present => lowFree (support ▸ present))
  have decoder : decoded.read (underRead other m ell) = entered.read (underRead other m ell) :=
    TerminalDecode.terminalDecode_fold_read_other (full ctx m ell)
      (List.ofFn (fun index => CInputRef.bitsGet (underRead input m ell) index)) entered
      (underRead other m ell) (fresh_free other m ell)
  have enteredRead := Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey
    (.unsignedWord ((ell + m) + ell)) ctx.canonicalFreshKey_fresh other
  have released := Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey
    (.unsignedWord ((ell + m) + ell)) ctx.canonicalFreshKey_fresh
    (shifted.applyOp (highOp refs)) other
  exact released.trans (high.trans (shifts.trans (lowRead.trans (decoder.trans enteredRead))))

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.TerminalSplit
