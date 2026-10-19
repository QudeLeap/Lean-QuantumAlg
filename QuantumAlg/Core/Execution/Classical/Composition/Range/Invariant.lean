/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# Indexed invariants of actual chronological sequence records

The existing finite-sequence record feeds each actual returned store into its
next component. A predicate indexed by the number of completed slots therefore
advances from zero through every declared index. The execution equation for
this same record remains the one supplied by `execute_forRangeRecord`.
-/

namespace QuantumAlg.Circuit

open Execution

noncomputable section

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}

/-- Each indexed transition advances its invariant on the actual store and service state. -/
lemma forRangeRecord_invariant (count : Nat) (body : Fin count → Circuit model ctx ctx)
    (records : ∀ index, Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (body index).Path)
    (Invariant : Nat → Store ctx × model.HiddenState → Prop)
    (advance : ∀ index store, Invariant index.val store →
      Invariant (index.val + 1) (records index store).1)
    (store : Store ctx × model.HiddenState) (initial : Invariant 0 store) :
    Invariant count (forRangeRecord count body records store).1 := by
  induction count generalizing Invariant store with
  | zero => exact initial
  | succ count ih =>
      exact ih (fun index => body index.succ) (fun index => records index.succ)
        (fun processed current => Invariant (processed + 1) current)
        (fun index current established => advance index.succ current established)
        (records 0 store).1 (advance 0 store initial)

/-- Store-only chronological records retain invariants without exposing service state. -/
lemma forRangeStoreRecord_invariant (count : Nat)
    (body : Fin count → Circuit model ctx ctx)
    (records : ∀ index, Store ctx → Store ctx × (body index).Path)
    (Invariant : Nat → Store ctx → Prop)
    (advance : ∀ index store, Invariant index.val store →
      Invariant (index.val + 1) (records index store).1)
    (store : Store ctx) (initial : Invariant 0 store) :
    Invariant count (forRangeStoreRecord count body records store).1 := by
  induction count generalizing Invariant store with
  | zero => exact initial
  | succ count ih =>
      exact ih (fun index => body index.succ) (fun index => records index.succ)
        (fun index current => Invariant (index + 1) current)
        (fun index current established => advance index.succ current established)
        (records 0 store).1 (advance 0 store initial)

end

end QuantumAlg.Circuit
