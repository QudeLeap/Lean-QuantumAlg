/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Range

/-! # Exact ordered finite words behind a statically masked index traversal -/

namespace QuantumAlg.ListThreshold

/-- Suppressing a fixed initial index interval retains the exact shifted source word. -/
lemma flatMap_range_mask {Data : Type*} (action : Nat → List Data) (start count : Nat) :
    (List.range count).flatMap (fun index => if start ≤ index then action index else []) =
      (List.range (count - start)).flatMap (fun index => action (index + start)) := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [List.range_succ, List.flatMap_append, ih]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      by_cases active : start ≤ count
      · have next : count + 1 - start = (count - start) + 1 := by omega
        rw [if_pos active, next, List.range_succ, List.flatMap_append]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        rw [Nat.sub_add_cancel active]
      · have before : count - start = 0 := by omega
        have after : count + 1 - start = 0 := by omega
        simp [active, before, after]

/-- Flattening finite indexed source words is the same original increasing-index traversal. -/
lemma flatMap_range_eq_flatten_ofFn {Data : Type*} (action : Nat → List Data) (count : Nat) :
    (List.range count).flatMap action =
      (List.ofFn (fun index : Fin count => action index.val)).flatten := by
  have flatten (indices : List Nat) : indices.flatMap action = (indices.map action).flatten := by
    induction indices with
    | nil => rfl
    | cons first rest ih => simp only [List.flatMap_cons, List.map_cons, List.flatten_cons, ih]
  have entries : (List.range count).map action =
      List.ofFn (fun index : Fin count => action index.val) := by
    apply List.ext_getElem
    · simp
    · intro index _left _right
      simp
  rw [flatten, entries]

end QuantumAlg.ListThreshold
