/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.List.Threshold
import Mathlib.Data.List.Basic

/-! # Exact finite indexed words after suppressing an initial interval -/

namespace QuantumAlg.ListThreshold

/-- Bounded source words keep the original increasing order after a static lower mask. -/
lemma flatMap_bounded_range_mask {Data : Type*} (count start : Nat)
    (action : Fin count → List Data) :
    (List.range count).flatMap (fun index =>
      if within : index < count then
        if start ≤ index then action ⟨index, within⟩ else []
      else []) =
      (List.ofFn (fun index : Fin (count - start) =>
        action ⟨index.val + start, by have := index.isLt; omega⟩)).flatten := by
  let total (index : Nat) := if within : index < count then action ⟨index, within⟩ else []
  have masked : (List.range count).flatMap (fun index =>
      if within : index < count then
        if start ≤ index then action ⟨index, within⟩ else []
      else []) =
      (List.range count).flatMap (fun index => if start ≤ index then total index else []) := by
    apply List.flatMap_congr
    intro index member
    have within := List.mem_range.mp member
    simp only [dif_pos within, total]
  rw [masked, flatMap_range_mask, flatMap_range_eq_flatten_ofFn]
  apply congrArg List.flatten
  apply congrArg (fun entries : Fin (count - start) → List Data => List.ofFn entries)
  funext index
  have within : index.val + start < count := by have := index.isLt; omega
  simp only [total, dif_pos within]

/-- Flattening singleton finite words retains exactly the original indexed list. -/
lemma flatten_ofFn_singleton {Data : Type*} {count : Nat} (action : Fin count → Data) :
    (List.ofFn (fun index => [action index])).flatten = List.ofFn action := by
  have singletons (entries : List Data) :
      (entries.map (fun entry => [entry])).flatten = entries := by
    induction entries with
    | nil => rfl
    | cons first rest ih => simp only [List.map_cons, List.flatten_cons, ih, List.singleton_append]
  calc
    _ = ((List.ofFn action).map (fun entry : Data => [entry])).flatten := by
      rw [List.map_ofFn]
      rfl
    _ = List.ofFn action := singletons _

end QuantumAlg.ListThreshold
