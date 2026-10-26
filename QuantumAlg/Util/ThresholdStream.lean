/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.List.Range
import Mathlib.Data.List.MinMax

/-!
# Ordered prefix actions with one moving Boolean flag

A forward visit performs its indexed action while the flag is active,
then toggles at the unique last selected index. The complete fold is
exactly the original ordered prefix and clears the flag at that boundary.
-/

namespace QuantumAlg.ThresholdStream

/-- Original source actions in their unchanged increasing index order. -/
def word {Data : Type*} (action : Nat → Data → Data) (count : Nat) (state : Data) : Data :=
  (List.range count).foldl (fun value index => action index value) state

/-- The current action precedes the boundary toggle. -/
def forwardStep {Data : Type*} (action : Nat → Data → Data) (enabled : Bool) (last : Nat)
    (state : Data × Bool) (index : Nat) : Data × Bool :=
  (if state.2 then action index state.1 else state.1,
    state.2 ^^ (enabled && decide (index = last)))

private lemma word_succ {Data : Type*} (action : Nat → Data → Data)
    (count : Nat) (state : Data) :
    word action (count + 1) state = action count (word action count state) := by
  simp only [word, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

private lemma boundary_xor (count last : Nat) :
    (decide (count ≤ last) ^^ decide (count = last)) = decide (count + 1 ≤ last) := by
  by_cases below : count < last
  · have current : count ≤ last := by omega
    have next : count + 1 ≤ last := by omega
    simp [current, next, Nat.ne_of_lt below]
  · by_cases same : count = last
    · subst count
      simp
    · have current : ¬count ≤ last := by omega
      have next : ¬count + 1 ≤ last := by omega
      simp [current, next, same]

/-- Every intermediate flag and payload is determined by the original threshold and order. -/
lemma forward_count {Data : Type*} (action : Nat → Data → Data) (enabled : Bool)
    (last count : Nat) (state : Data) :
    (List.range count).foldl (forwardStep action enabled last) (state, enabled) =
      (if enabled then word action (min count (last + 1)) state else state,
        enabled && decide (count ≤ last)) := by
  induction count with
  | zero => simp [word]
  | succ count ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, ih]
      cases enabled
      · simp [forwardStep]
      · simp only [forwardStep, Bool.true_and, if_true]
        apply Prod.ext
        · change (if decide (count ≤ last) then
            action count (word action (min count (last + 1)) state)
            else word action (min count (last + 1)) state) =
              word action (min (count + 1) (last + 1)) state
          by_cases current : count ≤ last
          · have before : min count (last + 1) = count := Nat.min_eq_left (by omega)
            simp [current, before, word_succ]
          · have before : min count (last + 1) = last + 1 := Nat.min_eq_right (by omega)
            have after : min (count + 1) (last + 1) = last + 1 :=
              Nat.min_eq_right (by omega)
            simp [current, before, after]
        · exact boundary_xor count last

/-- A finite in-range boundary returns the flag to zero and retains exactly the selected prefix. -/
lemma forward_complete {Data : Type*} (action : Nat → Data → Data) (enabled : Bool)
    (last count : Nat) (state : Data) (within : last < count) :
    (List.range count).foldl (forwardStep action enabled last) (state, enabled) =
      (if enabled then word action (last + 1) state else state, false) := by
  rw [forward_count]
  have full : min count (last + 1) = last + 1 := Nat.min_eq_right (by omega)
  have ended : ¬count ≤ last := by omega
  simp [full, ended]

end QuantumAlg.ThresholdStream
