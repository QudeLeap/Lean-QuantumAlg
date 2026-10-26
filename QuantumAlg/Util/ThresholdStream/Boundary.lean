/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.ThresholdStream

/-!
# A selected boundary action inside an ordered moving-flag traversal

The current prefix action precedes one boundary action and the flag
toggle. After that boundary no later prefix action executes. The
equation retains the exact source order and the full original data.
-/

namespace QuantumAlg.ThresholdStream.Boundary

/-- The last active prefix action is followed by the actual selected boundary action. -/
def forwardStep {Data : Type*} (action boundary : Nat → Data → Data)
    (enabled : Bool) (last : Nat) (state : Data × Bool) (index : Nat) : Data × Bool :=
  let next := if state.2 then action index state.1 else state.1
  (if enabled && decide (index = last) then boundary index next else next,
    state.2 ^^ (enabled && decide (index = last)))

/-- Every intermediate state retains exactly the original active prefix and one boundary action. -/
lemma forward_count {Data : Type*} (action boundary : Nat → Data → Data) (enabled : Bool)
    (last count : Nat) (state : Data) :
    (List.range count).foldl (forwardStep action boundary enabled last) (state, enabled) =
      (if enabled then
        if count ≤ last then ThresholdStream.word action count state
        else boundary last (ThresholdStream.word action (last + 1) state)
      else state, enabled && decide (count ≤ last)) := by
  induction count with
  | zero => simp [ThresholdStream.word]
  | succ count ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, ih]
      cases enabled with
      | false => simp [forwardStep]
      | true =>
          simp only [forwardStep, Bool.true_and, if_true]
          apply Prod.ext
          · by_cases below : count < last
            · have current : count ≤ last := by omega
              have next : count + 1 ≤ last := by omega
              simp [current, next, Nat.ne_of_lt below, ThresholdStream.word_succ]
            · by_cases same : count = last
              · subst count
                simp [ThresholdStream.word_succ]
              · have current : ¬count ≤ last := by omega
                have next : ¬count + 1 ≤ last := by omega
                simp [current, next, same]
          · exact ThresholdStream.boundary_xor count last

/-- A finite in-range boundary executes once after the final prefix action and clears the flag. -/
lemma forward_complete {Data : Type*} (action boundary : Nat → Data → Data) (enabled : Bool)
    (last count : Nat) (state : Data) (within : last < count) :
    (List.range count).foldl (forwardStep action boundary enabled last) (state, enabled) =
      (if enabled then boundary last (ThresholdStream.word action (last + 1) state)
        else state, false) := by
  rw [forward_count]
  have ended : ¬count ≤ last := by omega
  simp only [if_neg ended, decide_eq_false ended, Bool.and_false]

end QuantumAlg.ThresholdStream.Boundary
