/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.List.Range
import Mathlib.Data.List.MinMax

/-! # Exact increasing indices retained by a finite threshold -/

namespace QuantumAlg.ThresholdStream

/-- Filtering a fixed index range retains exactly its original initial segment. -/
lemma filter_range_below (count limit : Nat) :
    (List.range count).filter (fun index => decide (index < limit)) =
      List.range (min count limit) := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [List.range_succ, List.filter_append, ih]
      by_cases inside : count < limit
      · have before : min count limit = count := Nat.min_eq_left (by omega)
        have after : min (count + 1) limit = count + 1 := Nat.min_eq_left (by omega)
        simp [inside, before, after, List.range_succ]
      · have before : min count limit = limit := Nat.min_eq_right (by omega)
        have after : min (count + 1) limit = limit := Nat.min_eq_right (by omega)
        simp [inside, before, after]

end QuantumAlg.ThresholdStream
