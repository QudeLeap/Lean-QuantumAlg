/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Union.Measurement

/-!
# Full store coordinates after a framed Z write

Splitting the actual postmeasurement store retains the complete other store.
Only the original writable measurement-result cell changes; the finite cast
expresses the equality of the actual wire dimensions
[dW19, qcnotes.tex:5409,5420].
-/

namespace QuantumAlg.Execution.ContextUnion

variable {left right : RuntimeCtx .quantum}
  (separate : RuntimeCtx.StorageDisjoint left right)

/-- Splitting an actual Z write preserves the full other store, for every initial value. -/
theorem contextUnion_measurementLeft_split_write
    (store : Store (left.disjointUnion right separate)) (wire : Fin left.systemCount)
    (output : CWriteRef left (.finite (left.quantumLayout.wire wire).dimension))
    (outcome : Fin ((left.disjointUnion right separate).quantumLayout.wire
      (leftPosition left right separate wire)).dimension) :
    split separate (store.write (measurementLeft separate wire output) (.finite outcome)) =
      ((split separate store).1.write output
        (.finite (Fin.cast (congrArg (fun dimension : ℕ+ => (dimension : Nat))
          (contextUnion_left_dimension left right separate wire)) outcome)),
        (split separate store).2) := by
  let equality := congrArg (fun dimension : ℕ+ => (dimension : Nat))
    (contextUnion_left_dimension left right separate wire)
  have restored : Fin.cast equality.symm (Fin.cast equality outcome) = outcome := by
    apply Fin.ext
    rfl
  have writes := contextUnion_measurementLeft_write separate
    (split separate store).1 (split separate store).2 wire output (Fin.cast equality outcome)
  have whole := congrArg (split separate) writes
  rw [restored, join_split_store, split_join_store] at whole
  exact whole

end QuantumAlg.Execution.ContextUnion
