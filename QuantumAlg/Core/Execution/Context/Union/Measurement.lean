/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Local.Framing
import all QuantumAlg.Core.Execution.Context.Union.Store.Laws

/-!
# Actual finite measurement writes in a resident frame

The compiled measurement designates the original physical wire and writable
cell. Its finite outcome is transported only across the proved equality of
that wire's dimension. The actual write preserves the entire other store,
including arbitrary earlier measurement results
[dW19, qcnotes.tex:5409,5420].
-/

namespace QuantumAlg.Execution

private theorem write_finite_transport {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (store : Store ctx) {first second : ℕ+} (equal : first = second)
    (output : CWriteRef ctx (.finite first)) (value : Fin first) :
    store.write
        (Eq.mp (congrArg (fun dimension : ℕ+ => CWriteRef ctx (.finite dimension)) equal)
          output)
        (.finite (Fin.cast (congrArg (fun dimension : ℕ+ => (dimension : Nat)) equal)
          value)) = store.write output (.finite value) := by
  cases equal
  rfl

namespace ContextUnion

variable {left right : RuntimeCtx .quantum}
  (separate : RuntimeCtx.StorageDisjoint left right)

/-- The real framed measurement write updates only the original measured-result cell. -/
theorem contextUnion_measurementLeft_write (first : Store left) (second : Store right)
    (wire : Fin left.systemCount)
    (output : CWriteRef left (.finite (left.quantumLayout.wire wire).dimension))
    (outcome : Fin (left.quantumLayout.wire wire).dimension) :
    (join separate first second).write (measurementLeft separate wire output)
        (.finite (Fin.cast (congrArg (fun dimension : ℕ+ => (dimension : Nat))
          (contextUnion_left_dimension left right separate wire).symm) outcome)) =
      join separate (first.write output (.finite outcome)) second := by
  exact (write_finite_transport (join separate first second)
    (contextUnion_left_dimension left right separate wire).symm
    (writeLeft separate output) outcome).trans
      (contextUnion_write_join_left separate first second output (.finite outcome))

/-- The numerical Z readout is exactly the original finite value, on the same real wire. -/
theorem contextUnion_measurementLeft_read
    (basis : (left.disjointUnion right separate).register.Index)
    (wire : Fin left.systemCount) :
    Fin.cast (congrArg (fun dimension : ℕ+ => (dimension : Nat))
      (contextUnion_left_dimension left right separate wire).symm)
        ((unionBasisEquiv left right separate basis).1 wire) =
      basis (leftPosition left right separate wire) := by
  apply Fin.ext
  exact (contextUnion_split_left_value left right separate basis wire).symm

end ContextUnion

end QuantumAlg.Execution
