/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Circuit

/-!
# A borrowed classical cell cannot receive a measurement result

The actual Z-measurement constructor requires a writable finite result cell.
The borrowed-input head is present and readable, but its role cannot be
presented as that writable result. This is a compiled ownership rejection for
every finite measurement dimension, including dimensions beyond two.
-/

namespace QuantumAlg.Execution

/-- A writable result reference cannot point to the borrowed input head. -/
public theorem borrowedInput_not_measurementOutput
    {ctx : RuntimeCtx .quantum} (key : StorageKey) (dimension : ℕ+)
    (fresh : key ∉ ctx.keys)
    (output : CWriteRef (ctx.addBorrowedInput key (.finite dimension) fresh)
      (.finite dimension)) :
    output.toCStorageRef ≠
      CStorageRef.borrowedInputHead ctx key (.finite dimension) fresh := by
  intro same
  apply output.writable
  rw [same]
  rfl

end QuantumAlg.Execution
