/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Event

/-!
# Unit weight for actual classical operations

This observation counts the closed classical-operation coordinates already
present in an execution ledger. Declared subroutines and quantum operations
receive zero weight; no implementation or event conversion is inferred.
-/

namespace QuantumAlg.Resource.Event

/-- Count one actual classical operation and zero events of every other model. -/
@[expose] public def classicalOperationWeight {model : ExecutionModel} : Event model → Nat
  | .classicalOperation _ => 1
  | _ => 0

end QuantumAlg.Resource.Event
