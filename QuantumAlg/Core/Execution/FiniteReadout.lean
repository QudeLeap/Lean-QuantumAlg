/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Store

/-!
# Finite classical readout transport

Equality transport of a finite register dimension preserves its storage key
and the integer value actually read from that same register.
-/

namespace QuantumAlg.Execution.FiniteReadout

noncomputable section

theorem transported_key {ctx : RuntimeCtx .quantum} {actual intended : ℕ+}
    (same : actual = intended) (ref : CWriteRef ctx (.finite intended)) :
    (Eq.mpr (congrArg (fun dimension => CWriteRef ctx (.finite dimension)) same) ref).key =
      ref.key := by
  cases same
  rfl

theorem transported_read_value {ctx : RuntimeCtx .quantum} {actual intended : ℕ+}
    (same : actual = intended) (ref : CWriteRef ctx (.finite intended)) (store : Store ctx) :
    (store.read (.storage
      (Eq.mpr (congrArg (fun dimension => CWriteRef ctx (.finite dimension)) same)
        ref).toCStorageRef)).toFin.val = (store.read (.storage ref.toCStorageRef)).toFin.val := by
  cases same
  rfl

end

end QuantumAlg.Execution.FiniteReadout
