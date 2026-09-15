/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Program
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Complete borrowed restoration by the actual first batch

The first allocation boundary has no incoming quantum systems. Its borrowed
wire list is therefore empty by the actual sublist invariant. The real owned
preparation, sampling, selected quantum members, measurement, reset and reload
then preserve the full borrowed classical-reference observation. No assumption
is made about the values or correlations in the incoming classical storage.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch

noncomputable section

open Execution

/-- The actual first-batch code restores every borrowed classical-reference correlation. -/
theorem nativeBatch_borrowedRestored (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat) (Reference : Register)
    {History : Type} [Fintype History] (state : State base Reference History) :
    (code base noQuantum N).BorrowedRestored Reference state
      ((code base noQuantum N).execute Reference state) := by
  have noBorrowed : base.borrowedQuantumWires = [] := by
    have subset := base.borrowedQuantumWires_sublist
    rw [noQuantum] at subset
    exact List.sublist_nil.mp subset
  exact Circuit.borrowedRestored_of_noBorrowedQuantum
    (code base noQuantum N) noBorrowed Reference state

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch
