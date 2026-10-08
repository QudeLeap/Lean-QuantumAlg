/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.Execution
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Borrowed restoration for exact native order finding

The exact source starts with no borrowed system or classical cell. The real
sampler and retained decoder therefore restore every external-reference
correlation independently of the sampled order-grid event.
-/

namespace QuantumAlg.OrderFinding.Exact.NativeEndpoint

noncomputable section

open QuantumAlg.Execution

/-- The complete exact run restores its empty borrowed input jointly with any reference. -/
theorem code_borrowedRestored {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State Sampling.Native.pre Reference
      ((Sampling.Native.model access).HiddenState × History)) :
    (code access).BorrowedRestored Reference state
      ((code access).execute Reference state) :=
  Circuit.borrowedRestored_of_noBorrowedQuantum (code access) rfl Reference state

end

end QuantumAlg.OrderFinding.Exact.NativeEndpoint
