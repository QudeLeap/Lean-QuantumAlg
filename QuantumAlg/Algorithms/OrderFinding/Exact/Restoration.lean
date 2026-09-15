/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Exact.Context
import all QuantumAlg.Algorithms.OrderFinding.Exact.Execution
import all QuantumAlg.Algorithms.OrderFinding.Exact.DecodeLaws
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Restoration
import all QuantumAlg.Core.Execution.Borrowed.Preservation

/-!
# Complete borrowed-reference restoration for decoded order finding

The actual sampling execution preserves the external reference. Its following
retained decoder preserves all borrowed classical and quantum storage jointly
with that same reference. Circuit composition carries both facts through the
single execution and its complete final storage.
-/

namespace QuantumAlg.OrderFinding.Exact

noncomputable section

open QuantumAlg.Execution

/-- The full sampling and decoding execution restores every borrowed correlation. -/
theorem code_borrowedRestored {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State Sampling.pre Reference History) :
    (code A).BorrowedRestored Reference state ((code A).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state (Sampling.code_borrowedRestored A state)
    (decoderCode_borrowedRestored t n Reference _)

end

end QuantumAlg.OrderFinding.Exact
