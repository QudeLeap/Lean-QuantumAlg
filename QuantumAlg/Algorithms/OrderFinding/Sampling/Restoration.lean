/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Sampling.Execution
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Restoration

/-!
# Empty-input sampling restoration

The empty-input endpoint specializes the single Framed sampler.
-/

namespace QuantumAlg.OrderFinding.Sampling

noncomputable section

open QuantumAlg.Execution

/-- The same actual run preserves the complete borrowed state and external reference. -/
theorem code_borrowedRestored {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    {Reference : Register} {H : Type} [Fintype H] (state : State pre Reference H) :
    (code A).BorrowedRestored Reference state ((code A).execute Reference state) :=
  Framed.code_borrowedRestored pre pre_quantumWires A state

end

end QuantumAlg.OrderFinding.Sampling
