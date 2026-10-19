/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.SwapTest.Execution
import all QuantumAlg.Primitives.HadamardTest.Restoration
import all QuantumAlg.Primitives.HadamardTest.Execution
import all QuantumAlg.Core.Execution.Borrowed.State

/-!
# Complete reference restoration of the actual SWAP-test execution

The exact execution equality transfers preservation of all borrowed/reference
observations. It does not make a restoration promise for the owned input words.
-/

namespace QuantumAlg.SwapTest

noncomputable section

open Execution

lemma code_borrowedRestored (width : Nat) (actual : model.Environment) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State (pre width) Reference (ClassicalOracleModel.empty.HiddenState × History)) :
    (code width).BorrowedRestored
      Reference state ((code width).execute actual Reference state) := by
  rw [code_execute]
  exact HadamardTest.code_borrowedRestored (width + width)
    (HadamardTest.environment (swapRegistersOp width)) state

end

end QuantumAlg.SwapTest
