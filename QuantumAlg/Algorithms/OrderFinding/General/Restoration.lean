/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.General.Execution
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Preservation

/-!
# Full borrowed restoration of native general order finding

The original canonical base and all of its external-reference correlations
survive the same source sampling, result allocation and native recovery run.
The output manifest and restoration are distinct properties of that execution.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.NativeEndpoint

noncomputable section

open QuantumAlg.Execution

/-- Actual option allocation and finite recovery preserve the entire borrowed joint state. -/
theorem recoveryStage_borrowedRestored {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width) {Reference : Register} {History : Type} [Fintype History]
    (state : State (NativeSampling.post t width) Reference History) :
    (recoveryStage hinput A).BorrowedRestored Reference state
      ((recoveryStage hinput A).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (Circuit.borrowedRestored_retain (resultKey t width) (outputShape t)
      (resultFresh t width) state)
    (ClassicalRoutines.OrderRecovery.Native.nativeRecovery_into_borrowedRestored
      (recoverySpec hinput A) (baseInput t width) (sampleInput t width) (resultRef t width)
      Reference _)

/-- The complete actual sampler and recovery jointly restore every original borrowed resource. -/
theorem code_borrowedRestored {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width) {Reference : Register} {History : Type} [Fintype History]
    (state : State (pre width) Reference History) :
    (code hinput A).BorrowedRestored Reference state ((code hinput A).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state (NativeSampling.borrowedRestored A state)
    (recoveryStage_borrowedRestored hinput A _)

end

end QuantumAlg.OrderFinding.ShorSourceJoint.NativeEndpoint
