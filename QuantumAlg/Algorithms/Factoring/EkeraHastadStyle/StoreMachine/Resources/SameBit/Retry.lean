/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Calibration
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Resources.Scalar
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Resources.SameBit.Definitions
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Resources.SameBit.Repetition

/-!
# Public closed form of the Ekerå--Håstad retry count
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace PublicResourceBounds

noncomputable section

/-- The internally selected retry count is the displayed logarithmic ceiling.
The doubled denominator reserves half of the public failure budget for the
one-time key-generation exceptional event. -/
theorem retryCount_eq_closedForm (budget : FailureBudget) :
    NativeFiniteRetry.Calibration.retryCount budget =
      max 1 (Nat.ceil
        (Real.log
            (((2 * budget.failureDenominator : Nat) : Real) /
              budget.failureNumerator) /
          Real.log ((256 : Real) / 147))) := by
  unfold NativeFiniteRetry.Calibration.retryCount FailureBudget.retryCountFor
    FailureBudget.retryExponentFor NativeFiniteRetry.Calibration.retryTargetBudget
    NativeFiniteRetry.Calibration.conditionalFailureBudget
  norm_num

end

end PublicResourceBounds
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
