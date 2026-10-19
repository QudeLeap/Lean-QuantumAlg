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

/-- The selected count is the positive reciprocal-logarithm ceiling.
Half of the real target is reserved for the one-time original-key exception. -/
lemma retryCount_eq_closedForm (η : Real) :
    NativeFiniteRetry.Calibration.retryCount η =
      Nat.ceil (Real.log (2 / η) / Real.log ((256 : Real) / 147)) :=
  NativeFiniteRetry.Calibration.realRetryCount_eq_inverse_log η

end

end PublicResourceBounds
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
