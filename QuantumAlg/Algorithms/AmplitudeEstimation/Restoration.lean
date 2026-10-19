/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Execution
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Complete external-reference restoration in amplitude estimation

The actual preparation, native word, allocation, measurement and packing
preserve the whole external reference. This follows from the canonical
interpreter theorem for an input without borrowed quantum wires and does not
use a success event or an output-state assumption.
-/

namespace QuantumAlg.AmplitudeEstimation

noncomputable section

open QuantumAlg.Execution

/-- Every actual run preserves the complete borrowed interface and external reference jointly. -/
lemma code_borrowedRestored (n t : Nat) (environment : (model n).Environment)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State pre Reference (ClassicalOracleModel.empty.HiddenState × H)) :
    (code n t).BorrowedRestored Reference state ((code n t).execute environment Reference state) :=
  Circuit.borrowedRestored_of_noBorrowedQuantum (code n t) environment rfl Reference state

end

end QuantumAlg.AmplitudeEstimation
