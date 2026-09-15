/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.PauliNormalizer.Basic
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.PauliNormalizer.Automation

/-! # Pauli-X normalization for axis Clifford codes -/

section

namespace QuantumAlg.QubitTwoDesign.PauliNormalizer.X

open Matrix
open scoped ComplexOrder Kronecker Quaternion QuadraticAlgebra

set_option maxHeartbeats 8000000 in
-- Exhaustive Pauli-X conjugation over the eight axis codes needs this local budget.
theorem axis (negative : Bool) (coordinate : Fin 4) :
    qubitClifford (.axis negative coordinate) * pauliX *
        (qubitClifford (.axis negative coordinate))ᴴ ∈ signedRawPauliSet := by
  fin_cases coordinate <;> cases negative <;> pauliAxisMemFinish

end QuantumAlg.QubitTwoDesign.PauliNormalizer.X

end
