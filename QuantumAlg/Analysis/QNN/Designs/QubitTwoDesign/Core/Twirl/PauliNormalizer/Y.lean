/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.PauliNormalizer.Basic
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.PauliNormalizer.Y.Axis
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.PauliNormalizer.Y.Edge
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.PauliNormalizer.Y.Half

/-! # Pauli-Y normalization by the strict Clifford lift -/

section

namespace QuantumAlg.QubitTwoDesign.PauliNormalizer

open Matrix
open scoped ComplexOrder Kronecker Quaternion QuadraticAlgebra

theorem conjPauliYMem (g : BinaryOctahedral) :
    qubitClifford g * pauliY * (qubitClifford g)ᴴ ∈ signedRawPauliSet := by
  cases g with
  | axis negative coordinate => exact Y.axis negative coordinate
  | half negative => exact Y.half negative
  | edge pair negativeLeft negativeRight => exact Y.edge pair negativeLeft negativeRight

end QuantumAlg.QubitTwoDesign.PauliNormalizer

end
