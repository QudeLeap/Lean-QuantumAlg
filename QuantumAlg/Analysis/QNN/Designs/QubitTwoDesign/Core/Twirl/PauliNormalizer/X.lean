/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.PauliNormalizer.Basic
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.PauliNormalizer.X.Axis
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.PauliNormalizer.X.Edge
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.PauliNormalizer.X.Half

/-! # Pauli-X normalization by the strict Clifford lift -/

section

namespace QuantumAlg.QubitTwoDesign.PauliNormalizer

open Matrix
open scoped ComplexOrder Kronecker Quaternion QuadraticAlgebra

lemma conjPauliXMem (g : BinaryOctahedral) :
    qubitClifford g * pauliX * (qubitClifford g)ᴴ ∈ signedRawPauliSet := by
  cases g with
  | axis negative coordinate => exact X.axis negative coordinate
  | half negative => exact X.half negative
  | edge pair negativeLeft negativeRight => exact X.edge pair negativeLeft negativeRight

end QuantumAlg.QubitTwoDesign.PauliNormalizer

end
