/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.PauliNormalizer.Basic
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.PauliNormalizer.Z.Axis
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.PauliNormalizer.Z.Edge
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Twirl.PauliNormalizer.Z.Half

/-! # Pauli-Z normalization by the strict Clifford lift -/

section

namespace QuantumAlg.QubitTwoDesign.PauliNormalizer

open Matrix
open scoped ComplexOrder Kronecker Quaternion QuadraticAlgebra

lemma conjPauliZMem (g : BinaryOctahedral) :
    qubitClifford g * pauliZ * (qubitClifford g)ᴴ ∈ signedRawPauliSet := by
  cases g with
  | axis negative coordinate => exact Z.axis negative coordinate
  | half negative => exact Z.half negative
  | edge pair negativeLeft negativeRight => exact Z.edge pair negativeLeft negativeRight

end QuantumAlg.QubitTwoDesign.PauliNormalizer

end
