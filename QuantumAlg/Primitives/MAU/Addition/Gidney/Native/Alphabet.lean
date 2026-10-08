/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Resources

/-!
# Native alphabet of a pivot-flip modular offset

Comparison and controlled bi-flips emit actual default-model primitives.
The resulting alphabet contains only single-qubit gates, CNOT and Toffoli;
coherent control does not introduce an additional native coordinate.
-/

namespace QuantumAlg.MAU.Addition.Gidney

noncomputable section

/-- The three actual default-model coordinates of an expanded modular offset. -/
def offsetAlphabet : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  EncodedBit.GateSpec.primitiveAlphabet

end

end QuantumAlg.MAU.Addition.Gidney
