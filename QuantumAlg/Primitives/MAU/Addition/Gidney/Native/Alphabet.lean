/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Resources
import all QuantumAlg.Core.Base.Accounting.Control

/-!
# Native alphabet of a pivot-flip modular offset

The comparison uses primitive coordinates, while the coherent bi-flip
adds one qubit control to those same native labels. These are distinct
coordinates in the independently specified offset alphabet.
-/

namespace QuantumAlg.MAU.Addition.Gidney

noncomputable section

/-- Uncontrolled and once-controlled primitive coordinates of an actual modular offset. -/
def offsetAlphabet : ResourcePool .quantum :=
  EncodedBit.GateSpec.primitiveAlphabet +
    ResourcePool.controlForDimension 2 EncodedBit.GateSpec.primitiveAlphabet

end

end QuantumAlg.MAU.Addition.Gidney
