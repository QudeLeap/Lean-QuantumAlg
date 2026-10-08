/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Parameters
import all QuantumAlg.Core.Measure

/-!
# Original finite sample and terminal outcome values

The value type is independent of its probability law. The measurement field
expands the definition of OrderFinding.Outcome without changing its type.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical

/-- One source sample together with the Born result for its selected circuit member. -/
structure SourceOutcome (N : Nat) where
  /-- The original little-endian finite random sample. -/
  sample : Fin (2 ^ residueSamplingBits N)
  /-- The selected member's big-endian phase-register measurement. -/
  measurement : TerminalZMeasure.Outcome (phaseBits N)

end QuantumAlg.Factoring.ShorStyle.Canonical
