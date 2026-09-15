/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Oracle.Common
import all QuantumAlg.Components.Oracle.Reflection
import all QuantumAlg.Components.Oracle.ZeroReflection
import all QuantumAlg.Components.Oracle.BlockEncoding
import all QuantumAlg.Components.Oracle.SignalProcessing
import all QuantumAlg.Components.Oracle.TimeEvolution

/-!
# Oracle components

Stable re-export header for reusable oracle components.  Algorithm-specific
oracle hypotheses remain in `QuantumAlg.Algorithms`; primitive-specific wrappers
remain in `QuantumAlg.Primitives`. This namespace collects Components-layer
oracle building blocks that do not import those later layers.

When introducing an oracle-based algorithm, first search this module and its
submodules for an existing XOR, phase, reflection, projector-controlled NOT, or
block-encoding constructor. Add a new component oracle only when the constructor
is reusable without importing `Primitives` or `Algorithms`; keep
algorithm-specific oracle models local to the algorithm module.
-/

section

end
