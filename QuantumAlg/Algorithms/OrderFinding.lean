/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Algorithms.OrderFinding.Native
public import QuantumAlg.Algorithms.OrderFinding.Eigenstructure
public import QuantumAlg.Algorithms.OrderFinding.Exact
import QuantumAlg.Algorithms.OrderFinding.GcdBridge
public import QuantumAlg.Algorithms.OrderFinding.General
import QuantumAlg.Algorithms.OrderFinding.Probability

/-!
# Order finding

Canonical aggregate for exact and general native quantum order finding,
including the source-joint probability bridge, resource projections, and
classical gcd reduction boundary. Legacy circuit and orbit helpers retain
their own module paths while their production consumers migrate.
-/

section

end
