/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Execution
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Preparation.Seed

/-!
# Complete reference-aware seed of the actual known-order bank

The native-dimensional group bank is allocated by the runtime's fixed zero
preparation. The support statement keeps the persistent group-oracle state,
every classical history and arbitrary external-reference matrix entries.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderExecution

noncomputable section

open QuantumAlg.Execution

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- The real zero allocation has exactly the physical zero seed in every
complete store and external-reference block. -/
theorem preparationCode_zero_seeded (P : KnownOrderProblem G)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State pre Reference ((model P).HiddenState × H)) :
    BasisSeeded.Holds
      (preparedEmptyBasisEquiv pre pre.canonicalFreshKey (OrderOracle.layout P)
        bankFresh (bankDisjoint P) (by rfl)
        (BasisPreparation.zero (OrderOracle.layout P)).value)
      ((preparationCode P).execute Reference state) := by
  exact Circuit.prepareZero_empty_seeded
    (gates := AlgorithmGate.model) (oracles := OrderOracle.model P)
    (operations := BitWord.model)
    (services := ClassicalFiniteGroupOracle.model G)
    pre.canonicalFreshKey (OrderOracle.layout P) bankFresh (bankDisjoint P)
    (by rfl) state

end

end QuantumAlg.FiniteCyclicDLP.OrderExecution
