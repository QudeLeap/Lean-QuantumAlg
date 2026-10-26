/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Cleanup.Reinitialized
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Cleanup.Resources
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Physical restart of the actual whole point bank

Every path measures all original systems. The same original circuit
restores the borrowed classical interface jointly with the arbitrary
reference and prepares zero on every complete record. The bank itself
is owned; no valid-point or good-prefix premise is imposed.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Cleanup.Parameters

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Cleanup.Parameters ctx)

/-- Every literal cleanup path contains an actual quantum measurement. -/
lemma circuit_measured (path : (parameters.circuit (services := services)).Path) :
    ∃ dimension : ℕ+, Resource.Event.measurement
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) dimension ∈
      (parameters.circuit (services := services)).eventTrace path := by
  refine ⟨2, ?_⟩
  have actual := parameters.circuit_measurement_count (services := services) path
  change ResourcePool.count
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (.measurement (2 : ℕ+)) (ResourcePool.ofList (parameters.circuit.eventTrace path)) = 854
      at actual
  rw [ResourcePool.count_ofList] at actual
  by_contra absent
  have zero := List.count_eq_zero.mpr absent
  omega

/-- All reachable records reset the same fully owned quantum bank with its complete reference. -/
lemma circuit_restartCleanup
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (noBorrowed : ctx.borrowedQuantumWires = []) :
    Circuit.RestartCleanup parameters.circuit environment where
  measured := parameters.circuit_measured (services := services)
  restores := by
    intro Reference History _ state
    exact Circuit.borrowedRestored_of_noBorrowedQuantum parameters.circuit environment
      noBorrowed Reference state
  reinitialized := ⟨ctx.quantumLayout.restrictSelectedBasis ctx.borrowedSelectionᶜ
    parameters.zeroLabel, parameters.circuit_reinitializedAt environment noBorrowed⟩

end

end Cleanup.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
