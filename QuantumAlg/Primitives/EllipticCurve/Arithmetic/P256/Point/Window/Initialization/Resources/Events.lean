/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Initialization.Resources
import all QuantumAlg.Components.GateModel.Algorithm.Resources.Events

/-!
# Complete independent events for the actual whole-bank restart

All 854 real measurements and selected X corrections precede the original
512-bit affine loader. Its actual selected native X word has a fixed
independent complete allowance and contributes no classical instruction.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Initialization

noncomputable section

attribute [local irreducible] program placedProgram ResourcePool.scale

/-- Full native allowance for the complete reset followed by both affine-coordinate loaders. -/
def eventEnvelope (services : ClassicalOracleModel) :
    ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) :=
  ResourcePool.scale 854 (Cleanup.Parameters.oneBudget (services := services)) +
    AlgorithmGate.gateEnvelope BitWord.model services 512 0 0

/-- Every actual original restart path obeys the independent complete event allowance. -/
lemma prepared_pool_le {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Cleanup.Parameters ctx) (x y : Fin (2 ^ 256))
    (path : (parameters.prepared (services := services) (placedProgram parameters x y)).Path) :
    (parameters.prepared (placedProgram parameters x y)).resourcePool path ≤
      eventEnvelope services := by
  have reset := parameters.circuit_pool_le (services := services) path.1
  have loader := AlgorithmGate.algorithmGate_unitary_pool_le (placedProgram parameters x y)
    BitWord.model services 512 0 0 (by
      intro coordinate
      rw [placedProgram, Execution.unitaryOfEqualWires_cost]
      have native := program_native_counts x y
      cases coordinate with
      | toffoli => exact native.1.le
      | cnot => exact native.2.1.le
      | singleQubit => exact native.2.2)
  exact (prepared_resourcePool parameters x y path).le.trans (add_le_add reset loader)

end

end Initialization

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
