/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Finalized.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Finalized.Space

/-!
# Numeric resources of the actual terminally cleaned P-256 run

These closed gate bounds follow from the already proved native limits of the
same three-attempt `runFinalized` circuit. Measurement, duration, modeled
classical work and space retain their separate actual-path proofs. The space
bounds still include the caller's original resident and auxiliary contexts.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage.Inputs

noncomputable section

open Execution ClassicalRoutines

/-- Closed native coordinates for the actual terminally cleaned run. -/
def runFinalizedNativeLimit : AlgorithmGate.Coordinate → Nat
  | .toffoli => 99272733288
  | .cnot => 81134896044
  | .singleQubit => 25700867624

/-- Every numeral comes from the existing three-attempt ledger and the 854 terminal X gates. -/
lemma runFinalizedNativeLimit_source (coordinate : AlgorithmGate.Coordinate) :
    runFinalizedNativeLimit coordinate =
      Recovery.Parameters.runNativeLimit coordinate +
        (if coordinate = .singleQubit then 854 else 0) := by
  obtain ⟨toffoli, cnot, singleQubit⟩ := Recovery.Parameters.runNativeLimit_values
  cases coordinate <;> norm_num [runFinalizedNativeLimit, toffoli, cnot, singleQubit] <;> decide

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Inputs ctx)

/-- The three concrete native ceilings concern every path of this exact finalized program. -/
lemma runFinalized_native_numeric_le (coordinate : AlgorithmGate.Coordinate)
    (path : (original.runFinalized (services := services)).code.Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate coordinate)
      ((original.runFinalized (services := services)).code.resourcePool path) ≤
        runFinalizedNativeLimit coordinate := by
  rw [runFinalizedNativeLimit_source]
  exact original.runFinalized_native_le coordinate path

/-- Exact measurement count and duration and modeled classical ceilings for the
same actual path. Its live-space bounds are the imported
`runFinalized_resident_le` and `runFinalized_auxiliary_le` theorems. -/
lemma runFinalized_other_numeric
    (path : (original.runFinalized (services := services)).code.Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.measurement (2 : ℕ+))
        ((original.runFinalized (services := services)).code.resourcePool path) = 215432 ∧
      (original.runFinalized (services := services)).code.depth
        Resource.Event.quantumDuration path ≤ 171185448791 ∧
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        ((original.runFinalized (services := services)).code.resourcePool path) ≤
          20288182564 := by
  exact ⟨original.runFinalized_measurement_count path,
    original.runFinalized_quantumTime_le path,
    original.runFinalized_classical_le path⟩

end

end Storage.Inputs

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
