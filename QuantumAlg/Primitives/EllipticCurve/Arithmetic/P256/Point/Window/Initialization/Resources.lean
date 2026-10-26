/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Initialization.Seed
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting.QuantumTime
import all QuantumAlg.Core.Base.Accounting.ClassicalWeight

/-!
# Same-path resources of complete fixed-point re-preparation

The literal whole-bank reset and actual affine X layer are both counted.
Their measurements, native gates and dependency time belong to the same
complete execution path. The resident context contains the same original
854 quantum systems and existing classical cells throughout.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Initialization

noncomputable section

open Execution

attribute [local irreducible] program placedProgram ResourcePool.scale

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Cleanup.Parameters ctx) (x y : Fin (2 ^ 256))

lemma prepared_resourcePool
    (path : (parameters.prepared (services := services) (placedProgram parameters x y)).Path) :
    (parameters.prepared (placedProgram parameters x y)).resourcePool path =
      parameters.circuit.resourcePool path.1 +
        (placedProgram parameters x y).eventCost BitWord.model services := by
  change ResourcePool.ofList (parameters.circuit.eventTrace path.1 ++
    (placedProgram parameters x y).eventTrace BitWord.model services) = _
  rw [ResourcePool.ofList_append,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost _ BitWord.model services]
  rfl

private lemma placed_gate_count (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate coordinate)
      ((placedProgram parameters x y).eventCost BitWord.model services) =
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate coordinate)
        (program x y).eventCost := by
  rw [UnitaryCircuit.unitaryCircuit_event_count_classical_context
    (placedProgram parameters x y) BitWord.model services (.gate coordinate)]
  rw [placedProgram, unitaryOfEqualWires_cost]

/-- The actual reset and actual fixed loader introduce no Toffoli or CNOT. -/
lemma prepared_native_counts
    (path : (parameters.prepared (services := services) (placedProgram parameters x y)).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .toffoli)
      ((parameters.prepared (placedProgram parameters x y)).resourcePool path) = 0 ∧
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .cnot)
      ((parameters.prepared (placedProgram parameters x y)).resourcePool path) = 0 ∧
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .singleQubit)
      ((parameters.prepared (placedProgram parameters x y)).resourcePool path) ≤ 1366 := by
  simp only [prepared_resourcePool, ResourcePool.count_add,
    placed_gate_count]
  have reset := parameters.circuit_native_counts (services := services) path.1
  have load := program_native_counts x y
  exact ⟨by omega, by omega, by omega⟩

/-- Every full restart path contains all 854 actual whole-bank measurements. -/
lemma prepared_measurement_count
    (path : (parameters.prepared (services := services) (placedProgram parameters x y)).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+))
      ((parameters.prepared (placedProgram parameters x y)).resourcePool path) = 854 := by
  rw [prepared_resourcePool, ResourcePool.count_add,
    UnitaryCircuit.unitaryCircuit_event_count_classical_context, Nat.add_zero]
  exact parameters.circuit_measurement_count (services := services) path.1

/-- The native layer retains its genuine one-layer dependency expression after real reset. -/
lemma prepared_quantumTime
    (path : (parameters.prepared (services := services) (placedProgram parameters x y)).Path) :
    (parameters.prepared (placedProgram parameters x y)).depth Resource.Event.quantumDuration path =
      parameters.circuit.depth Resource.Event.quantumDuration path.1 +
        (program x y).evaluatedEventDepth Resource.Event.quantumDuration := by
  change parameters.circuit.depth Resource.Event.quantumDuration path.1 +
    DepthExpr.depthEval Resource.Event.quantumDuration
      ((placedProgram parameters x y).eventDepth BitWord.model services) = _
  rw [UnitaryCircuit.unitaryCircuit_quantumDuration_classical_context]
  simp only [UnitaryCircuit.evaluatedEventDepth, placedProgram, unitaryOfEqualWires_depth]

lemma prepared_quantumTime_le
    (path : (parameters.prepared (services := services) (placedProgram parameters x y)).Path) :
    (parameters.prepared (placedProgram parameters x y)).depth Resource.Event.quantumDuration
      path ≤ 855 := by
  rw [prepared_quantumTime]
  exact Nat.add_le_add (parameters.circuit_quantumTime_le (services := services) path.1)
    (program_quantumTime_le x y)

private lemma loader_classical_weight :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((placedProgram parameters x y).eventCost BitWord.model services) = 0 := by
  apply ResourcePool.weightedCount_eq_zero_of_mem
  intro event present
  cases event with
  | classicalOperation coordinate =>
      have absent := UnitaryCircuit.unitaryCircuit_event_count_classical_context
        (placedProgram parameters x y) BitWord.model services (.classicalOperation coordinate)
      exact False.elim ((Multiset.count_eq_zero.mp absent) present)
  | _ => rfl

/-- Measurements and the native X layer add no classical model instruction. -/
lemma prepared_classical_weight
    (path : (parameters.prepared (services := services) (placedProgram parameters x y)).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((parameters.prepared (placedProgram parameters x y)).resourcePool path) = 0 := by
  rw [prepared_resourcePool, ResourcePool.weightedCount_add, loader_classical_weight,
    Nat.add_zero]
  have bound := ResourcePool.weightedCount_mono
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    Resource.Event.classicalOperationWeight
    (actual := parameters.circuit.resourcePool path.1)
    (budget := ResourcePool.scale 854 (Cleanup.Parameters.oneBudget (services := services)))
    (parameters.circuit_pool_le (services := services) path.1)
  apply Nat.eq_zero_of_le_zero
  simpa only [ResourcePool.scale, ResourcePool.weightedCount_nsmul,
    Cleanup.Parameters.oneBudget, ResourcePool.weightedCount_add,
    ResourcePool.weightedCount_singleton, Resource.Event.classicalOperationWeight,
    Nat.add_zero, Nat.mul_zero] using bound

/-- No new quantum or classical cell is allocated by this actual restoration. -/
lemma prepared_peakResidentSpace
    (path : (parameters.prepared (services := services) (placedProgram parameters x y)).Path) :
    (parameters.prepared (placedProgram parameters x y)).peakResidentSpace path =
      ctx.residentSpace :=
  (parameters.prepared (placedProgram parameters x y)).fixed_peakResidentSpace path

end

end Initialization

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
