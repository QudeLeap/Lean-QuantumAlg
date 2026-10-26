/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Insertion

/-!
# Actual query resources with the intervening arithmetic retained

The original runtime-array load and same-array measured unlookup keep
their actual path, including every paid mask feedback instruction. The
intervening native arithmetic contributes its own event pool and depth.
No gate count is exchanged for a classical operation count.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryInsertion

noncomputable section

open Execution EncodedBit.WindowLookup

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    {lowWidth highRemaining : Nat}
    (parameters : RuntimeTable.CycleParameters encoding ctx 256 lowWidth highRemaining)
    (body : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout)

/-- Removing only the intervening unitary retains both original actual query records. -/
def queryPath
    (path : (circuit (services := services) parameters body).Path) :
    (parameters.circuit (services := services)).Path :=
  ⟨path.1, path.2.2⟩

/-- The complete actual query pool and the actual arithmetic pool are both retained. -/
lemma circuit_resourcePool
    (path : (circuit (services := services) parameters body).Path) :
    (circuit parameters body).resourcePool path =
      parameters.circuit.resourcePool (queryPath parameters body path) +
        body.eventCost BitWord.model services := by
  rcases path with ⟨first, own, last⟩
  change ResourcePool.ofList ((load parameters).eventTrace first ++
    (body.eventTrace BitWord.model services ++ (unlookup parameters).eventTrace last)) =
      ResourcePool.ofList ((load parameters).eventTrace first ++
        (unlookup parameters).eventTrace last) + body.eventCost BitWord.model services
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append, ResourcePool.ofList_append,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost body BitWord.model services]
  ac_rfl

/-- Native arithmetic adds no measurements to the original 256 physical outcomes. -/
lemma circuit_measurement_count
    (path : (circuit (services := services) parameters body).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+)) ((circuit parameters body).resourcePool path) = 256 := by
  rw [circuit_resourcePool, ResourcePool.count_add,
    UnitaryCircuit.unitaryCircuit_event_count_classical_context,
    Nat.add_zero]
  exact parameters.measurement_count (queryPath parameters body path)

private lemma native_classical_weight :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (body.eventCost BitWord.model services) = 0 := by
  apply ResourcePool.weightedCount_eq_zero_of_mem
  intro event present
  cases event with
  | classicalOperation coordinate =>
      have absent := UnitaryCircuit.unitaryCircuit_event_count_classical_context body
        BitWord.model services (.classicalOperation coordinate)
      exact False.elim ((Multiset.count_eq_zero.mp absent) present)
  | _ => rfl

/-- The real parity feedback remains in its original independent classical coordinate. -/
lemma circuit_classical_weight_le
    (path : (circuit (services := services) parameters body).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((circuit parameters body).resourcePool path) ≤
        RuntimeTable.runtimeCycleClassicalLimit 256 highRemaining lowWidth := by
  rw [circuit_resourcePool, ResourcePool.weightedCount_add, native_classical_weight,
    Nat.add_zero]
  exact (parameters.separate_coordinates (queryPath parameters body path)).2

/-- The actual dependence depth includes the arithmetic between the original query directions. -/
lemma circuit_quantumTime
    (path : (circuit (services := services) parameters body).Path) :
    (circuit parameters body).depth Resource.Event.quantumDuration path =
      parameters.circuit.depth Resource.Event.quantumDuration
        (queryPath parameters body path) +
          body.evaluatedEventDepth Resource.Event.quantumDuration := by
  rcases path with ⟨first, own, last⟩
  change (load parameters).depth Resource.Event.quantumDuration first +
    (DepthExpr.depthEval Resource.Event.quantumDuration (body.eventDepth BitWord.model services) +
      (unlookup parameters).depth Resource.Event.quantumDuration last) =
        ((load parameters).depth Resource.Event.quantumDuration first +
          (unlookup parameters).depth Resource.Event.quantumDuration last) +
            body.evaluatedEventDepth Resource.Event.quantumDuration
  rw [UnitaryCircuit.unitaryCircuit_quantumDuration_classical_context]
  omega

/-- Every gate is charged separately to the same actual query record and native body. -/
lemma circuit_gate_count (coordinate : AlgorithmGate.Coordinate)
    (path : (circuit (services := services) parameters body).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate coordinate)
      ((circuit parameters body).resourcePool path) =
        ResourcePool.count
          (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate coordinate)
          (parameters.circuit.resourcePool (queryPath parameters body path)) +
            ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
              (.gate coordinate) body.eventCost := by
  rw [circuit_resourcePool, ResourcePool.count_add,
    UnitaryCircuit.unitaryCircuit_event_count_classical_context]

end

end QueryInsertion

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
