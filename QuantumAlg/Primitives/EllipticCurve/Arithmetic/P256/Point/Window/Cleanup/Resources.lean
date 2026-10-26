/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Cleanup
import all QuantumAlg.Components.Classical.Model.BitWord
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Resources
import all QuantumAlg.Core.Base.Accounting.ClassicalWeight
import all QuantumAlg.Core.Execution.Circuit.Weighted
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources

/-!
# Same-program complete point-bank cleanup resources

Every actual path pays one MZ per original system and only its selected
identity or native X. The reused outcome cell already belongs to the
caller. Quantum duration counts the literal sequential corrections;
classical operations are not exchanged for quantum gates.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Cleanup.Parameters

noncomputable section

open Execution

private instance cleanupResourceDimensionNeZero (dimension : ℕ+) : NeZero (dimension : Nat) :=
  ⟨Nat.ne_of_gt dimension.property⟩

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Cleanup.Parameters ctx)

attribute [local irreducible] ResourcePool.scale

include parameters in
lemma systemCount_eq : ctx.systemCount = 854 := by
  have count := congrArg List.length parameters.sameWires
  simp only [QuantumLayout.wires, List.length_ofFn] at count
  exact count.symm.trans encoding_width

/-- An independent allowance for the real measurement and at most one actual X. -/
def oneBudget : ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) :=
  ResourcePool.singleton
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (.measurement (2 : ℕ+)) + ResourcePool.singleton
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .singleQubit)

lemma one_eventTrace (wire : Fin ctx.systemCount)
    (path : (parameters.one (services := services) wire).Path) :
    (parameters.one wire).eventTrace path =
      Resource.Event.measurement
        (model := .quantum AlgorithmGate.model .empty BitWord.model services) (2 : ℕ+) ::
        (if -path.2.1.toFin = 0 then [] else [Resource.Event.gate .singleQubit]) := by
  rcases path with ⟨measured, selected, inner⟩
  change Circuit.zEvent (ctx.quantumLayout.wire wire).dimension BitWord.model services ::
    (QuditShift.qubitShiftCircuit ctx.quantumLayout wire (parameters.qubit wire) .empty
      (-selected.toFin)).eventTrace BitWord.model services = _
  have first := congrArg
    (fun dimension : ℕ+ => Circuit.zEvent (gates := AlgorithmGate.model)
      (oracles := .empty) dimension BitWord.model services)
    (parameters.qubit wire)
  rw [first, QuditShift.qubitShiftCircuit_events ctx.quantumLayout wire
    (parameters.qubit wire) .empty (-selected.toFin) BitWord.model services]
  rfl

lemma one_pool_le (wire : Fin ctx.systemCount)
    (path : (parameters.one (services := services) wire).Path) :
    (parameters.one wire).resourcePool path ≤ oneBudget (services := services) := by
  change ResourcePool.ofList ((parameters.one wire).eventTrace path) ≤ _
  rw [one_eventTrace]
  split_ifs <;> simp [oneBudget, ResourcePool.ofList_cons]

lemma one_measurement_count (wire : Fin ctx.systemCount)
    (path : (parameters.one (services := services) wire).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+)) ((parameters.one wire).resourcePool path) = 1 := by
  change ResourcePool.count
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.measurement (2 : ℕ+))
    (ResourcePool.ofList ((parameters.one wire).eventTrace path)) = 1
  rw [one_eventTrace]
  split_ifs <;> simp

/-- The allowance is derived from every actual indexed reset, including all 854 measurements. -/
lemma circuit_pool_le (path : (parameters.circuit (services := services)).Path) :
    parameters.circuit.resourcePool path ≤
      ResourcePool.scale 854 (oneBudget (services := services)) := by
  dsimp only [circuit, run, id_eq] at path ⊢
  have actual := Circuit.forRange_pool_le
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx.systemCount
    (fun wire => parameters.one (services := services) wire) (oneBudget (services := services))
    (fun wire current => parameters.one_pool_le (services := services) wire current) path
  have budgetEq := congrArg
    (fun count => ResourcePool.scale count (oneBudget (services := services)))
      parameters.systemCount_eq
  rw [← budgetEq]
  exact actual

/-- The actual measurements and conditional X gates incur no classical operation. -/
lemma circuit_classical_zero (path : (parameters.circuit (services := services)).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (parameters.circuit.resourcePool path) = 0 := by
  have bounded := ResourcePool.weightedCount_mono
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    Resource.Event.classicalOperationWeight
    (parameters.circuit_pool_le (services := services) path)
  have budgetZero : ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (ResourcePool.scale 854 (oneBudget (services := services))) = 0 := by
    simp only [ResourcePool.scale, ResourcePool.weightedCount_nsmul, oneBudget,
      ResourcePool.weightedCount_add, ResourcePool.weightedCount_singleton,
      Resource.Event.classicalOperationWeight, Nat.zero_add, Nat.mul_zero]
  exact Nat.eq_zero_of_le_zero (bounded.trans_eq budgetZero)

/-- No Toffoli or CNOT is introduced by the actual whole-bank cleanup. -/
lemma circuit_native_counts (path : (parameters.circuit (services := services)).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .toffoli)
        (parameters.circuit.resourcePool path) = 0 ∧
      ResourcePool.count
        (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .cnot)
        (parameters.circuit.resourcePool path) = 0 ∧
      ResourcePool.count
        (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .singleQubit)
        (parameters.circuit.resourcePool path) ≤ 854 := by
  have counts := (ResourcePool.le_iff_count
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (left := parameters.circuit.resourcePool path)
    (right := ResourcePool.scale 854 (oneBudget (services := services)))).mp
      (parameters.circuit_pool_le (services := services) path)
  have first := counts (.gate .toffoli)
  have second := counts (.gate .cnot)
  have third := counts (.gate .singleQubit)
  simp only [ResourcePool.count_scale, oneBudget, ResourcePool.count_add,
    ResourcePool.count_singleton, reduceCtorEq, ↓reduceIte, Nat.zero_add,
    Nat.mul_one] at first second third
  exact ⟨Nat.eq_zero_of_le_zero first, Nat.eq_zero_of_le_zero second, third⟩

/-- The literal range executes exactly one real MZ for each original physical system. -/
lemma circuit_measurement_count (path : (parameters.circuit (services := services)).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+)) (parameters.circuit.resourcePool path) = 854 := by
  dsimp only [circuit, run, id_eq] at path ⊢
  have actual := Circuit.forRange_event_count
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (.measurement (2 : ℕ+)) ctx.systemCount
    (fun wire => parameters.one (services := services) wire) 1
    (fun wire current => parameters.one_measurement_count (services := services) wire current) path
  exact actual.trans (by rw [Nat.mul_one, parameters.systemCount_eq])

/-- The same emitted sequential schedule has at most 854 quantum-duration units. -/
lemma circuit_quantumTime_le (path : (parameters.circuit (services := services)).Path) :
    parameters.circuit.depth Resource.Event.quantumDuration path ≤ 854 := by
  have actual := Circuit.depth_le_weightedCount_of_pool_le
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) parameters.circuit
    Resource.Event.quantumDuration (ResourcePool.scale 854 (oneBudget (services := services))) path
      (parameters.circuit_pool_le (services := services) path)
  simpa only [ResourcePool.scale, ResourcePool.weightedCount_nsmul, oneBudget,
    ResourcePool.weightedCount_add, ResourcePool.weightedCount_singleton,
    Resource.Event.quantumDuration, Nat.mul_zero, Nat.mul_one, Nat.zero_add] using actual

end

end Cleanup.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
