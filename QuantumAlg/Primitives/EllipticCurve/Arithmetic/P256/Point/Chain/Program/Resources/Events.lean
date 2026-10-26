/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Resources.Bounds
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Cycle.Resources.Events

/-!
# Complete independent native allowance for the original measured point program

All six actual queries and both arithmetic resets retain their finite
nongate labels. Existing same-path native bounds supply the three gate
coordinates independently. No path, Store or program resource projection
occurs in the allowance, including the two complete 256-bit outcome packs.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

open Execution AlgorithmGate EncodedBit.WindowLookup

noncomputable section

/-- Independent nongate source allowances for the original six queries and two resets. -/
def otherEventEnvelope (services : ClassicalOracleModel) (highRemaining lowWidth : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) :=
  let query := RuntimeUnlookup.envelope services 256 lowWidth highRemaining
  let reset := measuredResetWordEnvelope services 256
  (query + query + query + query + query + query) + (reset + reset)

/-- Complete finite point allowance with the original independent worst-mask native bounds. -/
def eventEnvelope (services : ClassicalOracleModel) (highRemaining lowWidth : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) :=
  gateEnvelope BitWord.model services
    (251217348 + 26 * controlSingle (highRemaining + lowWidth) +
      6 * bareQuerySingleLimit highRemaining lowWidth)
    (605210374 + 26 * controlCnot (highRemaining + lowWidth) +
      6 * bareQueryCnotLimit highRemaining lowWidth)
    (972513620 + 26 * controlToffoli (highRemaining + lowWidth) +
      6 * bareQueryToffoliLimit highRemaining lowWidth) +
    nonGateEnvelope (otherEventEnvelope services highRemaining lowWidth)

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Program.Parameters ctx)

attribute [local irreducible] native arithmetic circuit Circuit.resourcePool
  ResourcePool.scale

private lemma query_nongate_pool_le (occurrence : Fin 6)
    (path : (parameters.query (services := services) occurrence).Path) :
    nonGateEnvelope ((parameters.query occurrence).resourcePool path) ≤
      nonGateEnvelope (RuntimeUnlookup.envelope services 256 parameters.lowWidth
        parameters.highRemaining) := by
  have actual := Window.QueryInsertion.circuit_resourcePool
    (parameters.queryParameters occurrence)
    (unitaryOfEqualWires _ _ parameters.sameWires
      (Window.QueryColumns.body parameters.stream
        (parameters.highRemaining + parameters.lowWidth) parameters.addressBound occurrence)) path
  change (parameters.query occurrence).resourcePool path = _ at actual
  have bounded := (parameters.queryParameters occurrence).nongate_pool_le
    (services := services) (parameters.bareQueryPath occurrence path)
  rw [actual, nonGateEnvelope_add, nonGateEnvelope_unitary, add_zero]
  exact bounded

attribute [local irreducible] query

private lemma arithmetic_nongate_pool_le (kind : Arithmetic.Call.Kind)
    (path : (parameters.arithmetic (services := services) kind).Path) :
    nonGateEnvelope ((parameters.arithmetic kind).resourcePool path) ≤
      nonGateEnvelope (measuredResetWordEnvelope services 256) := by
  unfold arithmetic at path ⊢
  rw [Arithmetic.Call.circuit_resourcePool, nonGateEnvelope_add, nonGateEnvelope_add,
    nonGateEnvelope_unitary, nonGateEnvelope_unitary, zero_add, add_zero]
  exact nonGateEnvelope_mono (measuredResetWordCircuit_pool_le (QubitLayout.canonical _)
    parameters.sameWires (Window.resultWord .numerator) (Window.resultWord_distinct .numerator)
    parameters.output parameters.mask _)

private lemma fixed_nongate_pool :
    nonGateEnvelope (parameters.fixedNativePool (services := services)) = 0 := by
  simp only [fixedNativePool, nonGateEnvelope_add, nonGateEnvelope_unitary, zero_add]

private lemma circuit_nongate_pool_le
    (path : (parameters.circuit (services := services)).Path) :
    nonGateEnvelope (parameters.circuit.resourcePool path) ≤
      nonGateEnvelope
        (otherEventEnvelope services parameters.highRemaining parameters.lowWidth) := by
  rw [circuit_resourcePool, nonGateEnvelope_add, nonGateEnvelope_add,
    parameters.fixed_nongate_pool, add_zero]
  simp only [queryPool, callPool, otherEventEnvelope, nonGateEnvelope_add]
  exact add_le_add
    (add_le_add
      (add_le_add
        (add_le_add
          (add_le_add
            (add_le_add (parameters.query_nongate_pool_le 0 (parameters.queryZeroPath path))
              (parameters.query_nongate_pool_le 1 (parameters.queryOnePath path)))
            (parameters.query_nongate_pool_le 2 (parameters.queryTwoPath path)))
          (parameters.query_nongate_pool_le 3 (parameters.queryThreePath path)))
        (parameters.query_nongate_pool_le 4 (parameters.queryFourPath path)))
      (parameters.query_nongate_pool_le 5 (parameters.queryFivePath path)))
    (add_le_add (parameters.arithmetic_nongate_pool_le .division
      (parameters.divisionCallPath path)) (parameters.arithmetic_nongate_pool_le .multiplication
        (parameters.multiplicationCallPath path)))

/-- The same actual complete point path fits the independent full native event pool. -/
lemma circuit_pool_le (path : (parameters.circuit (services := services)).Path) :
    parameters.circuit.resourcePool path ≤
      eventEnvelope services parameters.highRemaining parameters.lowWidth := by
  unfold eventEnvelope
  apply complete_pool_le
  · intro coordinate
    have masks := parameters.selectedMaskSum_le path
    cases coordinate with
    | toffoli => exact parameters.circuit_toffoli_count_le path
    | cnot =>
        have actual := parameters.circuit_cnot_count_le path
        change _ ≤ 605210374 + 26 * controlCnot (parameters.highRemaining + parameters.lowWidth) +
          6 * bareQueryCnotLimit parameters.highRemaining parameters.lowWidth
        omega
    | singleQubit =>
        have actual := parameters.circuit_singleQubit_count_le path
        change _ ≤ 251217348 + 26 * controlSingle (parameters.highRemaining + parameters.lowWidth) +
          6 * bareQuerySingleLimit parameters.highRemaining parameters.lowWidth
        omega
  · exact parameters.circuit_nongate_pool_le path

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
