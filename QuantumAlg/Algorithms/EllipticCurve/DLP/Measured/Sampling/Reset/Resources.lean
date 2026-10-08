/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Reset

/-!
# Finite native reset branch allowances

Each physical wire executes one Z measurement and the selected exact
identity/X correction. A zero correction emits no native gate. The pool and
depth allowances charge at most one X per physical wire; the path identities
retain the actual selected trace.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution

private abbrev ResetModel : ExecutionModel := .quantum AlgorithmGate.model .empty

/-- One measurement and at most one actual native X are available at each wire. -/
private def resetWireBudget {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount) :
    ResourcePool ResetModel :=
  ResourcePool.singleton (Circuit.zEvent (ctx.quantumLayout.wire wire).dimension) +
    ResourcePool.singleton (model := ResetModel) (.gate AlgorithmGate.Coordinate.singleQubit)

private def resetWireDepth {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (duration : Resource.Event ResetModel → Nat) : Nat :=
  duration (Circuit.zEvent (ctx.quantumLayout.wire wire).dimension) +
    duration (.gate .singleQubit)

private theorem resetWire_pool_le {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (qubit : (ctx.quantumLayout.wire wire).dimension = 2)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    (path : (QuditShift.resetWireToBasis wire
      (QuditShift.qubitRealizations ctx.quantumLayout wire qubit .empty) output value).Path) :
    (QuditShift.resetWireToBasis wire
      (QuditShift.qubitRealizations ctx.quantumLayout wire qubit .empty) output value).resourcePool
        path ≤ resetWireBudget wire := by
  rw [QuditShift.resetWireToBasis_pool]
  have correction : ResourcePool.ofList
      ((QuditShift.qubitShiftCircuit ctx.quantumLayout wire qubit .empty
        (value - path.2.1.toFin)).eventTrace) ≤
      ResourcePool.singleton (model := ResetModel) (.gate .singleQubit) := by
    rw [QuditShift.qubitShiftCircuit_events]
    split <;> simp [ResourcePool.ofList, ResourcePool.singleton]
  simpa only [resetWireBudget, QuditShift.qubitRealizations, ResourcePool.ofList_cons]
    using add_le_add_right correction _

private theorem resetWire_depth_le {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (qubit : (ctx.quantumLayout.wire wire).dimension = 2)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    (duration : Resource.Event ResetModel → Nat)
    (path : (QuditShift.resetWireToBasis wire
      (QuditShift.qubitRealizations ctx.quantumLayout wire qubit .empty) output value).Path) :
    (QuditShift.resetWireToBasis wire
      (QuditShift.qubitRealizations ctx.quantumLayout wire qubit .empty) output value).depth
        duration path ≤ resetWireDepth wire duration := by
  rw [QuditShift.resetWireToBasis_duration]
  have correction :
      (QuditShift.qubitShiftCircuit ctx.quantumLayout wire qubit .empty
        (value - path.2.1.toFin)).evaluatedEventDepth duration ≤
        duration (.gate .singleQubit) := by
    by_cases zero : value - path.2.1.toFin = 0
    · simp [QuditShift.qubitShiftCircuit, zero]
    · simp only [QuditShift.qubitShiftCircuit, if_neg zero, Gate.singleQubitAt,
        UnitaryCircuit.evaluatedEventDepth_native]
      change duration (.gate .singleQubit) ≤ duration (.gate .singleQubit)
      exact le_rfl
  exact Nat.add_le_add_left correction _

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail exponentWidth : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (seed : AffinePoint E)

/-- The actual wire order allows one Z measurement and at most one X per position. -/
def samplingResetBudget : ResourcePool ResetModel :=
  ∑ wire : Fin (PublicInput.terminal E exponentWidth).systemCount,
    resetWireBudget wire

omit [Fact p.Prime] in
/-- The independent reset allowance contains one Z and one possible X per real wire. -/
theorem samplingResetBudget_card :
    (samplingResetBudget E exponentWidth).card =
      2 * (PublicInput.terminal E exponentWidth).systemCount := by
  simp [samplingResetBudget, resetWireBudget, ResourcePool.singleton,
    Multiset.card_sum]
  omega

omit [Fact p.Prime] in
/-- Exactly one possible native X gate per live qubit is reserved by reset. -/
theorem samplingResetBudget_singleQubit_count :
    ResourcePool.count (model := ResetModel) (.gate AlgorithmGate.Coordinate.singleQubit)
      (samplingResetBudget E exponentWidth) =
      (PublicInput.terminal E exponentWidth).systemCount := by
  simp [samplingResetBudget, resetWireBudget, ResourcePool.count_finset_sum,
    Circuit.zEvent]

omit [Fact p.Prime] in
/-- Reset uses measurements and possible X gates, so it reserves no CNOT gates. -/
theorem samplingResetBudget_cnot_count :
    ResourcePool.count (model := ResetModel) (.gate AlgorithmGate.Coordinate.cnot)
      (samplingResetBudget E exponentWidth) = 0 := by
  simp [samplingResetBudget, resetWireBudget, ResourcePool.count_finset_sum,
    Circuit.zEvent]

omit [Fact p.Prime] in
/-- Reset reserves measurements and possible X gates, but no Toffoli gates. -/
theorem samplingResetBudget_toffoli_count :
    ResourcePool.count (model := ResetModel) (.gate AlgorithmGate.Coordinate.toffoli)
      (samplingResetBudget E exponentWidth) = 0 := by
  simp [samplingResetBudget, resetWireBudget, ResourcePool.count_finset_sum,
    Circuit.zEvent]

/-- Arbitrary durations charge one Z and at most one X at each physical position. -/
def samplingResetDepthLimit (duration : Resource.Event ResetModel → Nat) : Nat :=
  ∑ wire : Fin (PublicInput.terminal E exponentWidth).systemCount,
    resetWireDepth wire duration

/-- The selected actual reset path lies within the literal finite branch allowance. -/
theorem samplingReset_pool_le
    (path : (samplingReset E fieldTail exponentWidth sameWidth fits seed).Path) :
    (samplingReset E fieldTail exponentWidth sameWidth fits seed).resourcePool path ≤
      samplingResetBudget E exponentWidth :=
  Circuit.forRange_pool_le_sum _ _ _
    (fun wire iteration => resetWire_pool_le wire
      (samplingReset_qubits E exponentWidth wire)
      (samplingResetCells E exponentWidth wire)
      (samplingResetLabel E exponentWidth fieldTail sameWidth fits seed wire) iteration) path

/-- The complete arbitrary-duration bound follows the actual serial wire order. -/
theorem samplingReset_depth_le (duration : Resource.Event ResetModel → Nat)
    (path : (samplingReset E fieldTail exponentWidth sameWidth fits seed).Path) :
    (samplingReset E fieldTail exponentWidth sameWidth fits seed).depth duration path ≤
      samplingResetDepthLimit E exponentWidth duration :=
  Circuit.forRange_depth_le_sum _ _ duration _
    (fun wire iteration => resetWire_depth_le wire
      (samplingReset_qubits E exponentWidth wire)
      (samplingResetCells E exponentWidth wire)
      (samplingResetLabel E exponentWidth fieldTail sameWidth fits seed wire) duration iteration)
    path

/-- Unit depth is the selected serial reset trace, including any empty identity correction. -/
theorem samplingReset_unitDepth
    (path : (samplingReset E fieldTail exponentWidth sameWidth fits seed).Path) :
    (samplingReset E fieldTail exponentWidth sameWidth fits seed).depth (fun _ => 1) path =
      ∑ wire, (QuditShift.resetWireToBasis wire
        (samplingResetImplementations E exponentWidth wire)
        (samplingResetCells E exponentWidth wire)
        (samplingResetLabel E exponentWidth fieldTail sameWidth fits seed wire)).depth
          (fun _ => 1)
          (Circuit.forRangeComponentPath
            (PublicInput.terminal E exponentWidth).systemCount _ path wire) :=
  QuditShift.resetToBasisOn_unitDepth _ _ _ _ _ path

/-- A selected reset emits at most one Z and one native X per physical wire. -/
theorem samplingReset_eventCount_le
    (path : (samplingReset E fieldTail exponentWidth sameWidth fits seed).Path) :
    ((samplingReset E fieldTail exponentWidth sameWidth fits seed).eventTrace path).length ≤
      2 * (PublicInput.terminal E exponentWidth).systemCount := by
  have budget := samplingReset_pool_le E fieldTail exponentWidth sameWidth fits seed path
  have count := Multiset.card_le_card budget
  change ((samplingReset E fieldTail exponentWidth sameWidth fits seed).eventTrace path).length ≤
    (samplingResetBudget E exponentWidth).card at count
  simpa [samplingResetBudget, resetWireBudget, Multiset.card_sum, Finset.sum_const_zero,
    ResourcePool.singleton, Nat.mul_comm] using count

/-- Worst-case unit depth is two serial native events per physical wire. -/
theorem samplingReset_unitDepth_le
    (path : (samplingReset E fieldTail exponentWidth sameWidth fits seed).Path) :
    (samplingReset E fieldTail exponentWidth sameWidth fits seed).depth (fun _ => 1) path ≤
      2 * (PublicInput.terminal E exponentWidth).systemCount := by
  have bound := samplingReset_depth_le E fieldTail exponentWidth sameWidth fits seed
    (fun _ => 1) path
  simpa [samplingResetDepthLimit, resetWireDepth, Finset.sum_const_zero, Nat.mul_comm]
    using bound

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
