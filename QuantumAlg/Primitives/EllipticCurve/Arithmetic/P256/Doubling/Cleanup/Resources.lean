/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Cleanup.Program

/-! # Actual native counts of original-wire doubling cleanup -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling.Cleanup

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

private lemma comparison_events :
    comparisonGates.map (GateSpec.event .empty) =
      (MAU.Addition.HRS.carryGates highWidth comparisonConstant).map (GateSpec.event .empty) := by
  rw [comparisonGates, List.map_map]
  apply List.map_congr_left
  intro gate _present
  exact comparisonSubsystem.placeGate_event high_onto encoding_onto .empty gate

private lemma comparison_eventCost :
    (programList (QubitLayout.canonical encoding.width) .empty comparisonGates).eventCost =
      (MAU.Addition.HRS.carryProgram highWidth comparisonConstant).eventCost := by
  rw [MAU.Addition.HRS.carryProgram, programList_eventCost, programList_eventCost,
    comparison_events]

private lemma highCount_add (constant start count : Nat) :
    MAU.Addition.HRS.highConstantCount constant (start + count) =
      MAU.Addition.HRS.highConstantCount constant start +
        MAU.Addition.HRS.highConstantCount (constant / 2 ^ start) count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [Nat.add_succ, MAU.Addition.HRS.highConstantCount,
        MAU.Addition.HRS.highConstantCount, ih]
      have position : start + count + 1 = (count + 1) + start := by omega
      rw [position, Nat.testBit_add, Nat.add_assoc]

private lemma comparison_highCount254 :
    MAU.Addition.HRS.highConstantCount comparisonConstant.val 254 = 34 := by
  have first : MAU.Addition.HRS.highConstantCount comparisonConstant.val 64 = 0 := by decide
  have second : MAU.Addition.HRS.highConstantCount
      (comparisonConstant.val / 2 ^ 64) 64 = 1 := by decide
  have third : MAU.Addition.HRS.highConstantCount
      (comparisonConstant.val / 2 ^ 128) 64 = 1 := by decide
  have fourth : MAU.Addition.HRS.highConstantCount
      (comparisonConstant.val / 2 ^ 192) 62 = 32 := by decide
  rw [highCount_add comparisonConstant.val 192 62,
    highCount_add comparisonConstant.val 128 64,
    highCount_add comparisonConstant.val 64 64, first, second, third, fourth]

private lemma highCount_predecessor (constant count total : Nat)
    (current : MAU.Addition.HRS.highConstantCount constant (count + 1) = total)
    (last : constant.testBit (count + 1) = true) :
    MAU.Addition.HRS.highConstantCount constant count + 1 = total := by
  rw [MAU.Addition.HRS.highConstantCount, last] at current
  exact current

private lemma comparison_highCount253 :
    MAU.Addition.HRS.highConstantCount comparisonConstant.val 253 = 33 := by
  have high : comparisonConstant.val.testBit 254 = true := by decide
  have next := highCount_predecessor comparisonConstant.val 253 34 comparison_highCount254 high
  omega

private lemma comparison_cnot_sum : (comparisonGates.map cnotMultiplicity).sum = 67 := by
  rw [← programList_cnot_count_eq_sum
    (layout := QubitLayout.canonical encoding.width) (oracles := .empty), comparison_eventCost]
  rw [MAU.Addition.HRS.hrsCarry_cnot_count, comparison_highCount254,
    comparison_highCount253]

private lemma comparison_x_sum : (comparisonGates.map xMultiplicity).sum = 134 := by
  rw [← programList_x_count_eq_sum
    (layout := QubitLayout.canonical encoding.width) (oracles := .empty), comparison_eventCost]
  rw [MAU.Addition.HRS.hrsCarry_x_count, comparison_highCount254,
    comparison_highCount253]

private lemma comparison_toffoli_sum :
    (comparisonGates.map toffoliMultiplicity).sum = 1010 := by
  rw [← programList_toffoli_count_eq_sum
    (layout := QubitLayout.canonical encoding.width) (oracles := .empty), comparison_eventCost]
  rw [MAU.Addition.HRS.hrsCarry_toffoli_count]
  decide

/-- Native X leaves become controlled CNOTs; the final low-bit XOR is also paid. -/
lemma cleanup_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      cleanupProgram.eventCost = 135 := by
  rw [cleanupProgram, programList_cnot_count_eq_sum, cleanupGates,
    List.map_append, List.sum_append, selectedComparisonGates,
    listWithDirtyControl_cnotMultiplicity_sum, comparison_x_sum]
  rfl

/-- Every dirty-work repair is included in the four-Toffoli control lowering. -/
lemma cleanup_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      cleanupProgram.eventCost = 4107 := by
  rw [cleanupProgram, programList_toffoli_count_eq_sum, cleanupGates,
    List.map_append, List.sum_append, selectedComparisonGates,
    listWithDirtyControl_toffoliMultiplicity_sum, comparison_cnot_sum,
    comparison_toffoli_sum]
  rfl

/-- The selected comparison has no remaining uncontrolled X leaf. -/
lemma cleanup_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      cleanupProgram.eventCost = 0 := by
  rw [cleanupProgram, programList_x_count_eq_sum, cleanupGates,
    List.map_append, List.sum_append, selectedComparisonGates,
    listWithDirtyControl_xMultiplicity_sum]
  rfl

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling.Cleanup
