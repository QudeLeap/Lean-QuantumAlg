/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Layout
import all QuantumAlg.Primitives.MAU.Addition.HRS.Carry.Resources
import all QuantumAlg.Components.Encoded.BitGates.Realization

/-!
# Native P-256 complement carry on the complete two-word frame

Every borrowed carry wire is an actual addressed bit of the preserved
quantum addend. The compiled list retains the complete existing complement
and the original HRS carry's exact relative phases and native occurrences.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition

noncomputable section

open QuantumAlg.EncodedBit GateSpec

def complementWord : Fin (2 ^ width) := ⟨complement, complement_lt_capacity⟩

/-- The actual HRS carry instructions, each relocated to the fixed two-word frame. -/
def complementCarryGates : List (GateSpec encoding) :=
  (MAU.Addition.HRS.carryGates width complementWord).map
    (carrySubsystem.placeGate carryEncoding_onto encoding_onto)

/-- Compile precisely the relocated native instructions, without allocating a helper word. -/
def complementCarryProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical encoding.width).toQuantum :=
  programList (QubitLayout.canonical _) .empty complementCarryGates

/-- Exact coordinate action of the existing carry on its actual selected subsystem. -/
def complementCarryStep (state : Registers) : Registers :=
  (carrySubsystem.full carryEncoding_onto encoding_onto).step
    (fun pair => (MAU.Addition.HRS.carryOutput width complementWord pair.1, pair.2)) state

lemma complementCarryGates_step (state : Registers) :
    stepList complementCarryGates state = complementCarryStep state := by
  simpa only [complementCarryGates, complementCarryStep, MAU.Addition.HRS.hrsCarry_step] using
    carrySubsystem.placeGates_step carryEncoding_onto encoding_onto
      (MAU.Addition.HRS.carryGates width complementWord) state

/-- The same actual native program has the exact full-frame carry action. -/
lemma complementCarry_realizes (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes encoding complementCarryProgram environment complementCarryStep :=
  realizesList_congrStep (QubitLayout.canonical _) .empty complementCarryGates
    complementCarryGates_step environment

/-- Every native occurrence is inherited from the actual constant-carry list. -/
lemma complementCarry_events :
    complementCarryGates.map (event .empty) =
      (MAU.Addition.HRS.carryGates width complementWord).map (event .empty) := by
  simp only [complementCarryGates, List.map_map]
  apply List.map_congr_left
  intro gate _present
  exact carrySubsystem.placeGate_event carryEncoding_onto encoding_onto .empty gate

/-- The same literal occurrences give the same complete native ledger. -/
lemma complementCarry_eventCost : complementCarryProgram.eventCost =
    (MAU.Addition.HRS.carryProgram width complementWord).eventCost := by
  rw [complementCarryProgram, MAU.Addition.HRS.carryProgram,
    programList_eventCost, programList_eventCost, complementCarry_events]

private lemma highCount_add (constant start count : Nat) :
    MAU.Addition.HRS.highConstantCount constant (start + count) =
      MAU.Addition.HRS.highConstantCount constant start +
        MAU.Addition.HRS.highConstantCount (constant / 2 ^ start) count := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [Nat.add_succ, MAU.Addition.HRS.highConstantCount,
        MAU.Addition.HRS.highConstantCount, inductionHypothesis]
      have position : start + count + 1 = (count + 1) + start := by omega
      rw [position, Nat.testBit_add, Nat.add_assoc]

private lemma complement_highCount255 :
    MAU.Addition.HRS.highConstantCount complement 255 = 127 := by
  have first : MAU.Addition.HRS.highConstantCount complement 64 = 0 := by decide
  have second : MAU.Addition.HRS.highConstantCount (complement / 2 ^ 64) 64 = 33 := by decide
  have third : MAU.Addition.HRS.highConstantCount (complement / 2 ^ 128) 64 = 63 := by decide
  have fourth : MAU.Addition.HRS.highConstantCount (complement / 2 ^ 192) 63 = 31 := by decide
  rw [highCount_add complement 192 63, highCount_add complement 128 64,
    highCount_add complement 64 64, first, second, third, fourth]

private lemma complement_highCount254 :
    MAU.Addition.HRS.highConstantCount complement 254 = 127 := by
  have lastBit : complement.testBit 255 = false := by decide
  have recurrence (constant count : Nat) :
      MAU.Addition.HRS.highConstantCount constant (count + 1) =
        MAU.Addition.HRS.highConstantCount constant count +
          (constant.testBit (count + 1)).toNat := rfl
  have same : MAU.Addition.HRS.highConstantCount complement 255 =
      MAU.Addition.HRS.highConstantCount complement 254 := by
    have next := recurrence complement 254
    simp only [lastBit, Bool.toNat_false, Nat.add_zero] at next
    exact next
  exact same.symm.trans complement_highCount255

section

-- Normalize only the fixed word-width parameter when applying the generic native count laws.
attribute [local implicit_reducible] width

/-- The P-256 sparse complement determines exactly 254 native CNOT occurrences. -/
lemma complementCarry_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      complementCarryProgram.eventCost = 254 := by
  rw [complementCarry_eventCost]
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
    (MAU.Addition.HRS.carryProgram (254 + 2) complementWord).eventCost = 254
  rw [MAU.Addition.HRS.hrsCarry_cnot_count]
  dsimp only [complementWord]
  rw [complement_highCount255, complement_highCount254]

/-- Every selected constant bit contributes the two actually emitted X gates. -/
lemma complementCarry_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      complementCarryProgram.eventCost = 508 := by
  rw [complementCarry_eventCost]
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
    (MAU.Addition.HRS.carryProgram (254 + 2) complementWord).eventCost = 508
  rw [MAU.Addition.HRS.hrsCarry_x_count]
  dsimp only [complementWord]
  rw [complement_highCount255, complement_highCount254]

/-- Both actual carry traversals have exactly 1016 native Toffoli occurrences. -/
lemma complementCarry_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      complementCarryProgram.eventCost = 1016 := by
  rw [complementCarry_eventCost]
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
    (MAU.Addition.HRS.carryProgram (254 + 2) complementWord).eventCost = 1016
  rw [MAU.Addition.HRS.hrsCarry_toffoli_count]
  decide

end

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition
