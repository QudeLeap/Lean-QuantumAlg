/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Even.Correction.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Cleanup.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Correction.Resources
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime

/-! # Exact native resources of the complete modular-doubling program and inverse -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

private lemma doubling_event_count
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus doublingProgram.eventCost =
      ResourcePool.count focus rotationProgram.eventCost +
        ResourcePool.count focus evenCorrectionProgram.eventCost +
          ResourcePool.count focus complementCarryProgram.eventCost +
            ResourcePool.count focus Correction.correctionProgram.eventCost +
              ResourcePool.count focus Cleanup.cleanupProgram.eventCost := by
  simp only [doublingProgram, rotationProgram, evenCorrectionProgram,
    complementCarryProgram, Correction.correctionProgram, Cleanup.cleanupProgram,
    programList_eventCost, ResourcePool.count_ofList, doublingGates,
    List.map_append, List.count_append]

private lemma rotation_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      rotationProgram.eventCost = 0 := by
  rw [rotationProgram, programList_toffoli_count_eq_sum]
  exact EncodedBit.Word.adjacentShiftLeftGates_toffoliMultiplicity_sum
    targetWord targetWord_distinct

private lemma rotation_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      rotationProgram.eventCost = 0 := by
  rw [rotationProgram, programList_x_count_eq_sum]
  exact EncodedBit.Word.adjacentShiftLeftGates_xMultiplicity_sum targetWord targetWord_distinct

private lemma evenCorrection_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      evenCorrectionProgram.eventCost = 0 := by
  rw [evenCorrection_event_count]
  simp only [suffixIncrement_eventCost, MAU.Addition.HRS.hrsControlledBorrowedIncrement_x_count]

private lemma correction_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      Correction.correctionProgram.eventCost = 0 := by
  have first : ([.gate .cnot] : List (Resource.Event (.quantum AlgorithmGate.model .empty))).count
      (.gate .singleQubit) = 0 := by decide
  simpa only [first, suffixIncrement_eventCost,
    MAU.Addition.HRS.hrsControlledBorrowedIncrement_x_count, Nat.zero_add] using
      Correction.correction_event_count (.gate .singleQubit)

/-- Rotation, both sparse corrections, carry and complete flag cleanup are all paid. -/
lemma doubling_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      doublingProgram.eventCost = 2179 := by
  rw [doubling_event_count, rotation_cnot_count, evenCorrection_cnot_count,
    complementCarry_cnot_count, Correction.correction_cnot_count, Cleanup.cleanup_cnot_count]

/-- This count includes every original dirty-source repair and actual controlled comparison. -/
lemma doubling_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      doublingProgram.eventCost = 18267 := by
  rw [doubling_event_count, rotation_toffoli_count, evenCorrection_toffoli_count,
    complementCarry_toffoli_count, Correction.correction_toffoli_count,
    Cleanup.cleanup_toffoli_count]

/-- The carry's actual X instructions remain in the complete original program. -/
lemma doubling_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      doublingProgram.eventCost = 508 := by
  rw [doubling_event_count, rotation_x_count, evenCorrection_x_count,
    complementCarry_x_count, correction_x_count, Cleanup.cleanup_x_count]

private lemma doubling_length : doublingGates.length = 20954 := by
  have counted : primitiveEventCount doublingProgram = doublingGates.length :=
    primitiveEventCount_programList
      (layout := QubitLayout.canonical encoding.width) (oracles := .empty) doublingGates
  have coordinates : primitiveEventCount doublingProgram = 20954 := by
    rw [primitiveEventCount, doubling_x_count, doubling_cnot_count, doubling_toffoli_count]
  exact counted.symm.trans coordinates

/-- Quantum duration is derived from every actual sequential native instruction. -/
lemma doubling_quantumTime :
    doublingProgram.evaluatedEventDepth Resource.Event.quantumDuration = 20954 :=
  (programList_quantumTime (QubitLayout.canonical encoding.width) .empty doublingGates).trans
    doubling_length

private lemma inverseDoubling_event_count
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus inverseDoublingProgram.eventCost =
      ResourcePool.count focus doublingProgram.eventCost := by
  simp only [inverseDoublingProgram, doublingProgram, programList_eventCost,
    ResourcePool.count_ofList, inverseDoublingGates, List.map_reverse, List.count_reverse]

/-- Source restoration executes the entire literal inverse and pays its whole CNOT ledger. -/
lemma inverseDoubling_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      inverseDoublingProgram.eventCost = 2179 := by
  rw [inverseDoubling_event_count, doubling_cnot_count]

/-- No forward Toffoli is omitted from the complete inverse restoration cost. -/
lemma inverseDoubling_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      inverseDoublingProgram.eventCost = 18267 := by
  rw [inverseDoubling_event_count, doubling_toffoli_count]

/-- Complete source restoration retains every original one-qubit instruction. -/
lemma inverseDoubling_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      inverseDoublingProgram.eventCost = 508 := by
  rw [inverseDoubling_event_count, doubling_x_count]

/-- All forward native duration is paid again by the complete actual adjoint. -/
lemma inverseDoubling_quantumTime :
    inverseDoublingProgram.evaluatedEventDepth Resource.Event.quantumDuration = 20954 := by
  have length : inverseDoublingGates.length = 20954 := by
    rw [inverseDoublingGates, List.length_reverse]
    exact doubling_length
  exact (programList_quantumTime (QubitLayout.canonical encoding.width) .empty
    inverseDoublingGates).trans length

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling
