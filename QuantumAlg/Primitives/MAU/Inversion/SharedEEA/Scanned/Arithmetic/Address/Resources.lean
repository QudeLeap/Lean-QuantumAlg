/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Address.Remainder
import all QuantumAlg.Primitives.MAU.Addition.TTK.Placement.Resources
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime

/-! # Native resources of the actual complete three-subtraction metadata preparation -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress

noncomputable section

open EncodedBit NumberTheory.SharedEEA

private lemma constantProgram_toffoli_count (width : Nat)
    (constant : BitVec (ScanMetadata.addressWidth width)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (constantProgram width constant).eventCost = 0 := by
  rw [constantProgram, Word.xorConstantProgram, GateSpec.programList_toffoli_count_eq_sum,
    Word.xorConstantGates_toffoliMultiplicity_sum]

private lemma constantProgram_cnot_count (width : Nat)
    (constant : BitVec (ScanMetadata.addressWidth width)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (constantProgram width constant).eventCost = 0 := by
  rw [constantProgram, Word.xorConstantProgram, GateSpec.programList_cnot_count_eq_sum,
    Word.xorConstantGates_cnotMultiplicity_sum]

private lemma constantProgram_quantumTime (width : Nat)
    (constant : BitVec (ScanMetadata.addressWidth width)) :
    (constantProgram width constant).evaluatedEventDepth Resource.Event.quantumDuration =
      (Word.constantOneIndices constant.toFin).length := by
  rw [constantProgram, Word.xorConstantProgram, GateSpec.programList_quantumTime,
    Word.xorConstantGates_length]

/-- The actual complete metadata inverse retains its physical placed native Toffoli count. -/
lemma subtractProgram_toffoli_count (width : Nat) (positive : 1 ≤ width)
    (field : ArithmeticGeometry.Field) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (subtractProgram width positive field).eventCost =
        2 * (ScanMetadata.addressWidth width - 1) :=
  (placement width positive field).subtractProgram_toffoli_count

/-- Every native CNOT of the complete inverse is retained on the same original physical words. -/
lemma subtractProgram_cnot_count (width : Nat) (positive : 1 ≤ width)
    (field : ArithmeticGeometry.Field) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (subtractProgram width positive field).eventCost =
        ScanMetadata.addressWidth width + 2 * (ScanMetadata.addressWidth width - 1) +
          2 * (ScanMetadata.addressWidth width - 2) :=
  (placement width positive field).subtractProgram_cnot_count

/-- The actual native inverse uses the support-certified parallel TTK dependency schedule. -/
lemma subtractProgram_quantumTime_le (width : Nat) (positive : 1 ≤ width)
    (field : ArithmeticGeometry.Field) (enough : 2 ≤ ScanMetadata.addressWidth width) :
    (subtractProgram width positive field).evaluatedEventDepth Resource.Event.quantumDuration ≤
      5 * (ScanMetadata.addressWidth width) - 5 :=
  (placement width positive field).subtractProgram_quantumTime_le enough

/-- All three full metadata subtraction words are charged in the actual source sequence. -/
lemma remainderProgram_toffoli_count (width : Nat) (positive : 1 ≤ width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (remainderProgram width positive).eventCost = 6 * (ScanMetadata.addressWidth width - 1) := by
  simp only [remainderProgram, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    constantProgram_toffoli_count, subtractProgram_toffoli_count]
  omega

/-- The public constant loader adds no CNOT to the three complete native subtractions. -/
lemma remainderProgram_cnot_count (width : Nat) (positive : 1 ≤ width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (remainderProgram width positive).eventCost =
        3 * (ScanMetadata.addressWidth width + 2 * (ScanMetadata.addressWidth width - 1) +
          2 * (ScanMetadata.addressWidth width - 2)) := by
  simp only [remainderProgram, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    constantProgram_cnot_count, subtractProgram_cnot_count]
  omega

/-- Actual default time retains three source parallel schedules and every public-load X gate. -/
lemma remainderProgram_quantumTime_le (width : Nat) (positive : 1 ≤ width)
    (enough : 2 ≤ ScanMetadata.addressWidth width) :
    (remainderProgram width positive).evaluatedEventDepth Resource.Event.quantumDuration ≤
      (Word.constantOneIndices (remainderConstant width).toFin).length +
        3 * (5 * (ScanMetadata.addressWidth width) - 5) := by
  have first := subtractProgram_quantumTime_le width positive .coefficient enough
  have second := subtractProgram_quantumTime_le width positive .quotient enough
  have third := subtractProgram_quantumTime_le width positive .shift enough
  simp only [remainderProgram, UnitaryCircuit.evaluatedEventDepth_seq,
    constantProgram_quantumTime]
  omega

/-- These exact P-256 native counts belong to the actual full metadata preparation. -/
lemma p256_remainderProgram_counts :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (remainderProgram 256 (by decide)).eventCost = 54 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (remainderProgram 256 (by decide)).eventCost = 132 := by
  rw [remainderProgram_toffoli_count, remainderProgram_cnot_count]
  decide

/-- P-256 duration follows the actual parallel native metadata dependencies. -/
lemma p256_remainderProgram_quantumTime_le :
    (remainderProgram 256 (by decide)).evaluatedEventDepth Resource.Event.quantumDuration ≤
      137 := by
  have actual := remainderProgram_quantumTime_le 256 (by decide) (by decide)
  have numeric : (Word.constantOneIndices (remainderConstant 256).toFin).length +
      3 * (5 * (ScanMetadata.addressWidth 256) - 5) = 137 := by decide
  exact numeric ▸ actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress
