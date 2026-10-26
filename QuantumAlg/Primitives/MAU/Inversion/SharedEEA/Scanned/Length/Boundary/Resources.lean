/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Boundary.Program
import all QuantumAlg.Primitives.MAU.Addition.TTK.Placement.Resources
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime

/-! # Native resources of the real public boundary load and full-width subtraction -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthBoundary

noncomputable section

open EncodedBit NumberTheory.SharedEEA LengthCoordinates

/-- One actual X occurs at each set bit of the public boundary constant. -/
def constantWeight (width : Nat) (field : Field) : Nat :=
  (Word.constantOneIndices (constant width field).toFin).length

private lemma constantProgram_toffoli_count (width : Nat) (field : Field) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (constantProgram width field).eventCost = 0 := by
  rw [constantProgram, Word.xorConstantProgram, GateSpec.programList_toffoli_count_eq_sum,
    Word.xorConstantGates_toffoliMultiplicity_sum]

private lemma constantProgram_cnot_count (width : Nat) (field : Field) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (constantProgram width field).eventCost = 0 := by
  rw [constantProgram, Word.xorConstantProgram, GateSpec.programList_cnot_count_eq_sum,
    Word.xorConstantGates_cnotMultiplicity_sum]

/-- The actual constant load contributes no Toffoli; the whole placed inverse is charged. -/
lemma prepareProgram_toffoli_count (width : Nat) (field : Field) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (prepareProgram width field).eventCost = 2 * (ScanMetadata.addressWidth width - 1) := by
  rw [prepareProgram, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    constantProgram_toffoli_count, (placement width field).subtractProgram_toffoli_count,
    Nat.zero_add]

/-- Native CNOTs are exactly those of the complete physical inverse subtraction. -/
lemma prepareProgram_cnot_count (width : Nat) (field : Field) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (prepareProgram width field).eventCost =
        ScanMetadata.addressWidth width + 2 * (ScanMetadata.addressWidth width - 1) +
          2 * (ScanMetadata.addressWidth width - 2) := by
  rw [prepareProgram, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    constantProgram_cnot_count, (placement width field).subtractProgram_cnot_count, Nat.zero_add]

private lemma constantProgram_quantumTime (width : Nat) (field : Field) :
    (constantProgram width field).evaluatedEventDepth Resource.Event.quantumDuration =
      constantWeight width field := by
  rw [constantProgram, Word.xorConstantProgram, GateSpec.programList_quantumTime,
    Word.xorConstantGates_length]
  rfl

/-- Actual default duration retains the placed parallel subtraction and paid public loader. -/
lemma prepareProgram_quantumTime_le (width : Nat) (field : Field)
    (enough : 2 ≤ ScanMetadata.addressWidth width) :
    (prepareProgram width field).evaluatedEventDepth Resource.Event.quantumDuration ≤
      constantWeight width field + (5 * ScanMetadata.addressWidth width - 5) := by
  rw [prepareProgram, UnitaryCircuit.evaluatedEventDepth_seq, constantProgram_quantumTime]
  exact Nat.add_le_add_left ((placement width field).subtractProgram_quantumTime_le enough) _

/-- Exact P256 boundary preparation native Toffoli count, independent of the selected field. -/
lemma p256_prepareProgram_toffoli_count (field : Field) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (prepareProgram 256 field).eventCost = 18 := by
  rw [prepareProgram_toffoli_count]
  decide

/-- Exact P256 boundary preparation native CNOT count, independent of the selected field. -/
lemma p256_prepareProgram_cnot_count (field : Field) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (prepareProgram 256 field).eventCost = 44 := by
  rw [prepareProgram_cnot_count]
  decide

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthBoundary
