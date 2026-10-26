/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Prepare
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Alignment.Resources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Encoder.Resources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Clip.Resources

/-! # Native P-256 resources of complete actual length preparation -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthPrepare

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

/-- Every real alignment, borrowed encoder and full clipping Toffoli is included. -/
lemma p256_program_toffoli_count_le (field : Field) (first : Bool)
    (capacity : 256 + 3 ≤ 2 ^ ScanMetadata.addressWidth 256) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program 256 field first capacity).eventCost ≤ 10235 := by
  have alignment := (LengthAlignment.program_resources 256 field first).1
  have encoder := (LengthEncoder.p256_counts field first capacity).1
  rw [program, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    ResourcePool.count_add, ResourcePool.count_add, encoder,
    LengthClip.p256_prepareProgram_toffoli_count]
  have numeric : (256 + 3) * (256 : Nat).size = 2331 := by decide
  rw [numeric] at alignment
  omega

/-- Both real public divisor rotations are kept separate from the shared source-independent cost. -/
lemma p256_program_cnot_count_le (field : Field) (first : Bool)
    (capacity : 256 + 3 ≤ 2 ^ ScanMetadata.addressWidth 256) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program 256 field first capacity).eventCost ≤
        5265 + LengthAlignment.publicBudget 256 field := by
  have alignment := (LengthAlignment.program_resources 256 field first).2.1
  have encoder := (LengthEncoder.p256_counts field first capacity).2.1
  rw [program, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    ResourcePool.count_add, ResourcePool.count_add, encoder,
    LengthClip.p256_prepareProgram_cnot_count]
  have numeric : 2 * (256 + 3) * (256 : Nat).size = 4662 := by decide
  rw [numeric] at alignment
  omega

/-- Actual dependency duration includes native public exchanges and every paid preparation stage. -/
lemma p256_program_quantumTime_le (field : Field) (first : Bool)
    (capacity : 256 + 3 ≤ 2 ^ ScanMetadata.addressWidth 256) :
    (program 256 field first capacity).evaluatedEventDepth Resource.Event.quantumDuration ≤
      19684 + LengthAlignment.publicBudget 256 field := by
  have alignment := (LengthAlignment.program_resources 256 field first).2.2
  have clipping := LengthClip.p256_prepareProgram_quantumTime_le field
  have encoder := LengthEncoder.p256_quantumTime field first capacity
  rw [program, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_seq, encoder]
  have numeric : 3 * (256 + 3) * (256 : Nat).size = 6993 := by decide
  rw [numeric] at alignment
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthPrepare
