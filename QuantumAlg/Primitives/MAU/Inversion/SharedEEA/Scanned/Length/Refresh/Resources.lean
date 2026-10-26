/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Refresh
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Write.Resources

/-! # Complete actual four-write P-256 length refresh resources -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthRefresh

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- All four complete same-pool writers are charged in their actual original source order. -/
lemma p256_program_toffoli_count_le
    (capacity : 256 + 3 ≤ 2 ^ ScanMetadata.addressWidth 256) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program 256 capacity).eventCost ≤ 82024 := by
  have first := LengthRefreshWrite.p256_program_toffoli_count_le .coefficient false capacity
  have second := LengthRefreshWrite.p256_program_toffoli_count_le .coefficient true capacity
  have third := LengthRefreshWrite.p256_program_toffoli_count_le .divisor true capacity
  have fourth := LengthRefreshWrite.p256_program_toffoli_count_le .divisor false capacity
  simp only [program, UnitaryCircuit.seq_eventCost, ResourcePool.count_add]
  omega

/-- The complete CNOT bound includes two coefficient and two divisor writer costs. -/
lemma p256_program_cnot_count_le
    (capacity : 256 + 3 ≤ 2 ^ ScanMetadata.addressWidth 256) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program 256 capacity).eventCost ≤ 45228 := by
  have first := LengthRefreshWrite.p256_program_cnot_count_le .coefficient false capacity
  have second := LengthRefreshWrite.p256_program_cnot_count_le .coefficient true capacity
  have third := LengthRefreshWrite.p256_program_cnot_count_le .divisor true capacity
  have fourth := LengthRefreshWrite.p256_program_cnot_count_le .divisor false capacity
  have budgets : LengthAlignment.publicBudget 256 .coefficient = 0 ∧
      LengthAlignment.publicBudget 256 .divisor = 777 := by decide
  simp only [budgets.1, budgets.2] at first second third fourth
  simp only [program, UnitaryCircuit.seq_eventCost, ResourcePool.count_add]
  omega

/-- Serial composition retains the internal native dependency schedules of all four writers. -/
lemma p256_program_quantumTime_le
    (capacity : 256 + 3 ≤ 2 ^ ScanMetadata.addressWidth 256) :
    (program 256 capacity).evaluatedEventDepth Resource.Event.quantumDuration ≤ 160732 := by
  have first := LengthRefreshWrite.p256_program_quantumTime_le .coefficient false capacity
  have second := LengthRefreshWrite.p256_program_quantumTime_le .coefficient true capacity
  have third := LengthRefreshWrite.p256_program_quantumTime_le .divisor true capacity
  have fourth := LengthRefreshWrite.p256_program_quantumTime_le .divisor false capacity
  have budgets : LengthAlignment.publicBudget 256 .coefficient = 0 ∧
      LengthAlignment.publicBudget 256 .divisor = 777 := by decide
  simp only [budgets.1, budgets.2] at first second third fourth
  simp only [program, UnitaryCircuit.evaluatedEventDepth_seq]
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthRefresh
