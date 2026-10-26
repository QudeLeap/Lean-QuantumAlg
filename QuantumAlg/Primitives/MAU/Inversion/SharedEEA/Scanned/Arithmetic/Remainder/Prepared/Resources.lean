/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Prepared
import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Window.Resources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Address.Resources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Resources
import all QuantumAlg.Components.Encoded.BitGates.Predicate.Compute.Resources

/-! # Actual resources of complete remainder address/alignment/arithmetic/uncompute -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderAddress

noncomputable section

open EncodedBit

private lemma p256_prepare_toffoli_count_le :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (prepareProgram 256 (by decide)).eventCost ≤ 4716 := by
  have address := ArithmeticAddress.p256_remainderProgram_counts.1
  have alignment := (ArithmeticAlignment.p256_pairProgram_resources .shift).1
  rw [prepareProgram, UnitaryCircuit.seq_eventCost, ResourcePool.count_add, address]
  omega

private lemma p256_prepare_cnot_count_le :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (prepareProgram 256 (by decide)).eventCost ≤ 9456 := by
  have address := ArithmeticAddress.p256_remainderProgram_counts.2
  have alignment := (ArithmeticAlignment.p256_pairProgram_resources .shift).2.1
  rw [prepareProgram, UnitaryCircuit.seq_eventCost, ResourcePool.count_add, address]
  omega

private lemma p256_prepare_quantumTime_le :
    (prepareProgram 256 (by decide)).evaluatedEventDepth Resource.Event.quantumDuration ≤
      14123 := by
  have address := ArithmeticAddress.p256_remainderProgram_quantumTime_le
  have alignment := (ArithmeticAlignment.p256_pairProgram_resources .shift).2.2
  rw [prepareProgram, UnitaryCircuit.evaluatedEventDepth_seq]
  omega

/-- Full native preparation and its entire actual inverse surround the real arithmetic body. -/
lemma p256_program_toffoli_count_le (signed : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program 256 (by decide) signed).eventCost ≤
        9432 + (if signed then 7839 else 6545) := by
  have preparation := p256_prepare_toffoli_count_le
  rw [program, PredicateCompute.program_eventCost, ResourcePool.count_add,
    ResourcePool.count_nsmul, RemainderWindow.p256_program_toffoli_count]
  omega

/-- Both paid address/alignment words and every arithmetic CNOT remain in the actual ledger. -/
lemma p256_program_cnot_count_le (signed : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program 256 (by decide) signed).eventCost ≤ 22068 := by
  have preparation := p256_prepare_cnot_count_le
  rw [program, PredicateCompute.program_eventCost, ResourcePool.count_add,
    ResourcePool.count_nsmul, RemainderWindow.p256_program_cnot_count]
  exact (Nat.add_le_add_right (Nat.mul_le_mul_left 2 preparation) 3156).trans (by decide)

/-- Actual duration includes full address cleanup and both real common-control barrels. -/
lemma p256_program_quantumTime_le (signed : Bool) :
    (program 256 (by decide) signed).evaluatedEventDepth Resource.Event.quantumDuration ≤
      28246 + (if signed then 14187 else 12893) := by
  have preparation := p256_prepare_quantumTime_le
  rw [program, PredicateCompute.program_quantumTime, RemainderWindow.p256_program_quantumTime]
  omega

/-- Both real preparations retain their public loader X gates and the complete arithmetic scan X. -/
lemma p256_program_singleQubit_count (signed : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program 256 (by decide) signed).eventCost = 3196 := by
  rw [program, EncodedBit.PredicateCompute.program_eventCost,
    ResourcePool.count_add, ResourcePool.count_nsmul, prepareProgram,
    UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    ArithmeticAddress.p256_remainderProgram_singleQubit_count,
    ArithmeticAlignment.pairProgram_singleQubit_count,
    RemainderWindow.p256_program_singleQubit_count]


end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderAddress
