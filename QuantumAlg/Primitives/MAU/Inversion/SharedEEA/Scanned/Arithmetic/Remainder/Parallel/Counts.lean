/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Parallel.Program
import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Parallel.Counts
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Address.Resources
import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Window.Resources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Components
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources.Empty

/-!
# Direct native ledger of the actual complete paired remainder arithmetic

Both actual preparations and the unchanged full arithmetic window are
charged. The exact new alignment pool is inserted directly; no resource
equality to a legacy remainder executor supplies a bound. Genuine shared
address/window components retain their existing independent ledgers.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderAddress.Parallel

noncomputable section

open EncodedBit

/-- Exact actual preparation pool, including the full paid metadata address. -/
lemma prepareProgram_nativePool (width : Nat) (positive : 1 ≤ width) :
    (prepareProgram width positive).eventCost =
      (ArithmeticAddress.remainderProgram width positive).eventCost +
        ResourcePool.scale (PermutationBarrelParallel.exchangeCount
          (ArithmeticAlignment.permutation width) (PermutationBarrel.binaryStages width.size))
          (PermutationParallel.nativePairPool .empty) := by
  rw [prepareProgram, UnitaryCircuit.seq_eventCost,
    ArithmeticAlignment.Parallel.pairProgram_nativePool]

/-- Both real preparation directions and the entire native window occur in the same ledger. -/
lemma program_nativePool (width : Nat) (positive : 1 ≤ width) (signed : Bool) :
    (program width positive signed).eventCost =
      2 • ((ArithmeticAddress.remainderProgram width positive).eventCost +
        ResourcePool.scale (PermutationBarrelParallel.exchangeCount
          (ArithmeticAlignment.permutation width) (PermutationBarrel.binaryStages width.size))
          (PermutationParallel.nativePairPool .empty)) +
        (RemainderWindow.program width signed).eventCost := by
  rw [program, PredicateCompute.program_eventCost, prepareProgram_nativePool]

/-- This same unitary's actual native adjoint retains all native occurrences. -/
lemma inverseProgram_nativePool (width : Nat) (positive : 1 ≤ width) (signed : Bool) :
    (inverseProgram width positive signed).eventCost =
      (program width positive signed).eventCost := by
  rw [inverseProgram, AlgorithmGate.algorithmGate_emptyAdjoints_eventCost]

/-- Both actual source modes have the same corresponding full forward native ledger. -/
lemma bodyProgram_nativePool (width : Nat) (positive : 1 ≤ width) (signed : Bool) :
    (bodyProgram width positive signed).eventCost =
      (program width positive signed).eventCost := by
  cases signed
  · rfl
  · exact inverseProgram_nativePool width positive true

private lemma p256_prepare_counts_direct :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (prepareProgram 256 (by decide)).eventCost ≤ 4716 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (prepareProgram 256 (by decide)).eventCost ≤ 9456 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (prepareProgram 256 (by decide)).eventCost = 2 := by
  have address := ArithmeticAddress.p256_remainderProgram_counts
  have alignment := ArithmeticAlignment.Parallel.p256_pairProgram_counts_direct .shift
  have addressSingle := ArithmeticAddress.p256_remainderProgram_singleQubit_count
  simp only [prepareProgram, UnitaryCircuit.seq_eventCost, ResourcePool.count_add]
  exact ⟨by omega, by omega, by omega⟩

/-- Toffoli cap retains both full actual preparations and the original arithmetic mode. -/
lemma p256_program_toffoli_direct (signed : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program 256 (by decide) signed).eventCost ≤
        9432 + (if signed then 7839 else 6545) := by
  have preparation := p256_prepare_counts_direct.1
  rw [program, PredicateCompute.program_eventCost, ResourcePool.count_add,
    ResourcePool.count_nsmul, RemainderWindow.p256_program_toffoli_count]
  omega

/-- Every actual CNOT is retained independently of the unchanged Toffoli cap. -/
lemma p256_program_cnot_direct (signed : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program 256 (by decide) signed).eventCost ≤ 22068 := by
  have preparation := p256_prepare_counts_direct.2.1
  rw [program, PredicateCompute.program_eventCost, ResourcePool.count_add,
    ResourcePool.count_nsmul, RemainderWindow.p256_program_cnot_count]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 preparation) 3156

/-- Exact native one-qubit multiplicity includes both loader masks and the entire window. -/
lemma p256_program_singleQubit_direct (signed : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program 256 (by decide) signed).eventCost = 3196 := by
  rw [program, PredicateCompute.program_eventCost, ResourcePool.count_add,
    ResourcePool.count_nsmul, p256_prepare_counts_direct.2.2,
    RemainderWindow.p256_program_singleQubit_count]

private lemma p256_prepare_time_direct :
    (prepareProgram 256 (by decide)).evaluatedEventDepth Resource.Event.quantumDuration ≤
      9461 := by
  have address := ArithmeticAddress.p256_remainderProgram_quantumTime_le
  have alignment := ArithmeticAlignment.Parallel.p256_pairProgram_quantumTime_direct .shift
  rw [prepareProgram, UnitaryCircuit.evaluatedEventDepth_seq]
  omega

/-- Actual duration follows the same scheduled preparations and complete window execution. -/
lemma p256_program_quantumTime_direct (signed : Bool) :
    (program 256 (by decide) signed).evaluatedEventDepth Resource.Event.quantumDuration ≤
      18922 + (if signed then 14187 else 12893) := by
  have preparation := p256_prepare_time_direct
  rw [program, PredicateCompute.program_quantumTime, RemainderWindow.p256_program_quantumTime]
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderAddress.Parallel
