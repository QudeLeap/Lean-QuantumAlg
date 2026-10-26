/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Parallel.Pair
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Barrel.Parallel.Counts

/-!
# Direct whole native ledger of the actual original-metadata paired alignment

All original binary controls and complete fixed-power permutations remain
in the same actual new program. The exact event pool and coordinates are
derived from its actual paired stages, without an old executor's ledger.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment.Parallel

noncomputable section

open EncodedBit

/-- The whole actual pool retains every declared original quantum-metadata stage. -/
lemma pairProgram_nativePool (width : Nat) (field : ArithmeticGeometry.Field) :
    (pairProgram width field).eventCost =
      ResourcePool.scale (PermutationBarrelParallel.exchangeCount
        (ArithmeticAlignment.permutation width) (PermutationBarrel.binaryStages width.size))
        (PermutationParallel.nativePairPool .empty) :=
  (frame width field).program_nativePool (QubitLayout.canonical _) .empty
    (ArithmeticAlignment.permutation width) (PermutationBarrel.binaryStages width.size)

/-- Exact separate native coordinates refer to those same real paired stages. -/
lemma pairProgram_counts_direct (width : Nat) (field : ArithmeticGeometry.Field) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (pairProgram width field).eventCost =
          2 * PermutationBarrelParallel.exchangeCount
            (ArithmeticAlignment.permutation width) (PermutationBarrel.binaryStages width.size) ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (pairProgram width field).eventCost =
          4 * PermutationBarrelParallel.exchangeCount
            (ArithmeticAlignment.permutation width) (PermutationBarrel.binaryStages width.size) ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (pairProgram width field).eventCost = 0 :=
  (frame width field).program_counts_direct (QubitLayout.canonical _) .empty
    (ArithmeticAlignment.permutation width) (PermutationBarrel.binaryStages width.size)

/-- Actual time keeps both common-control Toffolis serial for every paired exchange. -/
lemma pairProgram_quantumTime_direct (width : Nat) (field : ArithmeticGeometry.Field) :
    (pairProgram width field).evaluatedEventDepth Resource.Event.quantumDuration =
      4 * PermutationBarrelParallel.exchangeCount
        (ArithmeticAlignment.permutation width) (PermutationBarrel.binaryStages width.size) :=
  (frame width field).program_quantumTime (QubitLayout.canonical _) .empty
    (ArithmeticAlignment.permutation width) (PermutationBarrel.binaryStages width.size)

/-- Original P-256 caps follow from the exact actual new-stage ledger. -/
lemma p256_pairProgram_counts_direct (field : ArithmeticGeometry.Field) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (pairProgram 256 field).eventCost ≤ 4662 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (pairProgram 256 field).eventCost ≤ 9324 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (pairProgram 256 field).eventCost = 0 := by
  have factors : PermutationBarrelParallel.exchangeCount (ArithmeticAlignment.permutation 256)
      (PermutationBarrel.binaryStages (256 : Nat).size) ≤ 2331 :=
    (PermutationBarrelParallel.binary_exchangeCount_le
      (controls := (256 : Nat).size) (ArithmeticAlignment.permutation 256)).trans_eq (by decide)
  have actual := pairProgram_counts_direct 256 field
  exact ⟨actual.1.le.trans (by omega), actual.2.1.le.trans (by omega), actual.2.2⟩

/-- The exact actual schedule meets the same independently stated P-256 duration cap. -/
lemma p256_pairProgram_quantumTime_direct (field : ArithmeticGeometry.Field) :
    (pairProgram 256 field).evaluatedEventDepth Resource.Event.quantumDuration ≤ 9324 := by
  have actual := pairProgram_counts_direct 256 field
  have scheduled := pairProgram_quantumTime_direct 256 field
  rw [← actual.2.1] at scheduled
  exact scheduled.trans_le (p256_pairProgram_counts_direct field).2.1

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment.Parallel
