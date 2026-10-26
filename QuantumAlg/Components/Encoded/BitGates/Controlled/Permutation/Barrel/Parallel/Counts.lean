/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Parallel.Counts
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Barrel.Parallel.Program
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Barrel.Binary

/-!
# Direct complete native ledger of the actual paired barrel

Every declared original control and fixed-power permutation stage is
retained. Exact native multiplicities are sums over the actual paired
transposition words, with no resource equality to a legacy executor.
-/

namespace QuantumAlg.EncodedBit.PermutationBarrelParallel

noncomputable section

variable {size controls : Nat}

/-- Exact number of paired exchanges in all the actual public fixed-power stages. -/
def exchangeCount (permutation : Equiv.Perm (Fin size))
    (stages : List (Fin controls × Nat)) : Nat :=
  (stages.map (fun stage => (Permutation.transpositions (permutation ^ stage.2)).length)).sum

namespace Frame

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- Whole native event multiplicities follow the new program's actual stage recursion. -/
lemma program_nativePool (frame : Frame encoding size controls)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (permutation : Equiv.Perm (Fin size)) (stages : List (Fin controls × Nat)) :
    (frame.program physical oracles permutation stages).eventCost =
      ResourcePool.scale (exchangeCount permutation stages)
        (PermutationParallel.nativePairPool oracles) := by
  induction stages with
  | nil => rfl
  | cons stage rest ih =>
      rw [program, UnitaryCircuit.seq_eventCost, stageProgram,
        PermutationParallel.Frame.program_nativePool, ih]
      simp only [exchangeCount, List.map_cons, List.sum_cons, ResourcePool.scale, add_nsmul]

/-- Every gate coordinate is derived from that same complete actual event pool. -/
lemma program_counts_direct (frame : Frame encoding size controls)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (permutation : Equiv.Perm (Fin size)) (stages : List (Fin controls × Nat)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
        (frame.program physical oracles permutation stages).eventCost =
          2 * exchangeCount permutation stages ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
        (frame.program physical oracles permutation stages).eventCost =
          4 * exchangeCount permutation stages ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
        (frame.program physical oracles permutation stages).eventCost = 0 := by
  induction stages with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons stage rest ih =>
      have head := (frame.pairFrame stage.1).program_counts_direct physical oracles
        (Permutation.transpositions (permutation ^ stage.2))
      simp only [program, UnitaryCircuit.seq_eventCost, stageProgram, ResourcePool.count_add,
        head.1, head.2.1, head.2.2, ih.1, ih.2.1, ih.2.2,
        exchangeCount, List.map_cons, List.sum_cons]
      exact ⟨by omega, by omega, by trivial⟩

end Frame

/-- The standard finite permutation factorization bounds exactly those emitted exchanges. -/
lemma exchangeCount_le (permutation : Equiv.Perm (Fin size))
    (stages : List (Fin controls × Nat)) :
    exchangeCount permutation stages ≤ size * stages.length := by
  induction stages with
  | nil => exact Nat.le_refl 0
  | cons stage rest ih =>
      have head : (Permutation.transpositions (permutation ^ stage.2)).length ≤ size := by
        simpa using Permutation.transpositions_length_le (permutation ^ stage.2)
      change (Permutation.transpositions (permutation ^ stage.2)).length +
        exchangeCount permutation rest ≤ size * (rest.length + 1)
      exact (Nat.add_le_add head ih).trans_eq (by
        rw [Nat.mul_succ]
        exact Nat.add_comm _ _)

/-- Every original binary control bit contributes its complete actual fixed-power stage. -/
lemma binary_exchangeCount_le (permutation : Equiv.Perm (Fin size)) :
    exchangeCount permutation (PermutationBarrel.binaryStages controls) ≤ size * controls := by
  simpa only [PermutationBarrel.binaryStages, List.length_map, List.length_finRange] using
    exchangeCount_le permutation (PermutationBarrel.binaryStages controls)

end

end QuantumAlg.EncodedBit.PermutationBarrelParallel
