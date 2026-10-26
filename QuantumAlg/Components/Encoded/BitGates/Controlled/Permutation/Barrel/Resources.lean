/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Barrel
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Resources

/-! # Native counts and default duration of the actual complete barrel word -/

namespace QuantumAlg.EncodedBit.PermutationBarrel

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {size controls : Nat}

private lemma stage_counts (barrel : PermutationBarrel encoding size controls)
    (permutation : Equiv.Perm (Fin size)) (stage : Fin controls × Nat) :
    ((barrel.stageGates permutation stage).map GateSpec.toffoliMultiplicity).sum ≤ size ∧
      ((barrel.stageGates permutation stage).map GateSpec.cnotMultiplicity).sum ≤ 2 * size ∧
      (barrel.stageGates permutation stage).length ≤ 3 * size := by
  have bound : (Permutation.transpositions (permutation ^ stage.2)).length ≤ size := by
    simpa using Permutation.transpositions_length_le (permutation ^ stage.2)
  have actual := (barrel.frame stage.1).gates_counts
    (Permutation.transpositions (permutation ^ stage.2))
  exact ⟨actual.1.trans_le bound, actual.2.1.trans_le (Nat.mul_le_mul_left 2 bound),
    actual.2.2.trans_le (Nat.mul_le_mul_left 3 bound)⟩

/-- The ledger contains every actual Fredkin, including all inactive quantum branches. -/
lemma gates_counts (barrel : PermutationBarrel encoding size controls)
    (permutation : Equiv.Perm (Fin size)) (stages : List (Fin controls × Nat)) :
    ((barrel.gates permutation stages).map GateSpec.toffoliMultiplicity).sum
        ≤ size * stages.length ∧
      ((barrel.gates permutation stages).map GateSpec.cnotMultiplicity).sum
        ≤ 2 * size * stages.length ∧
      (barrel.gates permutation stages).length ≤ 3 * size * stages.length := by
  induction stages with
  | nil => simp [gates]
  | cons stage rest ih =>
      have actual := barrel.stage_counts permutation stage
      simp only [gates, List.map_append, List.sum_append, List.length_append, List.length_cons]
      constructor
      · calc
          _ ≤ size + size * rest.length := Nat.add_le_add actual.1 ih.1
          _ = size * (rest.length + 1) := by simp [Nat.mul_add, Nat.add_comm]
      constructor
      · calc
          _ ≤ 2 * size + 2 * size * rest.length := Nat.add_le_add actual.2.1 ih.2.1
          _ = 2 * size * (rest.length + 1) := by simp [Nat.mul_add, Nat.add_comm]
      · calc
          _ ≤ 3 * size + 3 * size * rest.length := Nat.add_le_add actual.2.2 ih.2.2
          _ = 3 * size * (rest.length + 1) := by simp [Nat.mul_add, Nat.add_comm]

/-- The same literal program charges native gates and all common-control duration. -/
lemma program_resources (barrel : PermutationBarrel encoding size controls)
    (permutation : Equiv.Perm (Fin size)) (stages : List (Fin controls × Nat))
    (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
        (barrel.program permutation stages physical oracles).eventCost ≤ size * stages.length ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
        (barrel.program permutation stages physical oracles).eventCost ≤ 2 * size * stages.length ∧
      (barrel.program permutation stages physical oracles).evaluatedEventDepth
        Resource.Event.quantumDuration ≤ 3 * size * stages.length := by
  simp only [program, GateSpec.programList_toffoli_count_eq_sum,
    GateSpec.programList_cnot_count_eq_sum, GateSpec.programList_quantumTime]
  exact barrel.gates_counts permutation stages

end

end QuantumAlg.EncodedBit.PermutationBarrel
