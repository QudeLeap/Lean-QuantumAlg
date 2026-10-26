/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Barrel.Parallel.Program
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Barrel.Binary

/-! # Actual duration of every paired barrel stage -/

namespace QuantumAlg.EncodedBit.PermutationBarrelParallel.Frame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {size controls : Nat}

/-- Actual duration follows every emitted public stage and its common-control Toffolis. -/
lemma program_quantumTime (frame : Frame encoding size controls)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (permutation : Equiv.Perm (Fin size)) (stages : List (Fin controls × Nat)) :
    (frame.program physical oracles permutation stages).evaluatedEventDepth
        Resource.Event.quantumDuration =
      4 * (stages.map (fun stage =>
        (Permutation.transpositions (permutation ^ stage.2)).length)).sum := by
  induction stages with
  | nil => rfl
  | cons stage rest ih =>
      rw [program, UnitaryCircuit.evaluatedEventDepth_seq, stageProgram,
        PermutationParallel.Frame.program_quantumTime, ih]
      simp only [List.map_cons, List.sum_cons]
      omega

/-- Linear factor bounds refer to these exact public source permutations, without extra systems. -/
lemma program_quantumTime_le (frame : Frame encoding size controls)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (permutation : Equiv.Perm (Fin size)) (stages : List (Fin controls × Nat)) :
    (frame.program physical oracles permutation stages).evaluatedEventDepth
        Resource.Event.quantumDuration ≤ 4 * size * stages.length := by
  induction stages with
  | nil => exact Nat.le_refl 0
  | cons stage rest ih =>
      have head := (frame.pairFrame stage.1).fixed_quantumTime_le physical oracles
        (permutation ^ stage.2)
      rw [program, UnitaryCircuit.evaluatedEventDepth_seq]
      exact (Nat.add_le_add head ih).trans_eq (by
        simp only [List.length_cons, Nat.mul_succ]
        exact Nat.add_comm _ _)

/-- Every original binary metadata bit retains its full paid fixed-power stage. -/
lemma binary_quantumTime_le (frame : Frame encoding size controls)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (permutation : Equiv.Perm (Fin size)) :
    (frame.program physical oracles permutation
        (PermutationBarrel.binaryStages controls)).evaluatedEventDepth
          Resource.Event.quantumDuration ≤ 4 * size * controls := by
  simpa only [PermutationBarrel.binaryStages, List.length_map, List.length_finRange] using
    frame.program_quantumTime_le physical oracles permutation
      (PermutationBarrel.binaryStages controls)

end

end QuantumAlg.EncodedBit.PermutationBarrelParallel.Frame
