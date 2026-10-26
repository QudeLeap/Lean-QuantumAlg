/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Parallel.Program

/-! # Actual four-step time for every paired exchange -/

namespace QuantumAlg.EncodedBit.PermutationParallel.Frame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {size : Nat}

/-- Exact native time includes every common-control Toffoli dependency. -/
lemma program_quantumTime (frame : Frame encoding size)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (exchanges : List (Permutation.Transposition (Fin size))) :
    (frame.program physical oracles exchanges).evaluatedEventDepth
        Resource.Event.quantumDuration = 4 * exchanges.length := by
  induction exchanges with
  | nil => rfl
  | cons exchange rest ih =>
      rw [program, UnitaryCircuit.evaluatedEventDepth_seq,
        FredkinParallel.Frame.program_quantumTime, ih, List.length_cons]
      omega

/-- Fixed public permutations retain their complete source factor list and all physical systems. -/
lemma fixed_quantumTime_le (frame : Frame encoding size)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (permutation : Equiv.Perm (Fin size)) :
    (frame.program physical oracles (Permutation.transpositions permutation)).evaluatedEventDepth
        Resource.Event.quantumDuration ≤ 4 * size := by
  rw [program_quantumTime]
  exact Nat.mul_le_mul_left 4 (by simpa using Permutation.transpositions_length_le permutation)

end

end QuantumAlg.EncodedBit.PermutationParallel.Frame
