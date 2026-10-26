/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime

/-! # Actual native resources of a fixed controlled wire permutation -/

namespace QuantumAlg.EncodedBit.PermutationFrame

noncomputable section

open Permutation

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {size : Nat}

/-- One actual Toffoli per static transposition, including the inactive quantum branch. -/
lemma program_toffoli_count (frame : PermutationFrame encoding size)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (exchanges : List (Transposition (Fin size))) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
      (GateSpec.programList physical oracles (frame.gates exchanges)).eventCost =
        exchanges.length := by
  rw [GateSpec.programList_toffoli_count_eq_sum]
  exact (frame.gates_counts exchanges).1

/-- Two actual CNOTs per original coordinate exchange. -/
lemma program_cnot_count (frame : PermutationFrame encoding size)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (exchanges : List (Transposition (Fin size))) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
      (GateSpec.programList physical oracles (frame.gates exchanges)).eventCost =
        2 * exchanges.length := by
  rw [GateSpec.programList_cnot_count_eq_sum]
  exact (frame.gates_counts exchanges).2.1

/-- Common-control dependencies charge all three native steps of each exchange. -/
lemma program_quantumTime (frame : PermutationFrame encoding size)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (exchanges : List (Transposition (Fin size))) :
    (GateSpec.programList physical oracles (frame.gates exchanges)).evaluatedEventDepth
      Resource.Event.quantumDuration = 3 * exchanges.length := by
  rw [GateSpec.programList_quantumTime]
  exact (frame.gates_counts exchanges).2.2

/-- Static factorization yields linear bounds for the same emitted circuit and carrier. -/
lemma fixed_resources (frame : PermutationFrame encoding size)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (permutation : Equiv.Perm (Fin size)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
        (GateSpec.programList physical oracles (frame.gates (transpositions permutation))).eventCost
        ≤ size ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
        (GateSpec.programList physical oracles (frame.gates (transpositions permutation))).eventCost
        ≤ 2 * size ∧
      (GateSpec.programList physical oracles
        (frame.gates (transpositions permutation))).evaluatedEventDepth
        Resource.Event.quantumDuration ≤ 3 * size := by
  rw [frame.program_toffoli_count, frame.program_cnot_count, frame.program_quantumTime]
  have count : (transpositions permutation).length ≤ size := by
    simpa using transpositions_length_le permutation
  exact ⟨count, Nat.mul_le_mul_left 2 count, Nat.mul_le_mul_left 3 count⟩

end

end QuantumAlg.EncodedBit.PermutationFrame
