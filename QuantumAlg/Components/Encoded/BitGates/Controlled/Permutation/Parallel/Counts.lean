/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Parallel.Program

/-!
# Independent complete native ledger of the actual paired permutation

Each actual paired exchange contributes the native events read from its
two real CNOT layers and two serial common-control Toffolis. Recursion
over the actual new program gives its whole event multiset directly,
without comparing a legacy serial program's resource pool.
-/

namespace QuantumAlg.EncodedBit.PermutationParallel

noncomputable section

/-- Literal native ledger of one actual paired exchange. -/
def nativePairPool (oracles : OracleModel) :
    ResourcePool (.quantum AlgorithmGate.model oracles) :=
  ResourcePool.ofList
    [.gate .cnot, .gate .cnot, .gate .toffoli, .gate .toffoli, .gate .cnot, .gate .cnot]

namespace Frame

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {size : Nat}

private lemma exchange_nativePool (frame : Frame encoding size)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (exchange : Permutation.Transposition (Fin size)) :
    ((frame.exchangeFrame exchange).program physical oracles).eventCost =
      nativePairPool oracles := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    FredkinParallel.Frame.program_eventTrace]
  rfl

/-- The complete actual event pool follows each emitted new paired exchange. -/
lemma program_nativePool (frame : Frame encoding size)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (exchanges : List (Permutation.Transposition (Fin size))) :
    (frame.program physical oracles exchanges).eventCost =
      ResourcePool.scale exchanges.length (nativePairPool oracles) := by
  induction exchanges with
  | nil => rfl
  | cons exchange rest ih =>
      rw [program, UnitaryCircuit.seq_eventCost, exchange_nativePool, ih]
      simp only [List.length_cons, ResourcePool.scale, add_nsmul, one_nsmul]
      exact add_comm _ _

/-- Exact native multiplicities refer to this same actual new program. -/
lemma program_counts_direct (frame : Frame encoding size)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (exchanges : List (Permutation.Transposition (Fin size))) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
        (frame.program physical oracles exchanges).eventCost = 2 * exchanges.length ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
        (frame.program physical oracles exchanges).eventCost = 4 * exchanges.length ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
        (frame.program physical oracles exchanges).eventCost = 0 := by
  induction exchanges with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons exchange rest ih =>
      have head := (frame.exchangeFrame exchange).program_counts physical oracles
      simp only [program, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
        head.1, head.2.1, head.2.2, ih.1, ih.2.1, ih.2.2, List.length_cons]
      exact ⟨by omega, by omega, by trivial⟩

end Frame

end

end QuantumAlg.EncodedBit.PermutationParallel
