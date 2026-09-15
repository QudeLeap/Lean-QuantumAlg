/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Gram.Program

/-!
# Complete actual Gram matrix correctness

The six outputs equal the original integer dot products modulo the word width.
Every basis row is retained, and no initial accumulator values are assumed.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeMetricMachine

open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)
open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- All original Gram entries and basis rows hold in the final actual store. -/
theorem refreshInto_correct (basis : LatticeState.BasisRefs ctx width) (refs : Refs ctx width)
    (separation : Separation basis refs) (store : Store ctx) (value : NumberTheory.IntegerBasis3)
    (rep : BasisRawRepresents store basis value) :
    GramRawRepresents (refreshStore basis refs store) refs value ∧
      BasisRawRepresents (refreshStore basis refs store) basis value := by
  let state1 := entryStore basis refs .g11 store
  have rep1 := entryInto_preserves_basis basis refs separation .g11 store value rep
  have value1 := entryInto_correct basis refs separation .g11 store value rep
  let state2 := entryStore basis refs .g21 state1
  have rep2 := entryInto_preserves_basis basis refs separation .g21 state1 value rep1
  have value2 := entryInto_correct basis refs separation .g21 state1 value rep1
  let state3 := entryStore basis refs .g31 state2
  have rep3 := entryInto_preserves_basis basis refs separation .g31 state2 value rep2
  have value3 := entryInto_correct basis refs separation .g31 state2 value rep2
  let state4 := entryStore basis refs .g22 state3
  have rep4 := entryInto_preserves_basis basis refs separation .g22 state3 value rep3
  have value4 := entryInto_correct basis refs separation .g22 state3 value rep3
  let state5 := entryStore basis refs .g32 state4
  have rep5 := entryInto_preserves_basis basis refs separation .g32 state4 value rep4
  have value5 := entryInto_correct basis refs separation .g32 state4 value rep4
  let state6 := entryStore basis refs .g33 state5
  have rep6 := entryInto_preserves_basis basis refs separation .g33 state5 value rep5
  have value6 := entryInto_correct basis refs separation .g33 state5 value rep5
  refine ⟨?_, rep6⟩
  intro entry
  cases entry with
  | g11 =>
    change RawSignedRepresents ((refreshStore basis refs store).read
      (writeInput (metricCellRef refs .g11))) (entryValue value .g11)
    unfold refreshStore
    rw [entryInto_preserves_entry basis refs separation .g33 .g11 (by decide)]
    rw [entryInto_preserves_entry basis refs separation .g32 .g11 (by decide)]
    rw [entryInto_preserves_entry basis refs separation .g22 .g11 (by decide)]
    rw [entryInto_preserves_entry basis refs separation .g31 .g11 (by decide)]
    rw [entryInto_preserves_entry basis refs separation .g21 .g11 (by decide)]
    exact value1
  | g21 =>
    change RawSignedRepresents ((refreshStore basis refs store).read
      (writeInput (metricCellRef refs .g21))) (entryValue value .g21)
    unfold refreshStore
    rw [entryInto_preserves_entry basis refs separation .g33 .g21 (by decide)]
    rw [entryInto_preserves_entry basis refs separation .g32 .g21 (by decide)]
    rw [entryInto_preserves_entry basis refs separation .g22 .g21 (by decide)]
    rw [entryInto_preserves_entry basis refs separation .g31 .g21 (by decide)]
    exact value2
  | g31 =>
    change RawSignedRepresents ((refreshStore basis refs store).read
      (writeInput (metricCellRef refs .g31))) (entryValue value .g31)
    unfold refreshStore
    rw [entryInto_preserves_entry basis refs separation .g33 .g31 (by decide)]
    rw [entryInto_preserves_entry basis refs separation .g32 .g31 (by decide)]
    rw [entryInto_preserves_entry basis refs separation .g22 .g31 (by decide)]
    exact value3
  | g22 =>
    change RawSignedRepresents ((refreshStore basis refs store).read
      (writeInput (metricCellRef refs .g22))) (entryValue value .g22)
    unfold refreshStore
    rw [entryInto_preserves_entry basis refs separation .g33 .g22 (by decide)]
    rw [entryInto_preserves_entry basis refs separation .g32 .g22 (by decide)]
    exact value4
  | g32 =>
    change RawSignedRepresents ((refreshStore basis refs store).read
      (writeInput (metricCellRef refs .g32))) (entryValue value .g32)
    unfold refreshStore
    rw [entryInto_preserves_entry basis refs separation .g33 .g32 (by decide)]
    exact value5
  | g33 =>
    change RawSignedRepresents ((refreshStore basis refs store).read
      (writeInput (metricCellRef refs .g33))) (entryValue value .g33)
    unfold refreshStore
    exact value6

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeMetricMachine
