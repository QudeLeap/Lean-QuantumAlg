/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Pauli.Sum
import all QuantumAlg.Components.Pauli.Sum
import all QuantumAlg.Core.Base.Hamiltonian

/-!
# Ordered finite families of Pauli sums

Flattening an indexed family preserves every presented term, including repeated
strings, scalar terms, and zero coefficients.
-/

public section
namespace QuantumAlg.PauliSum
noncomputable section

/-- Concatenate the terms of a finite family in ascending index order. -/
@[expose] def ofFamily {n k : ℕ} (H : Fin k → PauliSum n) : PauliSum n :=
  ⟨(List.ofFn fun j => (H j).terms).flatten⟩

/-- An entry occurs in the flattening precisely when it occurs in an input block. -/
lemma mem_ofFamily_terms {n k : ℕ} (H : Fin k → PauliSum n) (a : ℝ × PauliString n) :
    a ∈ (ofFamily H).terms ↔ ∃ j, a ∈ (H j).terms := by
  simp [ofFamily]

/-- Every additive statistic of terms distributes over the original family. -/
lemma ofFamily_sum_terms {n k : ℕ} (H : Fin k → PauliSum n)
    {M : Type*} [AddCommMonoid M] (f : (ℝ × PauliString n) → M) :
    ((ofFamily H).terms.map f).sum = ∑ j, ((H j).terms.map f).sum := by
  simp [ofFamily, List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn]

/-- Flattening the presentation adds the corresponding certified Hamiltonians. -/
lemma ofFamily_toHamiltonian {n k : ℕ} (H : Fin k → PauliSum n) :
    (ofFamily H).toHamiltonian = Hamiltonian.sum (fun j => (H j).toHamiltonian) := by
  apply Hamiltonian.ext
  simp only [coe_toHamiltonian, Hamiltonian.coe_sum, ofFamily_sum_terms]

lemma ofFamily_length {n k : ℕ} (H : Fin k → PauliSum n) :
    (ofFamily H).terms.length = ∑ j, (H j).terms.length := by
  simp [ofFamily, List.length_flatten, List.map_ofFn, List.sum_ofFn]

lemma ofFamily_oneNorm {n k : ℕ} (H : Fin k → PauliSum n) :
    (ofFamily H).oneNorm = ∑ j, (H j).oneNorm :=
  ofFamily_sum_terms H (fun a => |a.1|)

end
end QuantumAlg.PauliSum
