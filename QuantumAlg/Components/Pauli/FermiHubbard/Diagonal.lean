/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Pauli.FermiHubbard.Onsite
import all QuantumAlg.Components.Pauli.FermiHubbard.Onsite
import all QuantumAlg.Components.Pauli.FermiHubbard.Modes
import all QuantumAlg.Components.Pauli.Sum.Family
import all QuantumAlg.Components.Pauli.JordanWigner.Strings
import all QuantumAlg.Components.Pauli.String
import all QuantumAlg.Components.Pauli.Letter
import Mathlib.Data.List.Pairwise

/-!
# Diagonal on-site strings

All four entries at every site use only I and Z. Their common diagonal basis
certifies exact on-site evolution, with the scalar term retained.
-/

public section
namespace QuantumAlg.FermiHubbard

lemma modeZ_support {n : ℕ} (p : Fin n) : (JordanWigner.modeZ p).support = {p} := by
  ext j
  simp [PauliString.support, JordanWigner.modeZ]

lemma onsiteZZ_apply {L : ℕ} (p : Site L) (j : Fin (2 * L ^ 2)) :
    onsiteZZ p j = if j = mode 0 p ∨ j = mode 1 p then .z else .i := by
  have hn : mode (0 : Fin 2) p ≠ mode (1 : Fin 2) p :=
    mode_ne_of_spin_ne (by decide) p p
  simp only [onsiteZZ, PauliString.mul, JordanWigner.modeZ]
  split_ifs <;> simp_all [PauliLetter.mulLetter]

lemma onsiteZZ_support {L : ℕ} (p : Site L) :
    (onsiteZZ p).support = {mode 0 p, mode 1 p} := by
  ext j
  simp [PauliString.support, onsiteZZ_apply]
  tauto

lemma identityString_support (L : ℕ) : (identityString L).support = ∅ := by
  ext j
  simp [identityString, PauliString.support]

lemma onsiteZZ_weight {L : ℕ} (p : Site L) : (onsiteZZ p).weight = 2 := by
  rw [PauliString.weight, onsiteZZ_support, Finset.card_pair]
  exact mode_ne_of_spin_ne (by decide) p p

lemma modeZ_weight {n : ℕ} (p : Fin n) : (JordanWigner.modeZ p).weight = 1 := by
  rw [PauliString.weight, modeZ_support, Finset.card_singleton]

lemma identityString_weight (L : ℕ) : (identityString L).weight = 0 := by
  rw [PauliString.weight, identityString_support, Finset.card_empty]

/-- Every literal on-site entry is diagonal, irrespective of its coefficient. -/
lemma onsite_terms_diagonal {L : ℕ} (u μ : ℝ) (a : ℝ × PauliString (2 * L ^ 2))
    (ha : a ∈ (onsite L u μ).terms) (j : Fin (2 * L ^ 2)) :
    a.2 j = .i ∨ a.2 j = .z := by
  rw [onsite, PauliSum.mem_ofFamily_terms] at ha
  obtain ⟨k, hk⟩ := ha
  simp only [siteTerms, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · simp only [onsiteZZ_apply]
    split_ifs <;> simp
  · simp only [JordanWigner.modeZ]
    split_ifs <;> simp
  · simp only [JordanWigner.modeZ]
    split_ifs <;> simp
  · exact Or.inl rfl

private lemma diagonal_strings_commute {n : ℕ} (P Q : PauliString n)
    (hP : ∀ j, P j = .i ∨ P j = .z) (hQ : ∀ j, Q j = .i ∨ Q j = .z) :
    P.Commute Q := by
  have h (j : Fin n) : ¬PauliLetter.anticommutes (P j) (Q j) := by
    rcases hP j with hP | hP <;> rcases hQ j with hQ | hQ <;>
      simp [hP, hQ, PauliLetter.anticommutes]
  simp [PauliString.Commute, PauliString.anticommutingCount, h]

/-- On-site terms, including per-site identities, commute internally. -/
lemma onsite_terms_pairwise (L : ℕ) (u μ : ℝ) :
    (onsite L u μ).terms.Pairwise (fun a b => a.2.Commute b.2) := by
  apply List.pairwise_of_forall_mem_list
  intro a ha b hb
  exact diagonal_strings_commute a.2 b.2
    (onsite_terms_diagonal u μ a ha) (onsite_terms_diagonal u μ b hb)

end QuantumAlg.FermiHubbard
