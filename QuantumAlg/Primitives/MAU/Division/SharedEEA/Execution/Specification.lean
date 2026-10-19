/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.CanonicalInverse
import all QuantumAlg.Util.Nat.FixedWidth.Modular.Word.Equiv

/-!
# Independent modular-add division permutation with a supplied flag

The unit denominator, arbitrary modular numerator and target, and original
flag are retained quantum fields. Independent finite arithmetic adds the
numerator times the canonical ZMod inverse into the target. Noncanonical
target labels are fixed individually. No circuit, native resource, initial
auxiliary state, or run enters this mathematical permutation.
-/

namespace QuantumAlg.MAU.Division.SharedEEA.ExecutionSpecification

noncomputable section

open NumberTheory.SharedEEA Nat.FixedWidth

/-- Original denominator, numerator, arbitrary target, and supplied live flag. -/
abbrev Labels (width : Nat) :=
  Fin (2 ^ width) × ((Fin (2 ^ width) × Fin (2 ^ width)) × Bool)

/-- Exactly the original unit denominator and canonical modular numerator and target support. -/
def admissible (modulus : Nat) (value : Labels modulus.size) : Prop :=
  value.1.val < modulus ∧ Nat.Coprime value.1.val modulus ∧
    value.2.1.1.val < modulus ∧ value.2.1.2.val < modulus

private def fittedModulus (modulus : Nat) : Fin (2 ^ modulus.size + 1) :=
  ⟨modulus, (Nat.lt_size_self modulus).trans (Nat.lt_succ_self _)⟩

private def offset (modulus : Nat) (modulusPositive : 0 < modulus)
    (denominator numerator : Fin (2 ^ modulus.size)) :
    Fin ((fittedModulus modulus).val + 1) :=
  ⟨(numerator.val * (CanonicalInverse.word modulus modulusPositive denominator.val).val) % modulus,
    (Nat.mod_lt _ modulusPositive).trans (Nat.lt_succ_self modulus)⟩

/-- Pure reversible addition preserves both source words and the independently supplied flag. -/
def permutation (modulus : Nat) (modulusPositive : 0 < modulus) :
    Equiv.Perm (Labels modulus.size) :=
  Equiv.prodCongrRight fun denominator =>
    Equiv.prodCongr
      (Equiv.prodCongrRight fun numerator => modularWordEquiv (fittedModulus modulus)
        (offset modulus modulusPositive denominator numerator)) (Equiv.refl Bool)

/-- Every canonical target receives the complete quotient; all other original fields remain. -/
lemma divisionSpecification_valid (modulus : Nat) (modulusPositive : 0 < modulus)
    (value : Labels modulus.size) (targetBounded : value.2.1.2.val < modulus) :
    (permutation modulus modulusPositive value).1 = value.1 ∧
      (permutation modulus modulusPositive value).2.1.1 = value.2.1.1 ∧
      (permutation modulus modulusPositive value).2.1.2.val =
        (value.2.1.2.val + value.2.1.1.val *
          (CanonicalInverse.word modulus modulusPositive value.1.val).val) % modulus ∧
      (permutation modulus modulusPositive value).2.2 = value.2.2 := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  change (modularWordEquiv (fittedModulus modulus)
    (offset modulus modulusPositive value.1 value.2.1.1) value.2.1.2).val = _
  rw [modularWordEquiv_apply,
    gidneyModularWord_valid (fittedModulus modulus) _ value.2.1.2 targetBounded]
  change (value.2.1.2.val + (value.2.1.1.val *
    (CanonicalInverse.word modulus modulusPositive value.1.val).val) % modulus) % modulus = _
  rw [Nat.add_mod_mod]

/-- The total binary extension fixes each target outside the canonical residue range. -/
lemma divisionSpecification_outside (modulus : Nat) (modulusPositive : 0 < modulus)
    (value : Labels modulus.size) (outside : modulus ≤ value.2.1.2.val) :
    permutation modulus modulusPositive value = value := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Prod.ext
      · rfl
      · change modularWordEquiv (fittedModulus modulus)
          (offset modulus modulusPositive value.1 value.2.1.1) value.2.1.2 = value.2.1.2
        rw [modularWordEquiv_apply]
        exact gidneyModularWord_outside (fittedModulus modulus) _ value.2.1.2 outside
    · rfl

/-- Modulus one fixes every binary label, including arbitrary supplied flags and padding. -/
lemma divisionSpecification_one (value : Labels (1 : Nat).size) :
    permutation 1 (by decide) value = value := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Prod.ext
      · rfl
      · change modularWordEquiv (fittedModulus 1)
          (offset 1 (by decide) value.1 value.2.1.1) value.2.1.2 = _
        rw [modularWordEquiv_apply]
        exact gidneyModularWord_modulus_one (fittedModulus 1) rfl _ value.2.1.2
    · rfl

/-- Nontrivial EEA input positivity follows from the original local unit support. -/
lemma divisionSpecification_positive (modulus : Nat) (nontrivial : 1 < modulus)
    (value : Labels modulus.size) (allowed : admissible modulus value) :
    0 < value.1.val := by
  have coprime := allowed.2.1
  by_contra absent
  have zero : value.1.val = 0 := by omega
  rw [zero, Nat.coprime_zero_left] at coprime
  omega

end

end QuantumAlg.MAU.Division.SharedEEA.ExecutionSpecification
