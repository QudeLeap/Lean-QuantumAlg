/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.CanonicalInverse
import all QuantumAlg.Util.Nat.FixedWidth.Modular.Word.Equiv

/-!
# Independent modular-add inverse permutation with a supplied flag

The input unit, arbitrary modular target, and arbitrary flag are the
original data fields. Their mathematical action adds the canonical
residue inverse into the target and preserves the other fields.
Finite labels outside the canonical target range are individually fixed.
The permutation contains no circuit, gate event, resource witness, or run.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.AccumulateSpecification

noncomputable section

open NumberTheory.SharedEEA Nat.FixedWidth

/-- Supplied binary fields include the original input, target, and live flag. -/
abbrev Labels (width : Nat) := Fin (2 ^ width) × Fin (2 ^ width) × Bool

/-- The original unit input and arbitrary modular target determine the allowed local support. -/
def admissible (modulus : Nat) (value : Labels modulus.size) : Prop :=
  value.1.val < modulus ∧ Nat.Coprime value.1.val modulus ∧ value.2.1.val < modulus

private def fittedModulus (modulus : Nat) : Fin (2 ^ modulus.size + 1) :=
  ⟨modulus, (Nat.lt_size_self modulus).trans (Nat.lt_succ_self _)⟩

private def offset (modulus : Nat) (modulusPositive : 0 < modulus)
    (input : Fin (2 ^ modulus.size)) : Fin ((fittedModulus modulus).val + 1) := by
  let : NeZero modulus := ⟨Nat.ne_of_gt modulusPositive⟩
  exact ⟨(CanonicalInverse.word modulus modulusPositive input.val).val,
    (ZMod.val_lt ((input.val : ZMod modulus)⁻¹)).trans (Nat.lt_succ_self modulus)⟩

/-- A reversible family of independent residue additions preserves the original input and flag. -/
def permutation (modulus : Nat) (modulusPositive : 0 < modulus) :
    Equiv.Perm (Labels modulus.size) :=
  Equiv.prodCongrRight fun input =>
    Equiv.prodCongr (modularWordEquiv (fittedModulus modulus)
      (offset modulus modulusPositive input)) (Equiv.refl Bool)

/-- Every admitted target receives the complete canonical inverse without changing other fields. -/
lemma accumulateSpecification_valid (modulus : Nat) (modulusPositive : 0 < modulus)
    (value : Labels modulus.size) (targetBounded : value.2.1.val < modulus) :
    (permutation modulus modulusPositive value).1 = value.1 ∧
      (permutation modulus modulusPositive value).2.1.val =
        (value.2.1.val + (CanonicalInverse.word modulus modulusPositive value.1.val).val) %
          modulus ∧
      (permutation modulus modulusPositive value).2.2 = value.2.2 := by
  refine ⟨rfl, ?_, rfl⟩
  change (modularWordEquiv (fittedModulus modulus)
    (offset modulus modulusPositive value.1) value.2.1).val = _
  rw [modularWordEquiv_apply]
  exact gidneyModularWord_valid (fittedModulus modulus) _ value.2.1 targetBounded

/-- Noncanonical target labels are preserved by the total binary extension. -/
lemma accumulateSpecification_outside (modulus : Nat) (modulusPositive : 0 < modulus)
    (value : Labels modulus.size) (outside : modulus ≤ value.2.1.val) :
    permutation modulus modulusPositive value = value := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change modularWordEquiv (fittedModulus modulus)
        (offset modulus modulusPositive value.1) value.2.1 = value.2.1
      rw [modularWordEquiv_apply]
      exact gidneyModularWord_outside (fittedModulus modulus) _ value.2.1 outside
    · rfl

/-- Modulus one fixes every binary label, including both supplied flag values. -/
lemma accumulateSpecification_one (value : Labels (1 : Nat).size) :
    permutation 1 (by decide) value = value := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change modularWordEquiv (fittedModulus 1) (offset 1 (by decide) value.1) value.2.1 = _
      rw [modularWordEquiv_apply]
      exact gidneyModularWord_modulus_one (fittedModulus 1) rfl _ value.2.1
    · rfl

/-- Positivity of the nontrivial EEA input is derived from the original unit support. -/
lemma accumulateSpecification_positive (modulus : Nat) (nontrivial : 1 < modulus)
    (value : Labels modulus.size) (allowed : admissible modulus value) :
    0 < value.1.val := by
  have coprime := allowed.2.1
  by_contra absent
  have zero : value.1.val = 0 := by omega
  rw [zero, Nat.coprime_zero_left] at coprime
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.AccumulateSpecification
