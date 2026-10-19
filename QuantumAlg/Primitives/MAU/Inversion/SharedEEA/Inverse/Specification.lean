/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.CanonicalInverse
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Inverse.Preparation

/-!
# Independent complete quantum XOR-inverse specification

The mathematical permutation preserves the first word and XORs the
canonical `ZMod` inverse into the arbitrary second word. This defines
an involutive permutation on all finite labels, with no gate metadata.
The implementation covers every positive modulus and its unit residues,
including even and composite moduli and modulus one. This is a project
proof extension of the prime domain in
[LYL+26, sec_EEA/sub_4phase.tex:104-128].

The local input predicate selects the corresponding density support. It
does not require a pure input, a classical input label, a zero target,
or a separable external reference. The final contract will compare the
full prepared quantum-reference state with this independent permutation.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InverseSpecification

noncomputable section

open Execution InversePreparation NumberTheory.SharedEEA

/-- Bounded unit residues, read from the actual first supplied quantum word. -/
def admissible (modulus : Nat) (basis : (before modulus.size).register.Index) : Prop :=
  (inputBasisEquiv modulus.size basis).1.val < modulus ∧
    Nat.Coprime (inputBasisEquiv modulus.size basis).1.val modulus

/-- A bounded unit of a nontrivial modulus supplies the native positivity premise internally. -/
lemma admissible_positive (modulus : Nat) (nontrivial : 1 < modulus)
    (basis : (before modulus.size).register.Index) (allowed : admissible modulus basis) :
    0 < (inputBasisEquiv modulus.size basis).1.val := by
  have coprime := allowed.2
  by_contra absent
  have zero : (inputBasisEquiv modulus.size basis).1.val = 0 := by omega
  rw [zero, Nat.coprime_zero_left] at coprime
  omega

/-- Every possible input-reference extension is allowed whenever this local support holds. -/
def valid (modulus : Nat)
    (state : ExecutionState (Store (before modulus.size)) (before modulus.size).register) : Prop :=
  ∀ basis, ¬admissible modulus basis → state.quantumMarginal.matrix basis basis = 0

/-- Pure finite arithmetic: preserve the first word and XOR the canonical residue inverse. -/
def wordStep (modulus : Nat) (modulusPositive : 0 < modulus)
    (pair : Fin (2 ^ modulus.size) × Fin (2 ^ modulus.size)) :
    Fin (2 ^ modulus.size) × Fin (2 ^ modulus.size) :=
  (pair.1, ⟨pair.2.val ^^^ (CanonicalInverse.word modulus modulusPositive pair.1.val).val,
    Nat.xor_lt_two_pow pair.2.isLt (CanonicalInverse.word modulus modulusPositive pair.1.val).isLt⟩)

/-- XOR with the same canonical inverse twice restores both complete arbitrary words. -/
lemma wordStep_involutive (modulus : Nat) (modulusPositive : 0 < modulus) :
    Function.Involutive (wordStep modulus modulusPositive) := by
  intro pair
  apply Prod.ext
  · rfl
  · apply Fin.ext
    change ((pair.2.val ^^^ (CanonicalInverse.word modulus modulusPositive pair.1.val).val) ^^^
      (CanonicalInverse.word modulus modulusPositive pair.1.val).val) = pair.2.val
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

private def wordEquiv (modulus : Nat) (modulusPositive : 0 < modulus) :
    Equiv.Perm (Fin (2 ^ modulus.size) × Fin (2 ^ modulus.size)) where
  toFun := wordStep modulus modulusPositive
  invFun := wordStep modulus modulusPositive
  left_inv := wordStep_involutive modulus modulusPositive
  right_inv := wordStep_involutive modulus modulusPositive

/-- The independent arithmetic permutation on the exact supplied context basis. -/
def permutation (modulus : Nat) (modulusPositive : 0 < modulus) :
    Equiv.Perm (before modulus.size).register.Index :=
  (inputBasisEquiv modulus.size).trans
    ((wordEquiv modulus modulusPositive).trans (inputBasisEquiv modulus.size).symm)

/-- The exact physical input labels undergo the independent two-word arithmetic. -/
lemma permutation_read (modulus : Nat) (modulusPositive : 0 < modulus)
    (basis : (before modulus.size).register.Index) :
    inputBasisEquiv modulus.size (permutation modulus modulusPositive basis) =
      wordStep modulus modulusPositive (inputBasisEquiv modulus.size basis) :=
  (inputBasisEquiv modulus.size).apply_symm_apply _

/-- Modulus one has zero canonical inverse, so every original target is unchanged. -/
lemma permutation_one (basis : (before (1 : Nat).size).register.Index) :
    permutation 1 (by decide) basis = basis := by
  apply (inputBasisEquiv (1 : Nat).size).injective
  rw [permutation_read]
  apply Prod.ext
  · rfl
  · apply Fin.ext
    change (inputBasisEquiv (1 : Nat).size basis).2.val ^^^
      (CanonicalInverse.word 1 (by decide)
        (inputBasisEquiv (1 : Nat).size basis).1.val).val = _
    simp only [CanonicalInverse.word_one, Fin.val_zero, Nat.xor_zero]

/-- The independently specified unitary contains no native event, physical placement, or run. -/
def operator (modulus : Nat) (modulusPositive : 0 < modulus) :
    UnitaryOperator (before modulus.size).register :=
  UnitaryOperator.ofPerm (R := (before modulus.size).register)
    (permutation modulus modulusPositive).symm

/-- Every mathematical basis column includes the exact amplitude, without a phase quotient. -/
lemma operator_ket (modulus : Nat) (modulusPositive : 0 < modulus)
    (basis : (before modulus.size).register.Index) :
    (operator modulus modulusPositive).apply
        (NormalizedVector.ket (R := (before modulus.size).register) basis) =
      NormalizedVector.ket (R := (before modulus.size).register)
        (permutation modulus modulusPositive basis) :=
  UnitaryOperator.ofPerm_apply_ket (R := (before modulus.size).register)
    (permutation modulus modulusPositive).symm basis

end

end QuantumAlg.MAU.Inversion.SharedEEA.InverseSpecification
