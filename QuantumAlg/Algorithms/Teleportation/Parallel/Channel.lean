/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Teleportation.Channel
import all QuantumAlg.Algorithms.Teleportation.Channel
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Parallel corrected branches preserve arbitrary joint inputs

The tensor product of the exact one-block Kraus operators is a scalar
identity on the complete input register. Its density action therefore
retains correlations between distinct teleported systems and an arbitrary
external reference [dW19, qcnotes.tex:809]. No factorization of the unknown
input is assumed. These matrix identities support the native interpreter
proof; they introduce no additional execution or supplied outcome.
-/

namespace QuantumAlg.QuantumTeleportation.Parallel

noncomputable section

open scoped BigOperators

/-- Joint computational labels of all unknown input systems, without a state factorization. -/
public abbrev inputRegister (count : Nat) : Register where
  Index := Fin count → Fin 2
  fintype := inferInstance
  decEq := inferInstance

/-- The rectangular one-block instruments combine by their genuine tensor matrix entries. -/
public def correctedBankKraus (count : Nat) (outcomes : Fin count → Bool × Bool) :
    HilbertOperator (inputRegister count) := fun row column =>
  ∏ index : Fin count,
    correctedKraus (outcomes index).1 (outcomes index).2 (row index) (column index)

/-- Every complete outcome has one scalar identity on the entire, possibly entangled input. -/
public lemma teleportation_correctedBankKraus_eq (count : Nat)
    (outcomes : Fin count → Bool × Bool) :
    correctedBankKraus count outcomes =
      ((2 : ℂ)⁻¹ ^ count) • (1 : HilbertOperator (inputRegister count)) := by
  classical
  ext row column
  simp only [correctedBankKraus, teleportation_correctedKraus_eq_half_identity,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases same : row = column
  · subst column
    simp
  · rw [if_neg same, mul_zero]
    have different : ∃ index, row index ≠ column index := by
      by_contra missing
      push Not at missing
      exact same (funext missing)
    obtain ⟨index, different⟩ := different
    exact Finset.prod_eq_zero (Finset.mem_univ index) (by simp [different])

/-- The complete corrected instrument acts trivially on every external reference coordinate. -/
public def correctedBankKrausWithReference (count : Nat)
    (outcomes : Fin count → Bool × Bool) (Reference : Register) :
    HilbertOperator ((inputRegister count).prod Reference) := fun row column =>
  correctedBankKraus count outcomes row.1 column.1 *
    if row.2 = column.2 then 1 else 0

/-- The scalar identity includes the entire input-reference tensor product. -/
public lemma teleportation_correctedBankKraus_reference (count : Nat)
    (outcomes : Fin count → Bool × Bool) (Reference : Register) :
    correctedBankKrausWithReference count outcomes Reference =
      ((2 : ℂ)⁻¹ ^ count) •
        (1 : HilbertOperator ((inputRegister count).prod Reference)) := by
  classical
  ext row column
  rcases row with ⟨row, rowRef⟩
  rcases column with ⟨column, columnRef⟩
  simp only [correctedBankKrausWithReference, teleportation_correctedBankKraus_eq,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases localSame : row = column <;>
    by_cases referenceSame : rowRef = columnRef <;>
    simp [localSame, referenceSame]

/-- A full measured branch retains every off-diagonal entry, with its actual branch weight. -/
public lemma teleportation_correctedBankBranch_joint (count : Nat)
    (outcomes : Fin count → Bool × Bool) (Reference : Register)
    (state : HilbertOperator ((inputRegister count).prod Reference)) :
    correctedBankKrausWithReference count outcomes Reference * state *
      (correctedBankKrausWithReference count outcomes Reference).conjTranspose =
        ((4 : ℂ)⁻¹ ^ count) • state := by
  rw [teleportation_correctedBankKraus_reference]
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
  congr 1
  simp only [star_pow, star_inv₀, star_ofNat, ← mul_pow]
  norm_num

/-- Summing the actual complete outcomes gives the identity joint channel, including n = 0. -/
public lemma teleportation_correctedBankBranches_sum (count : Nat) (Reference : Register)
    (state : HilbertOperator ((inputRegister count).prod Reference)) :
    (∑ outcomes : Fin count → Bool × Bool,
      correctedBankKrausWithReference count outcomes Reference * state *
        (correctedBankKrausWithReference count outcomes Reference).conjTranspose) = state := by
  simp only [teleportation_correctedBankBranch_joint, Finset.sum_const,
    Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fin, Nat.reduceMul]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have scalar : ((4 ^ count : Nat) : ℂ) * (4 : ℂ)⁻¹ ^ count = 1 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← mul_pow]
    norm_num
  rw [scalar, one_smul]

end

end QuantumAlg.QuantumTeleportation.Parallel
