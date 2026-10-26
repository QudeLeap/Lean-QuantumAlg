/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.Canonical
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Carrier.Translation
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.ParameterLayout
import all QuantumAlg.Primitives.ShortDLP.Oracle.Mathematics

/-!
# Complete original two-frequency source amplitudes on the same unit partner

The shared Fourier contraction is expanded on the original unit action.
Only source translations are combined; no total measured or dirty arithmetic
matrix is commuted. The complete actual arithmetic/resource proofs remain
independent of this source expansion [GN96, 9511007.tex:214-266].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open QuantumFourierTransform.Semiclassical
open scoped BigOperators

variable (m ell width : Nat) (modulus : BitVec width) [NeZero modulus.toNat]
  (generator target : (ZMod modulus.toNat)ˣ)

/-- The original two complete Fourier contractions act on the same unchanged unit register. -/
def memberFourierKraus (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    HilbertOperator (Recycling.Carrier.units modulus.toNat) :=
  Partner.fullOldKraus true ell
      (fun index => (exponentPowerOperators modulus target⁻¹ ell index :
        HilbertOperator (Recycling.Carrier.units modulus.toNat))) second *
    Partner.fullOldKraus true (ell + m)
      (fun index => (exponentPowerOperators modulus generator (ell + m) index :
        HilbertOperator (Recycling.Carrier.units modulus.toNat))) first

/-- Both actual chronological tuples select the full same-partner Fourier source operator. -/
lemma canonicalMemberSource_fullFourier (Reference : Register)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    canonicalMemberSource m ell width modulus generator target Reference
        (frequencyBits (ell + m) first, frequencyBits ell second) =
      sourceWithReference (memberFourierKraus m ell width modulus generator target first second)
        Reference := by
  have firstSource := canonicalExponentSource_fullFourier modulus generator true Reference first
  have secondSource := canonicalExponentSource_fullFourier modulus target⁻¹ true Reference second
  exact (congrArg₂ (fun left right :
      HilbertOperator ((Recycling.Carrier.units modulus.toNat).prod Reference) => left * right)
    secondSource firstSource).trans
      (fourier_reference_product _ _ Reference).symm

/-- The original complete Fourier contraction is its exact sum of unit translations. -/
lemma measuredExponentFourier_sum (bits : Nat) (unit : (ZMod modulus.toNat)ˣ)
    (frequency : Fin (2 ^ bits)) :
    Partner.fullOldKraus true bits
        (fun position => (exponentPowerOperators modulus unit bits position :
          HilbertOperator (Recycling.Carrier.units modulus.toNat))) frequency =
      ∑ input : Fin (2 ^ bits),
        (Partner.fullRows true bits frequency ((binaryEquiv bits).symm input) *
          NormalizedVector.invSqrt2 ^ bits) •
            (unitTranslation modulus (unit ^ input.val) :
              HilbertOperator (Recycling.Carrier.units modulus.toNat)) := by
  rw [Partner.qftPartner_fullOldKraus_physical, Partner.qftPartner_oldKraus_contraction]
  simp only [Partner.contraction, Partner.phaseBasis_one, mul_one]
  simp_rw [measuredOrderedWord_power]
  rw [← Equiv.sum_comp (binaryEquiv bits).symm]
  simp only [Equiv.apply_symm_apply]
  simp_rw [← Partner.qftPartner_fullRows_physical]

/-- The complete two-frequency source keeps both input sums and their common unit action. -/
lemma memberFourierKraus_sum (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    memberFourierKraus m ell width modulus generator target first second =
      ∑ sourceFirst : Fin (2 ^ (ell + m)), ∑ sourceSecond : Fin (2 ^ ell),
        ((Partner.fullRows true ell second ((binaryEquiv ell).symm sourceSecond) *
            NormalizedVector.invSqrt2 ^ ell) *
          (Partner.fullRows true (ell + m) first ((binaryEquiv (ell + m)).symm sourceFirst) *
            NormalizedVector.invSqrt2 ^ (ell + m))) •
              (unitTranslation modulus (target⁻¹ ^ sourceSecond.val * generator ^ sourceFirst.val) :
                HilbertOperator (Recycling.Carrier.units modulus.toNat)) := by
  unfold memberFourierKraus
  rw [measuredExponentFourier_sum, measuredExponentFourier_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  apply Finset.sum_congr rfl
  intro sourceFirst _
  apply Finset.sum_congr rfl
  intro sourceSecond _
  rw [mul_comm
    (Partner.fullRows true (ell + m) first ((binaryEquiv (ell + m)).symm sourceFirst) *
      NormalizedVector.invSqrt2 ^ (ell + m))]
  exact congrArg (fun operator : HilbertOperator (Recycling.Carrier.units modulus.toNat) =>
    ((Partner.fullRows true ell second ((binaryEquiv ell).symm sourceSecond) *
        NormalizedVector.invSqrt2 ^ ell) *
      (Partner.fullRows true (ell + m) first ((binaryEquiv (ell + m)).symm sourceFirst) *
        NormalizedVector.invSqrt2 ^ (ell + m))) • operator)
    (measuredTranslation_mul modulus (target⁻¹ ^ sourceSecond.val) (generator ^ sourceFirst.val))

/-- The canonical unit-one column is the original two-frequency oracle amplitude. -/
lemma memberFourierKraus_seed_entry
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell))
    (row : (Recycling.Carrier.units modulus.toNat).Index) :
    memberFourierKraus m ell width modulus generator target first second row 1 =
      ∑ sourceFirst : Fin (2 ^ (ell + m)), ∑ sourceSecond : Fin (2 ^ ell),
        ((Partner.fullRows true ell second ((binaryEquiv ell).symm sourceSecond) *
            NormalizedVector.invSqrt2 ^ ell) *
          (Partner.fullRows true (ell + m) first ((binaryEquiv (ell + m)).symm sourceFirst) *
            NormalizedVector.invSqrt2 ^ (ell + m))) *
              if row = oracleValue generator target sourceFirst.val sourceSecond.val then 1
              else 0 :=
    by
  rw [memberFourierKraus_sum]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro sourceFirst _
  apply Finset.sum_congr rfl
  intro sourceSecond _
  have coefficient : target⁻¹ ^ sourceSecond.val * generator ^ sourceFirst.val =
      oracleValue generator target sourceFirst.val sourceSecond.val := by
    simp only [oracleValue, inv_pow]
    ac_rfl
  have entry : (unitTranslation modulus
        (target⁻¹ ^ sourceSecond.val * generator ^ sourceFirst.val) :
          HilbertOperator (Recycling.Carrier.units modulus.toNat)) row 1 =
      (if row = oracleValue generator target sourceFirst.val sourceSecond.val then (1 : ℂ)
      else 0) :=
    by
    simp only [unitTranslation, UnitaryOperator.ofPerm_entry, Equiv.mulLeft_symm_apply,
      coefficient, inv_mul_eq_iff_eq_mul, mul_one]
  exact congrArg (fun amplitude : ℂ =>
    ((Partner.fullRows true ell second ((binaryEquiv ell).symm sourceSecond) *
        NormalizedVector.invSqrt2 ^ ell) *
      (Partner.fullRows true (ell + m) first ((binaryEquiv (ell + m)).symm sourceFirst) *
        NormalizedVector.invSqrt2 ^ (ell + m))) * amplitude) entry

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
