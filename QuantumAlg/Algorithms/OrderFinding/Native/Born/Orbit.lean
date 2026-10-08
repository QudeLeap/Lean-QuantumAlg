/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Native.Born.Amplitude
import all QuantumAlg.Algorithms.OrderFinding.Probability
import all QuantumAlg.Algorithms.OrderFinding.Eigenstructure
import all QuantumAlg.Util.Order.Finding
import all QuantumAlg.Primitives.WalshHadamard.Mathematics

/-!
# Source-orbit fibers of the actual native word

The XOR query targets one modular orbit for each exponent. Its injective
orbit labels and inverse Fourier phase sum connect the native amplitudes to
the independent source-joint probability formula.
-/

namespace QuantumAlg.OrderFinding.Native

noncomputable section

open scoped BigOperators

/-! ## Oracle-orbit fibers -/

/-- Target-register label for one coordinate of the exact modular orbit. -/
def orbitTarget {N x t m r : Nat} (A : ModExpOracleAccess N x t m)
    (k : Fin r) : Fin (2 ^ m) :=
  ⟨x ^ k.val % N,
    lt_of_lt_of_le (Nat.mod_lt _ A.modulus_pos) A.register_fits⟩

theorem modExpOracleTarget_eq_orbitTarget_iff {N x t m r : Nat}
    (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t m) (a : Fin (2 ^ t)) (k : Fin r) :
    modExpOracleTarget A a 0 = orbitTarget A k ↔ a.val % r = k.val := by
  have horder : orderOf (ZMod.unitOfCoprime x hinput.coprime) = r :=
    orderOf_zmodUnitOfCoprime_eq_input_order hinput
  constructor
  · intro htarget
    have hmodN : x ^ a.val ≡ x ^ k.val [MOD N] := by
      rw [Nat.ModEq]
      have hval := congrArg Fin.val htarget
      change Nat.xor 0 (x ^ a.val % N) = x ^ k.val % N at hval
      have hzero : Nat.xor 0 (x ^ a.val % N) = x ^ a.val % N :=
        Nat.zero_xor _
      exact hzero.symm.trans hval
    have hzmod : ((x ^ a.val : Nat) : ZMod N) =
        ((x ^ k.val : Nat) : ZMod N) :=
      (ZMod.natCast_eq_natCast_iff (x ^ a.val) (x ^ k.val) N).mpr hmodN
    have hpow :
        (ZMod.unitOfCoprime x hinput.coprime) ^ a.val =
          (ZMod.unitOfCoprime x hinput.coprime) ^ k.val := by
      apply Units.ext
      simpa [Units.val_pow_eq_pow_val, Nat.cast_pow] using hzmod
    let aval : Nat := a.val
    let kval : Nat := k.val
    have hpow' :
        (ZMod.unitOfCoprime x hinput.coprime) ^ aval =
          (ZMod.unitOfCoprime x hinput.coprime) ^ kval := by
      simpa [aval, kval] using hpow
    have hmodOrder :
        aval ≡ kval [MOD orderOf (ZMod.unitOfCoprime x hinput.coprime)] :=
      pow_eq_pow_iff_modEq.mp hpow'
    have hmodR' : aval ≡ kval [MOD r] := by
      simpa only [horder] using hmodOrder
    have hmodR : a.val ≡ k.val [MOD r] := by
      simpa [aval, kval] using hmodR'
    rw [Nat.ModEq, Nat.mod_eq_of_lt k.isLt] at hmodR
    exact hmodR
  · intro hresidue
    have hmodR : a.val ≡ k.val [MOD r] := by
      rw [Nat.ModEq, Nat.mod_eq_of_lt k.isLt]
      exact hresidue
    have hpow :
        (ZMod.unitOfCoprime x hinput.coprime) ^ a.val =
          (ZMod.unitOfCoprime x hinput.coprime) ^ k.val := by
      rw [pow_eq_pow_iff_modEq, horder]
      exact hmodR
    have hzmod : ((x ^ a.val : Nat) : ZMod N) =
        ((x ^ k.val : Nat) : ZMod N) := by
      have hval := congrArg
        (fun u : (ZMod N)ˣ => (u : ZMod N)) hpow
      simpa [Units.val_pow_eq_pow_val, Nat.cast_pow] using hval
    have hmodN : x ^ a.val ≡ x ^ k.val [MOD N] :=
      (ZMod.natCast_eq_natCast_iff (x ^ a.val) (x ^ k.val) N).mp hzmod
    apply Fin.ext
    simpa [modExpOracleTarget, orbitTarget, Nat.ModEq] using hmodN

theorem orbitTarget_injective {N x t m r : Nat}
    (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t m) :
    Function.Injective (orbitTarget A : Fin r → Fin (2 ^ m)) := by
  intro left right htarget
  have hmodN : x ^ left.val ≡ x ^ right.val [MOD N] := by
    rw [Nat.ModEq]
    exact congrArg Fin.val htarget
  have hzmod : ((x ^ left.val : Nat) : ZMod N) =
      ((x ^ right.val : Nat) : ZMod N) :=
    (ZMod.natCast_eq_natCast_iff (x ^ left.val) (x ^ right.val) N).mpr hmodN
  have hpow :
      (ZMod.unitOfCoprime x hinput.coprime) ^ left.val =
        (ZMod.unitOfCoprime x hinput.coprime) ^ right.val := by
    apply Units.ext
    simpa [Units.val_pow_eq_pow_val, Nat.cast_pow] using hzmod
  let leftVal : Nat := left.val
  let rightVal : Nat := right.val
  have hpow' :
      (ZMod.unitOfCoprime x hinput.coprime) ^ leftVal =
        (ZMod.unitOfCoprime x hinput.coprime) ^ rightVal := by
    simpa [leftVal, rightVal] using hpow
  have hmodOrder :
      leftVal ≡ rightVal
        [MOD orderOf (ZMod.unitOfCoprime x hinput.coprime)] :=
    pow_eq_pow_iff_modEq.mp hpow'
  have hmodR' : leftVal ≡ rightVal [MOD r] := by
    simpa only [orderOf_zmodUnitOfCoprime_eq_input_order hinput] using hmodOrder
  have hmodR : left.val ≡ right.val [MOD r] := by
    simpa [leftVal, rightVal] using hmodR'
  unfold Nat.ModEq at hmodR
  rw [Nat.mod_eq_of_lt left.isLt, Nat.mod_eq_of_lt right.isLt] at hmodR
  exact Fin.ext hmodR

theorem shorSourceJointPhaseTerm_eq_omega_pow (t : Nat)
    (c a : Fin (2 ^ t)) :
    shorSourceJointPhaseTerm t c a = ω t ^ (a.val * c.val) := by
  rw [shorSourceJointPhaseTerm, ω, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem born_invSqrtCard_eq_invSqrtN (t : Nat) :
    WalshHadamard.invSqrtCard t = invSqrtN t := by
  rw [WalshHadamard.invSqrtCard, invSqrtN]
  congr 3
  norm_num

private theorem born_invSqrtN_mul_self_sourceNormalization (t : Nat) :
    invSqrtN t * invSqrtN t = (((2 : Real) ^ t : Complex))⁻¹ := by
  rw [invSqrtN_mul_self]
  congr 1
  norm_num

private theorem born_star_sourceNormalization (t : Nat) :
    star ((((2 : Real) ^ t : Complex))⁻¹) =
      (((2 : Real) ^ t : Complex))⁻¹ := by
  rw [star_inv₀, star_pow, Complex.star_def, Complex.conj_ofReal]

theorem inverseQFT_orbitTerm_eq_star_sourceTerm (t : Nat)
    (c a : Fin (2 ^ t)) :
    star (invSqrtN t * ω t ^ (a.val * c.val)) *
        WalshHadamard.invSqrtCard t =
      star ((((2 : Real) ^ t : Complex))⁻¹ *
        shorSourceJointPhaseTerm t c a) := by
  rw [born_invSqrtCard_eq_invSqrtN,
    shorSourceJointPhaseTerm_eq_omega_pow]
  simp only [star_mul', star_invSqrtN, star_pow]
  calc
    (invSqrtN t * star (ω t) ^ (a.val * c.val)) * invSqrtN t =
        (invSqrtN t * invSqrtN t) *
          star (ω t) ^ (a.val * c.val) := by ring
    _ = (((2 : Real) ^ t : Complex))⁻¹ *
          star (ω t) ^ (a.val * c.val) := by
      rw [born_invSqrtN_mul_self_sourceNormalization]
    _ = star ((((2 : Real) ^ t : Complex))⁻¹) *
          star (ω t) ^ (a.val * c.val) := by
      rw [born_star_sourceNormalization]

theorem sourceAmplitude_orbitTarget_eq_star {N x t m r : Nat}
    (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t m)
    (c : Fin (2 ^ t)) (k : Fin r) :
    sourceAmplitude A c (orbitTarget A k) =
      star (shorSourceJointAmplitude t r (c, k)) := by
  classical
  unfold sourceAmplitude
  have hcondition : ∀ a : Fin (2 ^ t),
      orbitTarget A k = modExpOracleTarget A a 0 ↔
        a.val % r = k.val := by
    intro a
    rw [eq_comm, modExpOracleTarget_eq_orbitTarget_iff hinput A a k]
  simp_rw [hcondition, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  change (shorSourceJointPreimageIndices t k).sum
      (fun a => star (invSqrtN t * ω t ^ (a.val * c.val)) *
        WalshHadamard.invSqrtCard t) = _
  calc
    (shorSourceJointPreimageIndices t k).sum
        (fun a => star (invSqrtN t * ω t ^ (a.val * c.val)) *
          WalshHadamard.invSqrtCard t) =
        (shorSourceJointPreimageIndices t k).sum
          (fun a => star ((((2 : Real) ^ t : Complex))⁻¹ *
            shorSourceJointPhaseTerm t c a)) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      exact inverseQFT_orbitTerm_eq_star_sourceTerm t c a
    _ = star (shorSourceJointAmplitude t r (c, k)) := by
      rw [shorSourceJointAmplitude, star_mul', star_sum,
        born_star_sourceNormalization]
      simp_rw [star_mul', born_star_sourceNormalization]
      rw [Finset.mul_sum]

theorem sourceAmplitude_eq_zero_of_not_mem_orbit
    {N x t m r : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t m)
    (c : Fin (2 ^ t)) (y : Fin (2 ^ m))
    (hnot : y ∉ (Finset.univ : Finset (Fin r)).image (orbitTarget A)) :
    sourceAmplitude A c y = 0 := by
  classical
  unfold sourceAmplitude
  refine Finset.sum_eq_zero fun a _ => ?_
  let k : Fin r := ⟨a.val % r, Nat.mod_lt _ hinput.order_pos⟩
  have htarget : modExpOracleTarget A a 0 = orbitTarget A k :=
    (modExpOracleTarget_eq_orbitTarget_iff hinput A a k).mpr rfl
  have hne : y ≠ modExpOracleTarget A a 0 := by
    intro hy
    apply hnot
    refine Finset.mem_image.mpr ⟨k, Finset.mem_univ _, ?_⟩
    exact (hy.trans htarget).symm
  simp [hne]

/-- The exact modular-orbit target labels as a finite embedding. -/
def orbitTargetEmbedding {N x t m r : Nat}
    (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t m) : Fin r ↪ Fin (2 ^ m) where
  toFun := orbitTarget A
  inj' := orbitTarget_injective hinput A

@[simp] theorem orbitTargetEmbedding_apply {N x t m r : Nat}
    (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t m) (k : Fin r) :
    orbitTargetEmbedding hinput A k = orbitTarget A k := rfl

theorem mem_orbitTargetEmbedding_map_iff {N x t m r : Nat}
    (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t m) (y : Fin (2 ^ m)) :
    y ∈ (Finset.univ : Finset (Fin r)).map (orbitTargetEmbedding hinput A) ↔
      y ∈ (Finset.univ : Finset (Fin r)).image (orbitTarget A) := by
  constructor
  · intro hmem
    rcases Finset.mem_map.mp hmem with ⟨k, _hk, hky⟩
    exact Finset.mem_image.mpr
      ⟨k, Finset.mem_univ k, (orbitTargetEmbedding_apply hinput A k).symm.trans hky⟩
  · intro hmem
    rcases Finset.mem_image.mp hmem with ⟨k, _hk, hky⟩
    exact Finset.mem_map.mpr
      ⟨k, Finset.mem_univ k, (orbitTargetEmbedding_apply hinput A k).trans hky⟩


end

end QuantumAlg.OrderFinding.Native
