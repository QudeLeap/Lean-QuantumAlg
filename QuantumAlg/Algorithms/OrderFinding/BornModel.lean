/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.AccessCircuit
import all QuantumAlg.Algorithms.OrderFinding.AccessCircuit
import all QuantumAlg.Algorithms.OrderFinding.Eigenstructure
import all QuantumAlg.Algorithms.OrderFinding.Probability
import all QuantumAlg.Algorithms.QPE.Basic
import all QuantumAlg.Util.RationalApproximation

/-!
# Original order-finding source amplitudes and measurement probabilities

The circuit amplitudes, oracle fibers and exact dyadic support are mathematics
of the original source circuit [dW19, qcnotes.tex:2203-2258]. They do not depend
on the execution interface or its storage and resource proofs. The measurement
model here describes a marginal; native execution retains the full register.
-/

namespace QuantumAlg

open NormalizedVector
open scoped BigOperators

noncomputable section

namespace OrderFinding

/-- Raw Born support before the terminal decoder is executed. -/
def ExactOutcome (r t : Nat) (outcome : Outcome t) : Prop :=
  ∃ s : Fin r, (decodeOutcome outcome).val = s.val * (2 ^ t / r)

namespace BornBridge

/-- The actual normalized state produced by the production circuit. -/
def evolvedState {N x t m : Nat} (A : ModExpOracleAccess N x t m) :
    QubitLayout.State (layout t m) :=
  { state := PureState.ofNormalized
      (UnitaryCircuit.applyNormalized (OrderFinding.orderFindingCircuit A)
        (NormalizedVector.ket (R := Qubits (t + m))
          (prodEquiv ((0 : Fin (2 ^ t)), (0 : Fin (2 ^ m))))))
      (layout t m).systemIdx
    system_idx_eq := rfl }

/-- Raw post-oracle periodic state, before inverse-QFT readout. -/
def postOracleVec {N x t m : Nat} (A : ModExpOracleAccess N x t m) :
    HilbertVector (Qubits (t + m)) :=
  WithLp.toLp 2 fun basis =>
    let pair := prodEquiv.symm basis
    if pair.2 = modExpOracleTarget A pair.1 (0 : Fin (2 ^ m)) then
      WalshHadamard.invSqrtCard t
    else
      0

/-- Circuit amplitude written as the inverse-QFT sum over the actual periodic
oracle fibers. -/
def circuitSourceAmplitude {N x t m : Nat}
    (A : ModExpOracleAccess N x t m)
    (c : Fin (2 ^ t)) (y : Fin (2 ^ m)) : ℂ :=
  ∑ a : Fin (2 ^ t),
    star (invSqrtN t * ω t ^ (a.val * c.val)) *
      if y = modExpOracleTarget A a (0 : Fin (2 ^ m)) then
        WalshHadamard.invSqrtCard t
      else
        0

theorem modExpOracleTarget_eq_zero_iff {N x t m : Nat}
    (A : ModExpOracleAccess N x t m) (a : Fin (2 ^ t))
    (y : Fin (2 ^ m)) :
    modExpOracleTarget A a y = 0 ↔
      y = modExpOracleTarget A a (0 : Fin (2 ^ m)) := by
  constructor
  · intro h
    have htwice := congrArg (modExpOracleTarget A a) h
    simpa [modExpOracleTarget, Nat.xor_assoc] using htwice
  · intro h
    subst y
    apply Fin.ext
    simp [modExpOracleTarget]

theorem preparation_apply_input {t m : Nat} :
    (orderFindingPreparationCircuit t m).applyVec
        (NormalizedVector.ket (R := Qubits (t + m))
          (prodEquiv ((0 : Fin (2 ^ t)), (0 : Fin (2 ^ m)))) :
          HilbertVector (Qubits (t + m))) =
      HilbertVector.tensor
        (WalshHadamard.uniformState t : HilbertVector (Qubits t))
        (NormalizedVector.ket (R := Qubits m) (0 : Fin (2 ^ m)) :
          HilbertVector (Qubits m)) := by
  rw [← NormalizedVector.tensor_ket]
  change (orderFindingPreparationCircuit t m).matrix.applyVec
      (HilbertVector.tensor
        (NormalizedVector.ket (R := Qubits t) (0 : Fin (2 ^ t)) :
          HilbertVector (Qubits t))
        (NormalizedVector.ket (R := Qubits m) (0 : Fin (2 ^ m)) :
          HilbertVector (Qubits m))) = _
  rw [orderFindingPreparationCircuit, UnitaryCircuit.tensorQubits_matrix,
    UnitaryOperator.tensor_applyVec_tensor]
  change HilbertVector.tensor _
      ((UnitaryCircuit.identity (Qubits m) (List.range' t m)
        List.nodup_range').applyVec _) = _
  rw [UnitaryCircuit.applyVec_identity]
  congr 1
  rw [WalshHadamard.hadamardLayer_matrix]
  exact congrArg (fun state : NormalizedVector (Qubits t) =>
      (state : HilbertVector (Qubits t)))
    WalshHadamard.hadamardLayerOperator_apply_zero

theorem oracle_apply_preparation {N x t m : Nat}
    (A : ModExpOracleAccess N x t m) :
    (orderFindingOracleCircuit A).applyVec
        ((orderFindingPreparationCircuit t m).applyVec
          (NormalizedVector.ket (R := Qubits (t + m))
            (prodEquiv ((0 : Fin (2 ^ t)), (0 : Fin (2 ^ m)))) :
            HilbertVector (Qubits (t + m)))) =
      postOracleVec A := by
  rw [preparation_apply_input]
  apply WithLp.ofLp_injective
  funext basis
  change (orderFindingOracleCircuit A).matrix.applyVec
      (HilbertVector.tensor
        (WalshHadamard.uniformState t : HilbertVector (Qubits t))
        (NormalizedVector.ket (R := Qubits m) (0 : Fin (2 ^ m)) :
          HilbertVector (Qubits m))) basis =
    (if (prodEquiv.symm basis).2 =
        modExpOracleTarget A (prodEquiv.symm basis).1 0 then
      WalshHadamard.invSqrtCard t
    else
      0)
  change (modExpOracle A).applyVec
      (HilbertVector.tensor
        (WalshHadamard.uniformState t : HilbertVector (Qubits t))
        (NormalizedVector.ket (R := Qubits m) (0 : Fin (2 ^ m)) :
          HilbertVector (Qubits m))) basis = _
  rw [modExpOracle, UnitaryOperator.ofPerm_applyVec]
  change HilbertVector.tensor
      (WalshHadamard.uniformState t : HilbertVector (Qubits t))
      (NormalizedVector.ket (R := Qubits m) (0 : Fin (2 ^ m)) :
        HilbertVector (Qubits m))
      (prodEquiv ((prodEquiv.symm basis).1,
        modExpOracleTarget A (prodEquiv.symm basis).1
          (prodEquiv.symm basis).2)) = _
  rw [HilbertVector.tensor_apply_prod, WalshHadamard.uniformState_apply,
    NormalizedVector.ket_apply]
  rw [if_congr (modExpOracleTarget_eq_zero_iff A
    (prodEquiv.symm basis).1 (prodEquiv.symm basis).2) rfl rfl]
  by_cases htarget :
      (prodEquiv.symm basis).2 =
        modExpOracleTarget A (prodEquiv.symm basis).1 0
  · rw [if_pos htarget, if_pos htarget, mul_one]
  · rw [if_neg htarget, if_neg htarget, mul_zero]

theorem identityCircuit_entry (m : Nat) (systemIdx : List Nat)
    (hvalid : systemIdx.Nodup)
    (left right : Fin (2 ^ m)) :
    ((UnitaryCircuit.identity (Qubits m) systemIdx hvalid : UnitaryCircuit (Qubits m)).matrix :
      HilbertOperator (Qubits m))
        left right = if left = right then 1 else 0 := by
  rfl

theorem orderFindingCircuit_amplitude {N x t m : Nat}
    (A : ModExpOracleAccess N x t m)
    (c : Fin (2 ^ t)) (y : Fin (2 ^ m)) :
    (evolvedState A).normalized (prodEquiv (c, y)) =
      circuitSourceAmplitude A c y := by
  change UnitaryCircuit.applyVec (orderFindingCircuit A)
      (NormalizedVector.ket (R := Qubits (t + m))
        (prodEquiv ((0 : Fin (2 ^ t)), (0 : Fin (2 ^ m)))) :
        HilbertVector (Qubits (t + m))) (prodEquiv (c, y)) = _
  rw [orderFindingCircuit, UnitaryCircuit.applyVec_seq, UnitaryCircuit.applyVec_seq]
  rw [oracle_apply_preparation]
  change HilbertOperator.applyVec
      ((orderFindingReadoutCircuit t m).matrix : HilbertOperator (Qubits (t + m)))
      (postOracleVec A) (prodEquiv (c, y)) = _
  rw [HilbertOperator.applyVec_apply,
    ← Equiv.sum_comp (prodEquiv (m := t) (n := m)),
    Fintype.sum_prod_type]
  simp only [orderFindingReadoutCircuit, UnitaryCircuit.tensorQubits_matrix,
    UnitaryOperator.tensor_apply, Equiv.symm_apply_apply,
    UnitaryCircuit.dagger_matrix,
    QFTCircuit_matrix, Matrix.conjTranspose_apply, QFTOperator_entry,
    identityCircuit_entry, postOracleVec]
  rw [circuitSourceAmplitude]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.sum_eq_single y]
  · by_cases htarget : y = modExpOracleTarget A a 0
    · simp [htarget]
    · simp [htarget]
  · intro z _hz hzy
    simp [Ne.symm hzy]
  · simp

/-! ## Terminal-measurement fibers -/

theorem orderFindingMeasurementOutcome_injective (t : Nat) :
    Function.Injective (measurementOutcome t) := by
  intro left right h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases hbit : bit < t
  · let outputIndex : Fin t := ⟨t - 1 - bit, by omega⟩
    have hreverse : t - 1 - outputIndex.val = bit := by
      dsimp [outputIndex]
      omega
    have hout := congrFun h outputIndex
    simpa [measurementOutcome, hreverse] using hout
  · have htbit : t ≤ bit := Nat.le_of_not_gt hbit
    have hpow : 2 ^ t ≤ 2 ^ bit :=
      Nat.pow_le_pow_right (by decide : 1 ≤ 2) htbit
    rw [Nat.testBit_eq_false_of_lt (left.isLt.trans_le hpow),
      Nat.testBit_eq_false_of_lt (right.isLt.trans_le hpow)]

theorem orderFindingMeasurementOutcome_bijective (t : Nat) :
    Function.Bijective (measurementOutcome t) := by
  apply (Fintype.bijective_iff_injective_and_card (measurementOutcome t)).2
  refine ⟨orderFindingMeasurementOutcome_injective t, ?_⟩
  simp

@[simp] theorem orderFindingMeasurement_readout_prod {t m : Nat}
    (c : Fin (2 ^ t)) (y : Fin (2 ^ m)) :
    (measurement t m).readout (prodEquiv (c, y)) =
      measurementOutcome t c := by
  funext outputIndex
  change (prodEquiv (c, y)).val.testBit
      (t + m - 1 - outputIndex.val) =
    c.val.testBit (t - 1 - outputIndex.val)
  have hindex :
      t + m - 1 - outputIndex.val =
        m + (t - 1 - outputIndex.val) := by
    omega
  rw [hindex]
  exact prodEquiv_testBit_left c y
    ⟨t - 1 - outputIndex.val, by omega⟩

theorem orderFindingMeasurement_readout_eq_outcome_iff {t m : Nat}
    (basis : Fin (2 ^ (t + m))) (c : Fin (2 ^ t)) :
    (measurement t m).readout basis = measurementOutcome t c ↔
      (prodEquiv.symm basis).1 = c := by
  have hself :
      (measurement t m).readout basis =
        measurementOutcome t (prodEquiv.symm basis).1 := by
    simpa using orderFindingMeasurement_readout_prod
      (m := m) (prodEquiv.symm basis).1 (prodEquiv.symm basis).2
  constructor
  · intro h
    exact orderFindingMeasurementOutcome_injective t (hself.symm.trans h)
  · intro h
    exact hself.trans (congrArg (measurementOutcome t) h)

/-- Embed the unmeasured target-register basis into one phase-readout fiber. -/
def orderFindingFiberEmbedding {t m : Nat} (c : Fin (2 ^ t)) :
    Fin (2 ^ m) ↪ Fin (2 ^ (t + m)) where
  toFun := fun y => prodEquiv (c, y)
  inj' := by
    intro left right h
    cases prodEquiv.injective h
    rfl

@[simp] theorem orderFindingFiberEmbedding_apply {t m : Nat}
    (c : Fin (2 ^ t)) (y : Fin (2 ^ m)) :
    orderFindingFiberEmbedding c y = prodEquiv (c, y) := rfl

theorem orderFindingMeasurement_fiber {t m : Nat} (c : Fin (2 ^ t)) :
    Finset.univ.filter
        (fun basis : Fin (2 ^ (t + m)) =>
          (measurement t m).readout basis = measurementOutcome t c) =
      Finset.univ.map (orderFindingFiberEmbedding c) := by
  ext basis
  rw [Finset.mem_filter, orderFindingMeasurement_readout_eq_outcome_iff]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro hleft
    apply Finset.mem_map.mpr
    refine ⟨(prodEquiv.symm basis).2, Finset.mem_univ _, ?_⟩
    rw [orderFindingFiberEmbedding_apply, ← hleft]
    exact (Equiv.apply_symm_apply (prodEquiv (m := t) (n := m)) basis)
  · intro hmem
    obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hmem
    change prodEquiv (c, y) = basis at hy
    rw [← hy, Equiv.symm_apply_apply]

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

theorem circuitSourceAmplitude_orbitTarget_eq_star {N x t m r : Nat}
    (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t m)
    (c : Fin (2 ^ t)) (k : Fin r) :
    circuitSourceAmplitude A c (orbitTarget A k) =
      star (shorSourceJointAmplitude t r (c, k)) := by
  classical
  unfold circuitSourceAmplitude
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

theorem circuitSourceAmplitude_eq_zero_of_not_mem_orbit
    {N x t m r : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t m)
    (c : Fin (2 ^ t)) (y : Fin (2 ^ m))
    (hnot : y ∉ (Finset.univ : Finset (Fin r)).image (orbitTarget A)) :
    circuitSourceAmplitude A c y = 0 := by
  classical
  unfold circuitSourceAmplitude
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

/-- The actual terminal Born probability is the target-register marginal of
the source joint distribution. -/
theorem bornOutcomeProbability_eq_sourceMarginal {N x t m r : Nat}
    (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t m) (c : Fin (2 ^ t)) :
    (measurement t m).outcomePMF (evolvedState A) (measurementOutcome t c) =
      ENNReal.ofReal
        (∑ k : Fin r, orderFindingPublicOutcomeProbability t r (c, k)) := by
  classical
  rw [TerminalZMeasure.outcomePMF_apply, orderFindingMeasurement_fiber,
    Finset.sum_map]
  simp_rw [orderFindingFiberEmbedding_apply, orderFindingCircuit_amplitude]
  change (∑ y : Fin (2 ^ m),
      ENNReal.ofReal (‖circuitSourceAmplitude A c y‖ ^ 2)) = _
  calc
    (∑ y : Fin (2 ^ m),
        ENNReal.ofReal (‖circuitSourceAmplitude A c y‖ ^ 2)) =
        ∑ y ∈ (Finset.univ : Finset (Fin r)).map
            (orbitTargetEmbedding hinput A),
          ENNReal.ofReal (‖circuitSourceAmplitude A c y‖ ^ 2) := by
      symm
      apply Finset.sum_subset (by simp)
      intro y _hy hnot
      have hnotImage :
          y ∉ (Finset.univ : Finset (Fin r)).image (orbitTarget A) := by
        simpa only [mem_orbitTargetEmbedding_map_iff hinput A y] using hnot
      rw [circuitSourceAmplitude_eq_zero_of_not_mem_orbit
        hinput A c y hnotImage]
      simp
    _ = ∑ k : Fin r,
        ENNReal.ofReal
          (‖circuitSourceAmplitude A c (orbitTarget A k)‖ ^ 2) := by
      rw [Finset.sum_map]
      simp
    _ = ∑ k : Fin r,
        ENNReal.ofReal (orderFindingPublicOutcomeProbability t r (c, k)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [circuitSourceAmplitude_orbitTarget_eq_star hinput A]
      simp [orderFindingPublicOutcomeProbability, shorSourceJointProbability]
    _ = ENNReal.ofReal
        (∑ k : Fin r, orderFindingPublicOutcomeProbability t r (c, k)) := by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      intro k _hk
      exact orderFindingPublicOutcomeProbability_nonneg t r (c, k)

/-! ## Exact divisible-period support -/

theorem shorSourceJointAmplitude_eq_zero_of_not_dvd_period
    {t r : Nat} (hr : 0 < r) (hrt : r ∣ 2 ^ t)
    (c : Fin (2 ^ t)) (k : Fin r)
    (hnot : ¬ 2 ^ t / r ∣ c.val) :
    shorSourceJointAmplitude t r (c, k) = 0 := by
  let q : Nat := 2 ^ t
  let period : Nat := q / r
  have hq_pos : 0 < q := by
    dsimp [q]
    positivity
  have hr_le_q : r ≤ q := Nat.le_of_dvd hq_pos hrt
  have hperiod_pos : 0 < period := Nat.div_pos hr_le_q hr
  have hq_eq : r * period = q := Nat.mul_div_cancel' hrt
  have hkq : k.val < q := k.isLt.trans_le hr_le_q
  have hlength : ((q - 1 - k.val) / r) + 1 = period := by
    have hremainder : r - 1 - k.val < r := by omega
    have hdecomp :
        q - 1 - k.val = (r - 1 - k.val) + r * (period - 1) := by
      rw [Nat.mul_sub_left_distrib]
      omega
    rw [hdecomp, Nat.add_mul_div_left _ _ hr,
      Nat.div_eq_of_lt hremainder]
    omega
  have hterm : ∀ b : Nat,
      Complex.exp (2 * Real.pi *
          (((((r : Real) * (b : Real) * (c.val : Real)) /
            (2 : Real) ^ t) : Real)) * Complex.I) =
        (ω t ^ (r * c.val)) ^ b := by
    intro b
    rw [← pow_mul, ω, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hbase_ne : ω t ^ (r * c.val) ≠ 1 := by
    intro hbase
    have hbase_z : ω t ^ ((r * c.val : Nat) : Int) = 1 := by
      simpa only [zpow_natCast] using hbase
    have hdiv_z : ((q : Nat) : Int) ∣ ((r * c.val : Nat) : Int) := by
      simpa [q] using (omega_zpow_eq_one_iff t _).mp hbase_z
    have hdiv : q ∣ r * c.val := by
      exact_mod_cast hdiv_z
    rcases hdiv with ⟨multiple, hmultiple⟩
    apply hnot
    refine ⟨multiple, ?_⟩
    have hcancel : r * c.val = r * (period * multiple) := by
      calc
        r * c.val = q * multiple := hmultiple
        _ = (r * period) * multiple := by rw [hq_eq]
        _ = r * (period * multiple) := by ac_rfl
    exact Nat.eq_of_mul_eq_mul_left hr hcancel
  have hbase_pow : (ω t ^ (r * c.val)) ^ period = 1 := by
    calc
      (ω t ^ (r * c.val)) ^ period =
          ω t ^ ((r * c.val) * period) :=
        (pow_mul (ω t) (r * c.val) period).symm
      _ = ω t ^ (q * c.val) := by
        congr 1
        calc
          (r * c.val) * period = (r * period) * c.val := by ac_rfl
          _ = q * c.val := by rw [hq_eq]
      _ = (ω t ^ q) ^ c.val :=
        pow_mul (ω t) q c.val
      _ = 1 := by simp [q, omega_pow_eq_one]
  rw [shorSourceJointAmplitude_eq_orbit_phase_mul_quotient_step_sum hr]
  rw [shorSourceJointQuotientIndices_eq_range hr hkq]
  change _ * (_ * (Finset.range (((q - 1 - k.val) / r) + 1)).sum _) = _
  rw [hlength]
  simp_rw [hterm]
  rw [geom_sum_eq hbase_ne, hbase_pow]
  simp

theorem orderFindingPublicOutcomeProbability_eq_zero_of_not_dvd_period
    {t r : Nat} (hr : 0 < r) (hrt : r ∣ 2 ^ t)
    (c : Fin (2 ^ t)) (k : Fin r)
    (hnot : ¬ 2 ^ t / r ∣ c.val) :
    orderFindingPublicOutcomeProbability t r (c, k) = 0 := by
  unfold orderFindingPublicOutcomeProbability shorSourceJointProbability
  rw [shorSourceJointAmplitude_eq_zero_of_not_dvd_period hr hrt c k hnot]
  simp

/-- The production circuit has probability one on the exact dyadic support
whenever the true order divides the phase-register cardinality. -/
theorem exactMeasurementModel {N x t m r : Nat}
    (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t m) (hrt : r ∣ 2 ^ t) :
    ((measurement t m).outcomePMF
        (evolvedState A)).toOuterMeasure
      {outcome | ExactOutcome r t outcome} = 1 := by
    classical
    let q : Nat := 2 ^ t
    let period : Nat := q / r
    have hq_pos : 0 < q := by
      dsimp [q]
      positivity
    have hr_le_q : r ≤ q := Nat.le_of_dvd hq_pos hrt
    have hperiod_pos : 0 < period :=
      Nat.div_pos hr_le_q hinput.order_pos
    have hq_eq : r * period = q := Nat.mul_div_cancel' hrt
    rw [PMF.toOuterMeasure_apply_eq_one_iff]
    intro outcome houtcome
    obtain ⟨c, rfl⟩ :=
      (orderFindingMeasurementOutcome_bijective t).2 outcome
    have hdvd : period ∣ c.val := by
      by_contra hnot
      have hnot' : ¬ 2 ^ t / r ∣ c.val := by
        simpa [period, q] using hnot
      have hzero_each (k : Fin r) :
          orderFindingPublicOutcomeProbability t r (c, k) = 0 :=
        orderFindingPublicOutcomeProbability_eq_zero_of_not_dvd_period
          hinput.order_pos hrt c k hnot'
      have hzero :
          (measurement t m).outcomePMF (evolvedState A)
              (measurementOutcome t c) = 0 := by
        rw [bornOutcomeProbability_eq_sourceMarginal hinput A]
        simp [hzero_each]
      exact ((PMF.mem_support_iff _ _).mp houtcome) hzero
    change ∃ s : Fin r,
      (decodeOutcome (measurementOutcome t c)).val =
        s.val * (2 ^ t / r)
    rw [decodeOutcome_measurementOutcome]
    have hc_lt : c.val < r * period := by
      rw [hq_eq]
      exact c.isLt
    let s : Fin r :=
      ⟨c.val / period,
        (Nat.div_lt_iff_lt_mul hperiod_pos).2 hc_lt⟩
    refine ⟨s, ?_⟩
    change c.val = (c.val / period) * (2 ^ t / r)
    simpa [q, period] using (Nat.div_mul_cancel hdvd).symm

end BornBridge

end OrderFinding

end

end QuantumAlg
