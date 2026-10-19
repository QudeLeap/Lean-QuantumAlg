/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Algorithms.QPE.Basic
import all QuantumAlg.Primitives.WalshHadamard.Uniform
import all QuantumAlg.Util.Real.ReciprocalSquareTail
import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# Periodic analysis for quantum phase estimation

This module constructs the controlled-power operator independently of a hidden
phase parameter, proves its eigenstate action, chooses the nearest dyadic point
on the unit circle, and establishes the source-backed lower bound 2 / pi on
the corresponding amplitude.
-/

section

namespace QuantumAlg

open NormalizedVector Gate
open scoped BigOperators

noncomputable section

/-- Reindex a system-register/phase-register product into the combined QPE
register, with the phase register occupying the leading tensor factor. -/
def qpePowerProductEquiv (t n : Nat) :
    Fin (2 ^ n) × Fin (2 ^ t) ≃ Fin (2 ^ (t + n)) :=
  (Equiv.prodComm (Fin (2 ^ n)) (Fin (2 ^ t))).trans prodEquiv

@[simp] private lemma qpePowerProductEquiv_symm_apply (t n : Nat)
    (i : Fin (2 ^ (t + n))) :
    (qpePowerProductEquiv t n).symm i =
      ((prodEquiv.symm i).2, (prodEquiv.symm i).1) := by
  rfl

private lemma qpeReindex_mem_unitaryGroup {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (M : Matrix ι ι ℂ)
    (hM : M ∈ Matrix.unitaryGroup ι ℂ) :
    Matrix.reindex e e M ∈ Matrix.unitaryGroup κ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hM ⊢
  rw [Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, hM, Matrix.submatrix_one_equiv]

/-- Block-diagonal QPE operator whose system-register exponent is a function
of the complete phase-register basis label. -/
def qpeExponentOp {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n))
    (exponent : Fin (2 ^ t) → Nat) : UnitaryOperator (Qubits (t + n)) :=
  UnitaryOperator.ofMatrix
    (Matrix.reindex (qpePowerProductEquiv t n) (qpePowerProductEquiv t n)
      (Matrix.blockDiagonal fun a : Fin (2 ^ t) =>
        ((U : HilbertOperator (Qubits n)) ^ exponent a))) (by
      apply qpeReindex_mem_unitaryGroup
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
      have hblocks :
          (fun a : Fin (2 ^ t) =>
            (U : HilbertOperator (Qubits n)) ^ exponent a *
              ((U : HilbertOperator (Qubits n)) ^ exponent a).conjTranspose) =
            (1 : Fin (2 ^ t) → HilbertOperator (Qubits n)) := by
        funext a
        have hpow := (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ).pow_mem
          U.property (exponent a)
        rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hpow
        exact hpow
      rw [hblocks, Matrix.blockDiagonal_one])

/-- The metadata-free controlled-power ladder: on phase basis index `a`, apply
`U ^ a` to the system register. -/
def qpeControlledPowerOp {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) : UnitaryOperator (Qubits (t + n)) :=
  qpeExponentOp t U Fin.val

@[simp]
lemma qpeExponentOp_apply {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n))
    (exponent : Fin (2 ^ t) → Nat) (i j : Fin (2 ^ (t + n))) :
    qpeExponentOp t U exponent i j =
      if (prodEquiv.symm i).1 = (prodEquiv.symm j).1 then
        ((U : HilbertOperator (Qubits n)) ^
            exponent (prodEquiv.symm i).1)
          (prodEquiv.symm i).2 (prodEquiv.symm j).2
      else 0 := by
    change
      Matrix.reindex (qpePowerProductEquiv t n) (qpePowerProductEquiv t n)
          (Matrix.blockDiagonal fun a : Fin (2 ^ t) =>
            ((U : HilbertOperator (Qubits n)) ^ exponent a)) i j = _
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.blockDiagonal_apply]
    rw [qpePowerProductEquiv_symm_apply, qpePowerProductEquiv_symm_apply]

/-- Multiplying two exponent-controlled blocks adds their pointwise powers. -/
lemma qpeExponentOp_mul {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n))
    (left right : Fin (2 ^ t) → Nat) :
    qpeExponentOp t U left * qpeExponentOp t U right =
      qpeExponentOp t U (fun a => left a + right a) := by
  apply Subtype.ext
  let reindex := Matrix.reindexRingEquiv ℂ (qpePowerProductEquiv t n)
  change
    reindex (Matrix.blockDiagonal fun a : Fin (2 ^ t) =>
          ((U : HilbertOperator (Qubits n)) ^ left a)) *
        reindex (Matrix.blockDiagonal fun a : Fin (2 ^ t) =>
          ((U : HilbertOperator (Qubits n)) ^ right a)) =
      reindex (Matrix.blockDiagonal fun a : Fin (2 ^ t) =>
        ((U : HilbertOperator (Qubits n)) ^ (left a + right a)))
  rw [← map_mul]
  congr 1
  rw [← Matrix.blockDiagonal_mul]
  congr 2
  funext a
  exact (pow_add (U : HilbertOperator (Qubits n)) (left a) (right a)).symm

@[simp]
lemma qpeExponentOp_zero {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) :
    qpeExponentOp t U (fun _ => 0) = 1 := by
  apply Subtype.ext
  ext i j
  rw [qpeExponentOp_apply]
  change (if (prodEquiv.symm i).1 = (prodEquiv.symm j).1 then
      (1 : HilbertOperator (Qubits n))
        (prodEquiv.symm i).2 (prodEquiv.symm j).2 else 0) =
    (1 : HilbertOperator (Qubits (t + n))) i j
  by_cases hphase : (prodEquiv.symm i).1 = (prodEquiv.symm j).1
  · by_cases hsystem : (prodEquiv.symm i).2 = (prodEquiv.symm j).2
    · have hij : i = j := prodEquiv.symm.injective (Prod.ext hphase hsystem)
      subst j
      simp
    · have hij : i ≠ j := by
        intro hij
        subst j
        exact hsystem rfl
      simp [hphase, hsystem, hij]
  · have hij : i ≠ j := by
      intro hij
      subst j
      exact hphase rfl
    simp [hphase, hij]

/-- Repeating one exponent-controlled block scales every branch exponent. -/
lemma qpeExponentOp_pow {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n))
    (exponent : Fin (2 ^ t) → Nat) (count : Nat) :
    qpeExponentOp t U exponent ^ count =
      qpeExponentOp t U (fun a => count * exponent a) := by
  induction count with
  | zero =>
      simp only [pow_zero, Nat.zero_mul]
      exact (qpeExponentOp_zero t U).symm
  | succ count ih =>
      rw [pow_succ, ih, qpeExponentOp_mul]
      congr 1
      funext a
      rw [Nat.succ_mul]

/-- One QPE ladder leaf applies one base-oracle call precisely on phase labels
whose `stage` bit is set. -/
def qpeControlledBitOp {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (stage : Fin t) :
    UnitaryOperator (Qubits (t + n)) :=
  qpeExponentOp t U fun a => (a.val.testBit stage.val).toNat

@[simp]
lemma qpeControlledPowerOp_apply {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (i j : Fin (2 ^ (t + n))) :
    qpeControlledPowerOp t U i j =
      if (prodEquiv.symm i).1 = (prodEquiv.symm j).1 then
        ((U : HilbertOperator (Qubits n)) ^ (prodEquiv.symm i).1.val)
          (prodEquiv.symm i).2 (prodEquiv.symm j).2
      else 0 := by
  exact qpeExponentOp_apply t U Fin.val i j

lemma qpeControlledPowerOp_applyVec_eigenstate {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (u : NormalizedVector (Qubits n)) (lam : ℂ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      lam • (u : HilbertVector (Qubits n)))
    (ψ : HilbertVector (Qubits t)) :
    (qpeControlledPowerOp t U).applyVec
        (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
      HilbertVector.tensor
        (WithLp.toLp 2 fun a : Fin (2 ^ t) => ψ a * lam ^ a.val)
        (u : HilbertVector (Qubits n)) := by
  apply WithLp.ofLp_injective
  funext i
  rw [← Equiv.apply_symm_apply (prodEquiv (m := t) (n := n)) i]
  generalize (prodEquiv (m := t) (n := n)).symm i = pair
  rcases pair with ⟨a, y⟩
  rw [UnitaryOperator.applyVec_apply,
    ← Equiv.sum_comp (prodEquiv (m := t) (n := n))
      (fun j => qpeControlledPowerOp t U (prodEquiv (a, y)) j *
        HilbertVector.tensor ψ (u : HilbertVector (Qubits n)) j),
    Fintype.sum_prod_type]
  simp only [qpeControlledPowerOp_apply, Equiv.symm_apply_apply,
    HilbertVector.tensor_apply_prod]
  rw [Finset.sum_eq_single a]
  · simp only [if_true]
    have hpow := congrArg (fun v : HilbertVector (Qubits n) => v y)
      (qpeGatePower_applyVec_eigenstate hu a.val)
    change HilbertOperator.applyVec
        ((U : HilbertOperator (Qubits n)) ^ a.val)
        (u : HilbertVector (Qubits n)) y =
      (lam ^ a.val • (u : HilbertVector (Qubits n))) y at hpow
    change
      (∑ z, ((U : HilbertOperator (Qubits n)) ^ a.val) y z *
        (ψ a * (u : HilbertVector (Qubits n)) z)) =
        (ψ a * lam ^ a.val) * (u : HilbertVector (Qubits n)) y
    rw [show (∑ z, ((U : HilbertOperator (Qubits n)) ^ a.val) y z *
        (ψ a * (u : HilbertVector (Qubits n)) z)) =
        ψ a * HilbertOperator.applyVec
          ((U : HilbertOperator (Qubits n)) ^ a.val)
          (u : HilbertVector (Qubits n)) y by
        rw [HilbertOperator.applyVec_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        ring]
    change ψ a * _ = _
    rw [hpow]
    simp [mul_assoc]
  · intro b _ hba
    simp [Ne.symm hba]
  · simp

private lemma invSqrtCard_eq_invSqrtN (t : Nat) :
    WalshHadamard.invSqrtCard t = invSqrtN t := by
  rw [WalshHadamard.invSqrtCard, invSqrtN]
  congr 3
  norm_num

lemma qpeControlledPowerOp_apply_uniform_eigenstate {n : Nat}
    (P : QPEEigenstateInput n) (t : Nat) :
    (qpeControlledPowerOp t P.unitary).apply
        (NormalizedVector.tensor (WalshHadamard.uniformState t) P.eigenstate) =
      NormalizedVector.tensor (phaseState t P.phase) P.eigenstate := by
  have hphase :
      (WithLp.toLp 2 fun a : Fin (2 ^ t) =>
          WalshHadamard.uniformState t a *
            Complex.exp (2 * Real.pi * P.phase * Complex.I) ^ a.val) =
        (phaseState t P.phase : HilbertVector (Qubits t)) := by
    apply WithLp.ofLp_injective
    funext a
    change WalshHadamard.invSqrtCard t *
        Complex.exp (2 * Real.pi * P.phase * Complex.I) ^ a.val =
      invSqrtN t *
        Complex.exp (2 * Real.pi * P.phase * a.val * Complex.I)
    rw [invSqrtCard_eq_invSqrtN, ← Complex.exp_nat_mul]
    congr 2
    ring
  apply NormalizedVector.ext
  intro i
  change (qpeControlledPowerOp t P.unitary).applyVec
      (HilbertVector.tensor
        (WalshHadamard.uniformState t : HilbertVector (Qubits t))
        (P.eigenstate : HilbertVector (Qubits n))) i =
    HilbertVector.tensor (phaseState t P.phase : HilbertVector (Qubits t))
      (P.eigenstate : HilbertVector (Qubits n)) i
  rw [qpeControlledPowerOp_applyVec_eigenstate t P.unitary P.eigenstate
    (Complex.exp (2 * Real.pi * P.phase * Complex.I)) P.eigenstate_eq,
    hphase]

/-- Periodic distance between a phase and a dyadic estimate. -/
def qpePhaseDistance (t : Nat) (φ : Real) (j : Fin (2 ^ t)) : Real :=
  ‖((φ - (j.val : Real) / (2 : Real) ^ t : Real) : UnitAddCircle)‖

/-- The nearest dyadic grid point, with integer rounding reduced modulo the
grid size so phases near one wrap to index zero. -/
def qpeNearestIndex (t : Nat) (φ : Real) : Fin (2 ^ t) :=
  ⟨(round ((2 : Real) ^ t * φ)).natMod (2 ^ t),
    Int.natMod_lt (pow_ne_zero t (by norm_num : (2 : Nat) ≠ 0))⟩

lemma qpeNearestIndex_distance_le (t : Nat) (φ : Real) :
    qpePhaseDistance t φ (qpeNearestIndex t φ) ≤
      1 / (2 * (2 : Real) ^ t) := by
  let N : Nat := 2 ^ t
  let r : Int := round ((N : Real) * φ)
  let q : Nat := r.natMod N
  have hNpos : 0 < N := by
    dsimp [N]
    positivity
  have hNne : N ≠ 0 := hNpos.ne'
  have hmod_nonneg : 0 ≤ r % (N : Int) :=
    Int.emod_nonneg r (by exact_mod_cast hNne)
  have hqcast : (q : Int) = r % (N : Int) := by
    change (((r % (N : Int)).toNat : Nat) : Int) = r % (N : Int)
    exact Int.toNat_of_nonneg hmod_nonneg
  have hr : r = (r / (N : Int)) * (N : Int) + (q : Int) := by
    rw [hqcast]
    exact (Int.ediv_mul_add_emod r N).symm
  have hrReal :
      (r : Real) = ((r / (N : Int) : Int) : Real) * (N : Real) + (q : Real) := by
    exact_mod_cast hr
  have hNReal : (N : Real) ≠ 0 := by exact_mod_cast hNne
  have hrepr :
      φ - (q : Real) / (N : Real) =
        (((N : Real) * φ - (r : Real)) / (N : Real)) +
          ((r / (N : Int) : Int) : Real) := by
    rw [hrReal]
    field_simp [hNReal]
    ring
  have hperiod :
      ((((r / (N : Int) : Int) : Real)) : UnitAddCircle) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (p := (1 : Real))).2
    refine ⟨r / (N : Int), ?_⟩
    simp
  have hcircle :
      ((φ - (q : Real) / (N : Real) : Real) : UnitAddCircle) =
        ((((N : Real) * φ - (r : Real)) / (N : Real) : Real) :
          UnitAddCircle) := by
    rw [hrepr, AddCircle.coe_add, hperiod, add_zero]
  have hfinal :
      ‖((φ - (q : Real) / (N : Real) : Real) : UnitAddCircle)‖ ≤
        1 / (2 * (N : Real)) := by
    rw [hcircle]
    calc
      ‖((((N : Real) * φ - (r : Real)) / (N : Real) : Real) :
          UnitAddCircle)‖ ≤
          ‖((N : Real) * φ - (r : Real)) / (N : Real)‖ :=
        QuotientAddGroup.norm_mk_le_norm
      _ = |(N : Real) * φ - (r : Real)| / (N : Real) := by
        have hNabs : |(N : Real)| = (N : Real) :=
          abs_of_pos (by exact_mod_cast hNpos)
        rw [Real.norm_eq_abs, abs_div, hNabs]
      _ ≤ (1 / 2) / (N : Real) := by
        exact div_le_div_of_nonneg_right (abs_sub_round ((N : Real) * φ))
          (by positivity)
      _ = 1 / (2 * (N : Real)) := by ring
  simpa [qpePhaseDistance, qpeNearestIndex, q, r, N, Nat.cast_pow] using hfinal

/-- The real representative selected by rounding before reduction modulo the
dyadic grid.  Unlike the raw difference to the reduced index, this
representative is always in the nearest-cell interval. -/
def qpeRoundedError (t : Nat) (φ : Real) : Real :=
  (((2 : Real) ^ t * φ) - round ((2 : Real) ^ t * φ)) /
    (2 : Real) ^ t

lemma qpeRoundedError_abs_le (t : Nat) (φ : Real) :
    |qpeRoundedError t φ| ≤ 1 / (2 * (2 : Real) ^ t) := by
  have hpow : (0 : Real) < (2 : Real) ^ t := by positivity
  rw [qpeRoundedError, abs_div, abs_of_pos hpow]
  calc
    |(2 : Real) ^ t * φ - (round ((2 : Real) ^ t * φ) : Real)| /
          (2 : Real) ^ t <= (1 / 2) / (2 : Real) ^ t := by
      exact div_le_div_of_nonneg_right
        (abs_sub_round ((2 : Real) ^ t * φ)) hpow.le
    _ = 1 / (2 * (2 : Real) ^ t) := by ring

lemma qpeNearestIndex_error_eq_roundedError_add_int
    (t : Nat) (φ : Real) :
    exists z : Int,
      φ - ((qpeNearestIndex t φ).val : Real) / (2 : Real) ^ t =
        qpeRoundedError t φ + (z : Real) := by
  let N : Nat := 2 ^ t
  let r : Int := round ((N : Real) * φ)
  let q : Nat := r.natMod N
  have hNpos : 0 < N := by
    dsimp [N]
    positivity
  have hNne : N ≠ 0 := hNpos.ne'
  have hmod_nonneg : 0 ≤ r % (N : Int) :=
    Int.emod_nonneg r (by exact_mod_cast hNne)
  have hqcast : (q : Int) = r % (N : Int) := by
    change (((r % (N : Int)).toNat : Nat) : Int) = r % (N : Int)
    exact Int.toNat_of_nonneg hmod_nonneg
  have hr : r = (r / (N : Int)) * (N : Int) + (q : Int) := by
    rw [hqcast]
    exact (Int.ediv_mul_add_emod r N).symm
  have hrReal :
      (r : Real) = ((r / (N : Int) : Int) : Real) * (N : Real) + (q : Real) := by
    exact_mod_cast hr
  have hNReal : (N : Real) ≠ 0 := by exact_mod_cast hNne
  have hrepr :
      φ - (q : Real) / (N : Real) =
        (((N : Real) * φ - (r : Real)) / (N : Real)) +
          ((r / (N : Int) : Int) : Real) := by
    rw [hrReal]
    field_simp [hNReal]
    ring
  refine ⟨r / (N : Int), ?_⟩
  simpa [qpeNearestIndex, qpeRoundedError, q, r, N, Nat.cast_pow] using hrepr

/-- The normalized geometric-sum amplitude expressed in terms of one phase
error representative. -/
def qpeErrorAmplitude (t : Nat) (δ : Real) : ℂ :=
  (((2 ^ t : Nat) : ℂ))⁻¹ *
    ∑ k : Fin (2 ^ t),
      Complex.exp (2 * Real.pi *
        ((((k.val : Real) * δ : Real)) : ℂ) * Complex.I)

lemma phaseRegisterGeometricAmplitude_nearest_eq_errorAmplitude
    (t : Nat) (φ : Real) :
    phaseRegisterGeometricAmplitude t φ (qpeNearestIndex t φ) =
      qpeErrorAmplitude t (qpeRoundedError t φ) := by
  obtain ⟨z, hz⟩ :=
    qpeNearestIndex_error_eq_roundedError_add_int t φ
  rw [phaseRegisterGeometricAmplitude, qpeErrorAmplitude]
  have hscalar : (((2 : Real) ^ t : Complex)) = ((2 ^ t : Nat) : Complex) := by
    norm_num
  rw [hscalar]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [hz]
  have hexponent :
      2 * Real.pi *
          ((((qpeRoundedError t φ + (z : Real)) * k.val : Real)) : Complex) *
          Complex.I =
        2 * Real.pi *
            ((((k.val : Real) * qpeRoundedError t φ : Real)) : Complex) *
            Complex.I +
          ((z * (k.val : Int) : Int) : Complex) *
            (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [hexponent, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma qpeErrorAmplitude_norm_lower_bound (t : Nat) (δ : Real)
    (hdelta : |δ| ≤ 1 / (2 * (2 : Real) ^ t)) :
    2 / Real.pi ≤ ‖qpeErrorAmplitude t δ‖ := by
  let N : Nat := 2 ^ t
  have hNpos : 0 < N := by
    dsimp [N]
    positivity
  have hNReal : (0 : Real) < N := by exact_mod_cast hNpos
  by_cases hzero : δ = 0
  · subst δ
    have hamp : qpeErrorAmplitude t 0 = 1 := by
      simp [qpeErrorAmplitude]
    rw [hamp, norm_one]
    exact (div_le_one Real.pi_pos).2 Real.two_le_pi
  · have hNdelta : (N : Real) * |δ| ≤ 1 / 2 := by
      calc
        (N : Real) * |δ| ≤
            (N : Real) * (1 / (2 * (N : Real))) := by
          apply mul_le_mul_of_nonneg_left
          · simpa [N, Nat.cast_pow] using hdelta
          · positivity
        _ = 1 / 2 := by field_simp
    have hNge : (1 : Real) ≤ N := by exact_mod_cast hNpos
    have hangle :
        Real.pi * ((N : Real) * |δ|) ≤ Real.pi / 2 := by
      nlinarith [Real.pi_pos]
    have hbase : Complex.exp (2 * Real.pi * δ * Complex.I) ≠ 1 := by
      intro hexp
      obtain ⟨z, hz⟩ := Complex.exp_eq_one_iff.mp hexp
      have hzreal : δ = (z : Real) := by
        let C : ℂ := (2 * Real.pi : ℂ) * Complex.I
        have hC : C ≠ 0 := by
          exact mul_ne_zero (by exact_mod_cast Real.two_pi_pos.ne') Complex.I_ne_zero
        have hz' : (δ : ℂ) * C = (z : ℂ) * C := by
          dsimp [C]
          calc
            (δ : ℂ) * ((2 * Real.pi : ℂ) * Complex.I) =
                2 * Real.pi * δ * Complex.I := by ring
            _ = (z : ℂ) * (2 * Real.pi * Complex.I) := hz
            _ = (z : ℂ) * ((2 * Real.pi : ℂ) * Complex.I) := by ring
        have hcast : (δ : ℂ) = (z : ℂ) := mul_right_cancel₀ hC hz'
        have hre := congrArg Complex.re hcast
        simpa using hre
      have hz_ne : z ≠ 0 := by
        intro hz0
        apply hzero
        rw [hzreal, hz0]
        norm_num
      have hzabs : (1 : Real) ≤ |(z : Real)| := by
        exact_mod_cast Int.one_le_abs hz_ne
      have hdeltalt : |δ| < 1 := by
        calc
          |δ| ≤ 1 / (2 * (N : Real)) := by
            simpa [N, Nat.cast_pow] using hdelta
          _ ≤ 1 / 2 := by
            exact one_div_le_one_div_of_le (by norm_num : (0 : Real) < 2)
              (by nlinarith)
          _ < 1 := by norm_num
      rw [hzreal] at hdeltalt
      linarith
    have hratio :=
      geometric_phase_norm_ratio_lower_bound_of_angle_le
        (θ := δ) (A := Real.pi / 2) (m := N)
        Real.pi_div_two_pos (by linarith [Real.pi_pos]) hangle hbase
    have hratio' :
        (N : Real) * (2 / Real.pi) ≤
          ‖Complex.exp (2 * Real.pi * δ * Complex.I) ^ N - 1‖ /
            ‖Complex.exp (2 * Real.pi * δ * Complex.I) - 1‖ := by
      convert hratio using 1
      rw [Real.sin_pi_div_two]
      field_simp [Real.pi_ne_zero]
    have hclosed :
        qpeErrorAmplitude t δ =
          ((N : ℂ))⁻¹ *
            ((Complex.exp (2 * Real.pi * δ * Complex.I) ^ N - 1) /
              (Complex.exp (2 * Real.pi * δ * Complex.I) - 1)) := by
      rw [qpeErrorAmplitude]
      change ((N : ℂ))⁻¹ * _ = _
      rw [Fin.sum_univ_eq_sum_range (fun b : Nat =>
        Complex.exp (2 * Real.pi * ((((b : Real) * δ : Real)) : ℂ) * Complex.I))]
      rw [sum_range_exp_two_pi_mul_nat_mul_I_eq_geom_closed hbase]
    rw [hclosed, norm_mul, norm_inv, norm_natCast, norm_div]
    calc
      2 / Real.pi = (N : Real)⁻¹ * ((N : Real) * (2 / Real.pi)) := by
        field_simp [ne_of_gt hNReal, Real.pi_ne_zero]
      _ ≤ (N : Real)⁻¹ *
          (‖Complex.exp (2 * Real.pi * δ * Complex.I) ^ N - 1‖ /
            ‖Complex.exp (2 * Real.pi * δ * Complex.I) - 1‖) := by
        exact mul_le_mul_of_nonneg_left hratio' (by positivity)

/-! ### High-confidence cyclic phase-window tail -/

/-- Principal representative of the phase-grid error in `[-1/2, 1/2]`. -/
def qpePrincipalError (t : Nat) (φ : Real) (j : Fin (2 ^ t)) : Real :=
  let δ := φ - (j.val : Real) / (2 : Real) ^ t
  δ - round δ

lemma qpePrincipalError_abs_le (t : Nat) (φ : Real)
    (j : Fin (2 ^ t)) :
    |qpePrincipalError t φ j| <= 1 / 2 := by
  simpa [qpePrincipalError] using
    abs_sub_round (φ - (j.val : Real) / (2 : Real) ^ t)

/-- Periodic phase distance is the absolute value of the principal error. -/
lemma qpePhaseDistance_eq_abs_principalError (t : Nat) (φ : Real)
    (j : Fin (2 ^ t)) :
    qpePhaseDistance t φ j = |qpePrincipalError t φ j| := by
  rw [qpePhaseDistance, UnitAddCircle.norm_eq]
  rfl

/-- Reducing the raw phase error to its principal representative does not
change the finite geometric amplitude. -/
lemma phaseRegisterGeometricAmplitude_eq_principalError
    (t : Nat) (φ : Real) (j : Fin (2 ^ t)) :
    phaseRegisterGeometricAmplitude t φ j =
      qpeErrorAmplitude t (qpePrincipalError t φ j) := by
  let δ : Real := φ - (j.val : Real) / (2 : Real) ^ t
  let z : Int := round δ
  have hdelta : δ = qpePrincipalError t φ j + (z : Real) := by
    simp only [qpePrincipalError, δ, z]
    ring
  rw [phaseRegisterGeometricAmplitude, qpeErrorAmplitude]
  have hscalar : (((2 : Real) ^ t : Complex)) = ((2 ^ t : Nat) : Complex) := by
    norm_num
  rw [hscalar]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [show φ - (j.val : Real) / (2 : Real) ^ t = δ by rfl, hdelta]
  have hexponent :
      2 * Real.pi *
          (((((qpePrincipalError t φ j + (z : Real)) * k.val : Real))) :
            Complex) * Complex.I =
        2 * Real.pi *
            ((((k.val : Real) * qpePrincipalError t φ j : Real)) : Complex) *
            Complex.I +
          ((z * (k.val : Int) : Int) : Complex) *
            (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [hexponent, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Away from an exact grid point, a QPE geometric amplitude is bounded by
the reciprocal principal phase distance [Lin22, phaseestimation.tex:647-715]. -/
lemma phaseRegisterGeometricAmplitude_norm_le
    (t : Nat) (φ : Real) (j : Fin (2 ^ t))
    (hdistance : 0 < qpePhaseDistance t φ j) :
    ‖phaseRegisterGeometricAmplitude t φ j‖ <=
      1 / (2 * (2 : Real) ^ t * qpePhaseDistance t φ j) := by
  let δ := qpePrincipalError t φ j
  let N : Nat := 2 ^ t
  have hNpos : 0 < N := by
    dsimp [N]
    positivity
  have hNreal : (0 : Real) < N := by exact_mod_cast hNpos
  have hdelta_abs : |δ| <= 1 / 2 := by
    simpa [δ] using qpePrincipalError_abs_le t φ j
  have hdelta_pos : 0 < |δ| := by
    simpa [qpePhaseDistance_eq_abs_principalError, δ] using hdistance
  have harg : |2 * Real.pi * δ| <= Real.pi := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2),
      abs_of_nonneg Real.pi_pos.le]
    nlinarith [Real.pi_pos]
  have hden :=
    two_div_pi_mul_abs_le_norm_exp_ofReal_mul_I_sub_one harg
  have hden' :
      4 * |δ| <=
        ‖Complex.exp (2 * Real.pi * δ * Complex.I) - 1‖ := by
    calc
      4 * |δ| =
          (2 / Real.pi) * |2 * Real.pi * δ| := by
        rw [abs_mul, abs_mul,
          abs_of_pos (by norm_num : (0 : Real) < 2),
          abs_of_pos Real.pi_pos]
        field_simp [Real.pi_ne_zero]
        ring
      _ <= ‖Complex.exp
          (((2 * Real.pi * δ : Real) : Complex) * Complex.I) - 1‖ := hden
      _ = ‖Complex.exp (2 * Real.pi * δ * Complex.I) - 1‖ := by
        congr 3
        push_cast
        ring
  have hden_pos :
      0 < ‖Complex.exp (2 * Real.pi * δ * Complex.I) - 1‖ :=
    (mul_pos (by norm_num) hdelta_pos).trans_le hden'
  have hbase : Complex.exp (2 * Real.pi * δ * Complex.I) ≠ 1 := by
    exact sub_ne_zero.mp (norm_pos_iff.mp hden_pos)
  have hclosed :
      qpeErrorAmplitude t δ =
        ((N : Complex))⁻¹ *
          ((Complex.exp (2 * Real.pi * δ * Complex.I) ^ N - 1) /
            (Complex.exp (2 * Real.pi * δ * Complex.I) - 1)) := by
    rw [qpeErrorAmplitude]
    change ((N : Complex))⁻¹ * _ = _
    rw [Fin.sum_univ_eq_sum_range (fun b : Nat =>
      Complex.exp (2 * Real.pi * ((((b : Real) * δ : Real)) : Complex) *
        Complex.I))]
    rw [sum_range_exp_two_pi_mul_nat_mul_I_eq_geom_closed hbase]
  have hnum :
      ‖Complex.exp (2 * Real.pi * δ * Complex.I) ^ N - 1‖ <= 2 := by
    have hexp_norm :
        ‖Complex.exp (2 * Real.pi * δ * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      norm_num
    calc
      ‖Complex.exp (2 * Real.pi * δ * Complex.I) ^ N - 1‖ <=
          ‖Complex.exp (2 * Real.pi * δ * Complex.I) ^ N‖ + ‖(1 : Complex)‖ :=
        norm_sub_le _ _
      _ = 2 := by
        rw [norm_pow, hexp_norm, one_pow, norm_one]
        norm_num
  rw [phaseRegisterGeometricAmplitude_eq_principalError, show
    qpePrincipalError t φ j = δ by rfl, hclosed, norm_mul, norm_inv,
    norm_natCast, norm_div]
  have hratio :
      ‖Complex.exp (2 * Real.pi * δ * Complex.I) ^ N - 1‖ /
          ‖Complex.exp (2 * Real.pi * δ * Complex.I) - 1‖ <=
        2 / (4 * |δ|) := by
    exact div_le_div₀ (by norm_num) hnum
      (mul_pos (by norm_num) hdelta_pos) hden'
  calc
    (N : Real)⁻¹ *
          (‖Complex.exp (2 * Real.pi * δ * Complex.I) ^ N - 1‖ /
            ‖Complex.exp (2 * Real.pi * δ * Complex.I) - 1‖) <=
        (N : Real)⁻¹ * (2 / (4 * |δ|)) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = 1 / (2 * (2 : Real) ^ t * qpePhaseDistance t φ j) := by
      rw [qpePhaseDistance_eq_abs_principalError]
      change (N : Real)⁻¹ * (2 / (4 * |δ|)) =
        1 / (2 * (2 : Real) ^ t * |δ|)
      norm_num [N, Nat.cast_pow]
      field_simp [ne_of_gt hNreal, ne_of_gt hdelta_pos]
      ring

/-- Integer lift of a cyclic grid point selected by its principal phase
representative.  Different grid indices have different lifts modulo `2^t`. -/
def qpeLiftedGridIndex (t : Nat) (φ : Real) (j : Fin (2 ^ t)) : Int :=
  (j.val : Int) + (2 ^ t : Nat) *
    round (φ - (j.val : Real) / (2 : Real) ^ t)

private lemma qpeLiftedGridIndex_emod (t : Nat) (φ : Real)
    (j : Fin (2 ^ t)) :
    qpeLiftedGridIndex t φ j % (2 ^ t : Nat) = (j.val : Int) := by
  rw [qpeLiftedGridIndex, Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt (Int.natCast_nonneg j.val)
    (Int.ofNat_lt_ofNat_of_lt j.isLt)

lemma qpeLiftedGridIndex_injective (t : Nat) (φ : Real) :
    Function.Injective (qpeLiftedGridIndex t φ) := by
  intro left right h
  apply Fin.ext
  have hmod := congrArg (fun z : Int => z % (2 ^ t : Nat)) h
  rw [qpeLiftedGridIndex_emod, qpeLiftedGridIndex_emod] at hmod
  exact_mod_cast hmod

lemma qpePrincipalError_scaled (t : Nat) (φ : Real)
    (j : Fin (2 ^ t)) :
    (2 : Real) ^ t * qpePrincipalError t φ j =
      (2 : Real) ^ t * φ - (qpeLiftedGridIndex t φ j : Real) := by
  rw [qpePrincipalError, qpeLiftedGridIndex]
  norm_num [Nat.cast_pow]
  field_simp [pow_ne_zero t (by norm_num : (2 : Real) ≠ 0)]
  ring

/-- Real probability mass of the phase-grid indices outside periodic radius
`rho`. -/
def qpeBadIndexMass (t : Nat) (φ ρ : Real) : Real :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin (2 ^ t) =>
      ρ <= qpePhaseDistance t φ j),
    ‖phaseRegisterGeometricAmplitude t φ j‖ ^ 2

/-- The two cyclic grid tails obey the source reciprocal-square bound for every
positive radius and arbitrary eigenphase [Lin22,
phaseestimation.tex:647-715]. -/
lemma qpeBadIndexMass_le (t : Nat) (φ ρ : Real) (hrho : 0 < ρ) :
    qpeBadIndexMass t φ ρ <=
      1 / (2 * (2 : Real) ^ t * ρ) +
        1 / (2 * ((2 : Real) ^ t * ρ) ^ 2) := by
  classical
  let bad := Finset.univ.filter (fun j : Fin (2 ^ t) =>
    ρ <= qpePhaseDistance t φ j)
  let lifted := bad.image (qpeLiftedGridIndex t φ)
  let T : Real := (2 : Real) ^ t
  have hTpos : 0 < T := by
    dsimp [T]
    positivity
  have hscaledDistance (j : Fin (2 ^ t)) :
      T * qpePhaseDistance t φ j =
        |T * φ - (qpeLiftedGridIndex t φ j : Real)| := by
    rw [qpePhaseDistance_eq_abs_principalError]
    have h := congrArg abs (qpePrincipalError_scaled t φ j)
    simpa [T, abs_mul, abs_of_pos hTpos] using h
  have hpointwise :
      (∑ j ∈ bad, ‖phaseRegisterGeometricAmplitude t φ j‖ ^ 2) <=
        ∑ j ∈ bad,
          (1 / (4 * |T * φ - (qpeLiftedGridIndex t φ j : Real)| ^ 2)) := by
    apply Finset.sum_le_sum
    intro j hj
    have hbad : ρ <= qpePhaseDistance t φ j :=
      (Finset.mem_filter.mp hj).2
    have hdistance : 0 < qpePhaseDistance t φ j := hrho.trans_le hbad
    have hamp := phaseRegisterGeometricAmplitude_norm_le t φ j hdistance
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hamp 2
    calc
      ‖phaseRegisterGeometricAmplitude t φ j‖ ^ 2 <=
          (1 / (2 * T * qpePhaseDistance t φ j)) ^ 2 := by
        simpa [T] using hsquare
      _ = 1 / (4 * |T * φ - (qpeLiftedGridIndex t φ j : Real)| ^ 2) := by
        rw [← hscaledDistance]
        field_simp [ne_of_gt hTpos, ne_of_gt hdistance]
        ring
  have hfar : ∀ z ∈ lifted,
      T * ρ <= |T * φ - (z : Real)| := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    have hbad : ρ <= qpePhaseDistance t φ j :=
      (Finset.mem_filter.mp hj).2
    rw [← hscaledDistance]
    exact mul_le_mul_of_nonneg_left hbad hTpos.le
  have htail := integerReciprocalSquareTail_le lifted (T * φ) (T * ρ)
    (mul_pos hTpos hrho) hfar
  have hsum_image :
      (∑ j ∈ bad,
          1 / |T * φ - (qpeLiftedGridIndex t φ j : Real)| ^ 2) =
        ∑ z ∈ lifted, 1 / |T * φ - (z : Real)| ^ 2 := by
    rw [Finset.sum_image (qpeLiftedGridIndex_injective t φ).injOn]
  calc
    qpeBadIndexMass t φ ρ =
        ∑ j ∈ bad, ‖phaseRegisterGeometricAmplitude t φ j‖ ^ 2 := rfl
    _ <= ∑ j ∈ bad,
        1 / (4 * |T * φ - (qpeLiftedGridIndex t φ j : Real)| ^ 2) :=
      hpointwise
    _ = (1 / 4) *
        ∑ z ∈ lifted, 1 / |T * φ - (z : Real)| ^ 2 := by
      rw [← hsum_image, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ <= (1 / 4) * (2 / (T * ρ) + 2 / (T * ρ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left htail (by norm_num)
    _ = 1 / (2 * (2 : Real) ^ t * ρ) +
        1 / (2 * ((2 : Real) ^ t * ρ) ^ 2) := by
      dsimp [T]
      field_simp [ne_of_gt hrho, pow_ne_zero t (by norm_num : (2 : Real) ≠ 0)]
      ring

end

end QuantumAlg

end
