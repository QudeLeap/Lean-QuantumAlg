/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.Matrix.SymmetricStochastic
public import QuantumAlg.Core.Base
import all QuantumAlg.Core.Base
import all QuantumAlg.Core.Base.State.Basic
import all QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Core.Base.Gate.Basic
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Core.Base.Tensor.Certified
public import QuantumAlg.Util.FinPow
import all QuantumAlg.Util.FinPow
public import QuantumAlg.Components.Oracle.Reflection
import all QuantumAlg.Components.Oracle.Reflection
public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.Analysis.Normed.Lp.WithLp

/-!
# Two-reflection walk operators and search geometry

The normalized square-root rows of a symmetric stochastic matrix define two isometries
and their edge-space reflection product [dW19, qcnotes.tex:3208-3318].
-/

section

namespace QuantumAlg.QuantumWalk

open NormalizedVector
open scoped BigOperators ComplexConjugate

noncomputable section

variable {n : ℕ}

/-! ### Step 1: Walk superposition `|pₓ⟩` -/

/-- `|pₓ⟩ = Σ_y √(P_{x,y}) |y⟩`, normalized superposition over neighbours. -/
private def walkStateFormula (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (x : Fin (2 ^ n)) :
    HilbertVector (Qubits n) :=
  WithLp.toLp 2 (fun y => (Real.sqrt (P.mat x y) : ℂ))

@[simp]
private theorem walkStateFormula_apply (P : Matrix.SymmetricStochastic (Fin (2 ^ n)))
    (x y : Fin (2 ^ n)) :
    walkStateFormula P x y = (Real.sqrt (P.mat x y) : ℂ) := (rfl)

private theorem walkStateFormula_norm_sq (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (x : Fin
  (2 ^ n)) :
    ‖walkStateFormula P x‖ ^ 2 = (1 : ℝ) := by
  calc
    ‖walkStateFormula P x‖ ^ 2 = ∑ y : Fin (2 ^ n), ‖(walkStateFormula P x) y‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin (2 ^ n) => ℂ) (walkStateFormula P x)]
    _ = ∑ y : Fin (2 ^ n), Complex.normSq ((Real.sqrt (P.mat x y) : ℂ)) := by
      simp [Complex.normSq_eq_norm_sq]
    _ = ∑ y : Fin (2 ^ n), (P.mat x y : ℝ) := by
      simp [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im, Real.mul_self_sqrt
      (P.nonneg x _)]
    _ = 1 := P.rowSum_one x

private theorem walkStateFormula_norm (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (x : Fin (2 ^
  n)) :
    ‖walkStateFormula P x‖ = 1 := by
  have h_sq : ‖walkStateFormula P x‖ ^ 2 = (1 : ℝ) := walkStateFormula_norm_sq P x
  have h_nonneg : 0 ≤ ‖walkStateFormula P x‖ := norm_nonneg _
  nlinarith

/-- The normalized square-root row of the transition matrix. -/
public def walkState (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (x : Fin (2 ^ n)) :
    NormalizedVector (Qubits n) :=
  NormalizedVector.ofVector (walkStateFormula P x) (walkStateFormula_norm P x)

@[simp]
public theorem walkState_apply (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (x y : Fin (2 ^ n)) :
    walkState P x y = (Real.sqrt (P.mat x y) : ℂ) := walkStateFormula_apply P x y

public theorem walkState_norm (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (x : Fin (2 ^ n)) :
    ‖(walkState P x : HilbertVector (Qubits n))‖ = 1 := (walkState P x).norm_eq_one

/-! ### Step 2: Isometries `VA`, `VB` -/

/-- Isometry `VA : H → H⊗H` given by `VA·|x⟩ = |x⟩ ⊗ |p_x⟩`.
Matrix form: `VA[(a,b), x] = δ_{a,x} · √(P_{x,b})`. -/
public def VA (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) : Matrix (Fin (2 ^ (n + n))) (Fin (2
  ^ n)) ℂ
  :=
  Matrix.of fun (edge : Fin (2 ^ (n + n))) (x : Fin (2 ^ n)) =>
    if (prodEquiv.symm edge).1 = x then
      (Real.sqrt (P.mat x (prodEquiv.symm edge).2) : ℂ)
    else 0

/-- Isometry `VB : H → H⊗H` given by `VB·|y⟩ = |p_y⟩ ⊗ |y⟩`.
Matrix form: `VB[(a,b), y] = δ_{b,y} · √(P_{y,a})`. -/
public def VB (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) : Matrix (Fin (2 ^ (n + n))) (Fin (2
  ^ n)) ℂ
  :=
  Matrix.of fun (edge : Fin (2 ^ (n + n))) (y : Fin (2 ^ n)) =>
    if (prodEquiv.symm edge).2 = y then
      (Real.sqrt (P.mat y (prodEquiv.symm edge).1) : ℂ)
    else 0

@[simp]
public theorem VA_apply (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (edge : Fin (2 ^ (n + n)))
  (x :
  Fin (2 ^ n)) :
    VA P edge x =
      if (prodEquiv.symm edge).1 = x then
        (Real.sqrt (P.mat x (prodEquiv.symm edge).2) : ℂ)
      else 0 :=
  (rfl)

@[simp]
public theorem VB_apply (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (edge : Fin (2 ^ (n + n)))
  (y :
  Fin (2 ^ n)) :
    VB P edge y =
      if (prodEquiv.symm edge).2 = y then
        (Real.sqrt (P.mat y (prodEquiv.symm edge).1) : ℂ)
      else 0 :=
  (rfl)

/-! ### Step 3: Isometry property `V†·V = I` -/

/-- Each term `conj (VA[a,b;x]) * VA[a,b;x']` simplifies:
  - When `x = x'`: `|√(P x b)|² = P x b` if `a = x`, else 0
  - When `x ≠ x'`: 0 (first-register labels cannot agree with both x and x') -/
private lemma VA_term (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (x x' a b : Fin (2 ^ n)) :
    star ((VA P) (prodEquiv (a, b)) x) * ((VA P) (prodEquiv (a, b)) x')
    = if a = x then if x = x' then (P.mat x b : ℂ) else (0 : ℂ) else (0 : ℂ) := by
  simp only [VA_apply, Complex.star_def]
  by_cases hax : a = x
  · rw [hax]
    by_cases hxx' : x = x'
    · rw [hxx']
      rw [Complex.ext_iff]
      simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Real.mul_self_sqrt (P.nonneg x' b)]
    · simp [hxx']
  · simp [hax]

/-- `VA†·VA = I`. The isometry property: inner product of column vectors
gives `δ_{x,x'}` because `⟨x|x'⟩ = δ` in the first register and `‖|p_x⟩‖ = 1`. -/
public theorem VA_conjTranspose_mul_VA (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) :
    (VA P).conjTranspose * (VA P) = (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) := by
  ext x x'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  rw [← Equiv.sum_comp (prodEquiv : Fin (2 ^ n) × Fin (2 ^ n) ≃ _)]
  rw [Fintype.sum_prod_type]
  simp only [VA_term P x x']
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  by_cases hxx' : x = x'
  · subst x'
    simp only [↓reduceIte]
    erw [← Complex.ofReal_sum]
    erw [P.rowSum_one x]
    rfl
  · simp_rw [if_neg hxx']

/-- Each term `conj (VB[a,b;y]) * VB[a,b;y']` simplifies:
  - When `y = y'`: `|√(P y a)|² = P y a = P a y` (by symmetry) if `b = y`, else 0
  - When `y ≠ y'`: 0 (second-register labels cannot agree with both y and y') -/
private lemma VB_term (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (y y' a b : Fin (2 ^ n)) :
    star ((VB P) (prodEquiv (a, b)) y) * ((VB P) (prodEquiv (a, b)) y')
    = if b = y then if y = y' then (P.mat y a : ℂ) else (0 : ℂ) else (0 : ℂ) := by
  simp only [VB_apply, Complex.star_def]
  by_cases hby : b = y
  · rw [hby]
    by_cases hyy' : y = y'
    · rw [hyy']
      rw [Complex.ext_iff]
      simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Real.mul_self_sqrt (P.nonneg y' a)]
    · simp [hyy']
  · simp [hby]
/-- `VB†·VB = I`. Symmetric to VA, with the orthogonal register in the second slot.
Using `colSum_one` (which follows from symmetry + rowSum_one) for the column sum. -/
public theorem VB_conjTranspose_mul_VB (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) :
    (VB P).conjTranspose * (VB P) = (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) := by
  ext y y'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  rw [← Equiv.sum_comp (prodEquiv : Fin (2 ^ n) × Fin (2 ^ n) ≃ _)]
  rw [Fintype.sum_prod_type]
  simp only [VB_term P y y']
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  by_cases hyy' : y = y'
  · subst y'
    simp only [↓reduceIte]
    erw [← Complex.ofReal_sum]
    erw [P.rowSum_one y]
    rfl
  · simp_rw [if_neg hyy']

/-! ### Step 4: Projectors `PA = VA·VA†`, `PB = VB·VB†` -/

/-- The A-subspace projector `PA = VA·VA† = Σ_x |x⟩⟨x| ⊗ |p_x⟩⟨p_x|`. -/
public def PA (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) : HilbertOperator (Qubits (n + n)) :=
  VA P * (VA P).conjTranspose

/-- The B-subspace projector `PB = VB·VB† = Σ_y |p_y⟩⟨p_y| ⊗ |y⟩⟨y|`. -/
public def PB (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) : HilbertOperator (Qubits (n + n)) :=
  VB P * (VB P).conjTranspose

public theorem PA_conjTranspose (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) : (PA
  P).conjTranspose =
  PA P := by
  simp [PA, Matrix.conjTranspose_mul]

public theorem PA_idempotent (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) : PA P * PA P = PA P
  := by
  calc
    PA P * PA P = VA P * (((VA P).conjTranspose * (VA P)) * (VA P).conjTranspose) := by
      simp [PA, Matrix.mul_assoc]
    _ = VA P * ((1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) * (VA P).conjTranspose) := by
      rw [VA_conjTranspose_mul_VA P]
    _ = PA P := by simp [PA]

public theorem PB_conjTranspose (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) : (PB
  P).conjTranspose =
  PB P := by
  simp [PB, Matrix.conjTranspose_mul]

public theorem PB_idempotent (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) : PB P * PB P = PB P
  := by
  calc
    PB P * PB P = VB P * (((VB P).conjTranspose * (VB P)) * (VB P).conjTranspose) := by
      simp [PB, Matrix.mul_assoc]
    _ = VB P * ((1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) * (VB P).conjTranspose) := by
      rw [VB_conjTranspose_mul_VB P]
    _ = PB P := by simp [PB]

/-- Bundle `PA` as an `OrthogonalProjector`. -/
public def projectorA (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) : OrthogonalProjector (n + n)
  where
  op := PA P
  selfAdjoint := PA_conjTranspose P
  idempotent := PA_idempotent P

/-- Bundle `PB` as an `OrthogonalProjector`. -/
public def projectorB (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) : OrthogonalProjector (n + n)
  where
  op := PB P
  selfAdjoint := PB_conjTranspose P
  idempotent := PB_idempotent P

/-! ### Step 5: Walk unitary `W(P) = ref(B)·ref(A)` -/

/-- The Szegedy quantum walk unitary on the edge space `H⊗H`. -/
public def walkUnitary (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) : UnitaryOperator (Qubits (n
  + n)) :=
  OrthogonalProjector.reflectionOp (projectorB P) *
  OrthogonalProjector.reflectionOp (projectorA P)


/-! ### Search geometry — good/bad/uniform edge states -/

variable (M : Finset (Fin (2 ^ n)))

/-- Edge basis state `|x⟩|pₓ⟩` as a state vector in the tensor-product edge space.
These `2ⁿ` vectors are pairwise orthogonal (first register is the basis ket). -/
public def edgeBasis (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (x : Fin (2 ^ n)) :
    NormalizedVector (Qubits (n + n)) :=
  NormalizedVector.tensor (NormalizedVector.ket x) (walkState P x)

@[simp]
theorem edgeBasis_coe (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (x : Fin (2 ^ n)) :
    (edgeBasis P x : HilbertVector (Qubits (n + n))) =
      HilbertVector.tensor (NormalizedVector.ket (R := Qubits n) x : HilbertVector (Qubits n))
        (walkState P x : HilbertVector (Qubits n)) := (rfl)

public lemma inner_ket_ket (x y : Fin (2 ^ n)) :
    inner ℂ (NormalizedVector.ket x : NormalizedVector (Qubits n)).1
      (NormalizedVector.ket y : NormalizedVector (Qubits n)).1 =
        if x = y then (1 : ℂ) else 0 := by
  simp [NormalizedVector.ket_apply, PiLp.inner_apply]
/-- `‖|x⟩|p_x⟩‖ = 1`. -/
public theorem edgeBasis_norm (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (x : Fin (2 ^ n)) :
    ‖(edgeBasis P x : HilbertVector (Qubits (n + n)))‖ = 1 := by
  rw [edgeBasis_coe, HilbertVector.norm_tensor, NormalizedVector.norm_ket, walkState_norm, one_mul]

/-- `⟨edgeBasis x | edgeBasis y⟩ = 0` for `x ≠ y`.
Orthogonality from the first-register ket `⟨x|y⟩ = 0`. -/
public theorem inner_edgeBasis_eq_zero_of_ne (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) {x y :
  Fin (2
  ^ n)} (hne : x ≠ y) :
    inner ℂ ((edgeBasis P x : HilbertVector (Qubits (n + n)))) ((edgeBasis P y : HilbertVector
      (Qubits (n + n)))) = 0 := by
  simp only [edgeBasis_coe]
  rw [HilbertVector.inner_tensor_tensor]
  rw [inner_ket_ket x y]
  rw [if_neg hne]
  rw [zero_mul]

/-- `⟨edgeBasis x | edgeBasis x⟩ = 1`. -/
public theorem inner_edgeBasis_self_eq_one (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (x : Fin
  (2 ^
  n)) :
    inner ℂ ((edgeBasis P x : HilbertVector (Qubits (n + n)))) ((edgeBasis P x : HilbertVector
      (Qubits (n + n)))) = 1 := by
  simp only [edgeBasis_coe]
  rw [HilbertVector.inner_tensor_tensor]
  rw [inner_ket_ket x x]
  simp [walkState_norm]

/-- Uniform edge superposition `|U⟩ = (1/√(2ⁿ))·Σₓ |x⟩|pₓ⟩`.
Norm is 1 because the `edgeBasis` vectors are orthonormal. -/
private def uniformEdgeStateFormula (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) : HilbertVector
  (Qubits (n + n)) :=
  ((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℂ) • (∑ x : Fin (2 ^ n), (edgeBasis P x : HilbertVector (Qubits
    (n + n))))

private theorem edgeBasis_sum_norm_sq
    (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (S : Finset (Fin (2 ^ n))) :
    ‖∑ x ∈ S, (edgeBasis P x : HilbertVector (Qubits (n + n)))‖ ^ 2 = (S.card : ℝ) := by
  have hinner :
      inner ℂ (∑ x ∈ S, (edgeBasis P x : HilbertVector (Qubits (n + n)))) (∑ y ∈ S, (edgeBasis P y
        : HilbertVector (Qubits (n + n)))) =
        (S.card : ℂ) := by
    calc
      inner ℂ (∑ x ∈ S, (edgeBasis P x : HilbertVector (Qubits (n + n)))) (∑ y ∈ S, (edgeBasis P y
        : HilbertVector (Qubits (n + n))))
          = ∑ x ∈ S, ∑ y ∈ S, inner ℂ ((edgeBasis P x : HilbertVector (Qubits (n + n))))
            ((edgeBasis P y : HilbertVector (Qubits (n + n)))) := by
        rw [sum_inner]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [inner_sum]
      _ = ∑ x ∈ S, (1 : ℂ) := by
        refine Finset.sum_congr rfl (fun x hx => ?_)
        rw [Finset.sum_eq_single x]
        · rw [inner_edgeBasis_self_eq_one P x]
        · intro y _ hne
          exact inner_edgeBasis_eq_zero_of_ne P hne.symm
        · intro hx'
          exact False.elim (hx' hx)
      _ = (S.card : ℂ) := by simp
  have hre :
      RCLike.re (inner ℂ (∑ x ∈ S, (edgeBasis P x : HilbertVector (Qubits (n + n)))) (∑ y ∈ S,
        (edgeBasis P y : HilbertVector (Qubits (n + n))))) =
        (S.card : ℝ) := by
    rw [hinner]
    simp
  rwa [inner_self_eq_norm_sq] at hre

private theorem edgeBasis_sum_norm
    (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (S : Finset (Fin (2 ^ n))) :
    ‖∑ x ∈ S, (edgeBasis P x : HilbertVector (Qubits (n + n)))‖ = Real.sqrt (S.card : ℝ) := by
  have h_sq := edgeBasis_sum_norm_sq P S
  have h_nonneg : 0 ≤ ‖∑ x ∈ S, (edgeBasis P x : HilbertVector (Qubits (n + n)))‖ := norm_nonneg _
  have h_sq' :
      ‖∑ x ∈ S, (edgeBasis P x : HilbertVector (Qubits (n + n)))‖ ^ 2 =
        Real.sqrt (S.card : ℝ) ^ 2 := by
    rw [h_sq, Real.sq_sqrt (by positivity)]
  have h_sqrt := congrArg Real.sqrt h_sq'
  rw [Real.sqrt_sq h_nonneg] at h_sqrt
  rw [Real.sqrt_sq (Real.sqrt_nonneg _)] at h_sqrt
  exact h_sqrt

private theorem edgeBasis_univ_sum_inner
    (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (S : Finset (Fin (2 ^ n))) :
    inner ℂ (∑ x : Fin (2 ^ n), (edgeBasis P x : HilbertVector (Qubits (n + n)))) (∑ y ∈ S,
      (edgeBasis P y : HilbertVector (Qubits (n + n)))) =
      (S.card : ℂ) := by
  calc
    inner ℂ (∑ x : Fin (2 ^ n), (edgeBasis P x : HilbertVector (Qubits (n + n)))) (∑ y ∈ S,
      (edgeBasis P y : HilbertVector (Qubits (n + n))))
        = ∑ x : Fin (2 ^ n), ∑ y ∈ S, inner ℂ ((edgeBasis P x : HilbertVector (Qubits (n + n))))
          ((edgeBasis P y : HilbertVector (Qubits (n + n)))) := by
      rw [sum_inner]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [inner_sum]
    _ = ∑ y ∈ S, (1 : ℂ) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y hy => ?_)
      rw [Finset.sum_eq_single y]
      · rw [inner_edgeBasis_self_eq_one P y]
      · intro x _ hne
        exact inner_edgeBasis_eq_zero_of_ne P hne
      · intro hy'
        exact False.elim (hy' (Finset.mem_univ y))
    _ = (S.card : ℂ) := by simp

private theorem inv_sqrt_mul_inv_sqrt_mul_eq_sqrt_div
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (Real.sqrt b)⁻¹ * ((Real.sqrt a)⁻¹ * b) = Real.sqrt b / Real.sqrt a := by
  have hsqrta_ne : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ha)
  have hsqrtb_ne : Real.sqrt b ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hb)
  have hb_cancel : (Real.sqrt b)⁻¹ * b = Real.sqrt b := by
    apply mul_left_cancel₀ hsqrtb_ne
    calc
      Real.sqrt b * ((Real.sqrt b)⁻¹ * b)
          = (Real.sqrt b * (Real.sqrt b)⁻¹) * b := by ring
      _ = b := by rw [mul_inv_cancel₀ hsqrtb_ne, one_mul]
      _ = Real.sqrt b * Real.sqrt b := by
        rw [← sq, Real.sq_sqrt (le_of_lt hb)]
  calc
    (Real.sqrt b)⁻¹ * ((Real.sqrt a)⁻¹ * b)
        = (Real.sqrt a)⁻¹ * ((Real.sqrt b)⁻¹ * b) := by ring
    _ = (Real.sqrt a)⁻¹ * Real.sqrt b := by
      rw [hb_cancel]
    _ = Real.sqrt b / Real.sqrt a := by
      rw [div_eq_mul_inv, mul_comm]

/-- `‖|U⟩‖ = 1`. Orthonormal basis → sum norm = √N → 1/√N·sum norm = 1. -/
private theorem uniformEdgeStateFormula_norm (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) :
  ‖uniformEdgeStateFormula P‖ = 1 := by
  rw [uniformEdgeStateFormula, norm_smul]
  have h_sum_norm :
      ‖∑ x : Fin (2 ^ n), (edgeBasis P x : HilbertVector (Qubits (n + n)))‖ = Real.sqrt ((2 : ℝ) ^
        n) := by
    simpa [Finset.card_univ, Fintype.card_fin] using
      edgeBasis_sum_norm P (Finset.univ : Finset (Fin (2 ^ n)))
  have h_abs_c :
      ‖((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℂ)‖ =
        (Real.sqrt ((2 : ℝ) ^ n))⁻¹ := by
    simp [abs_of_nonneg]
  rw [h_abs_c, h_sum_norm]
  exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
/-- Uniform normalized superposition of the orthonormal edge states. -/
public def uniformEdgeState (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) :
    NormalizedVector (Qubits (n + n)) :=
  NormalizedVector.ofVector (uniformEdgeStateFormula P) (uniformEdgeStateFormula_norm P)

@[simp]
public theorem uniformEdgeState_coe (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) :
    (uniformEdgeState P : HilbertVector (Qubits (n + n))) =
      ((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℂ) •
        (∑ x : Fin (2 ^ n), (edgeBasis P x : HilbertVector (Qubits (n + n)))) := (rfl)

public theorem uniformEdgeState_norm (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) :
    ‖(uniformEdgeState P : HilbertVector (Qubits (n + n)))‖ = 1 :=
  (uniformEdgeState P).norm_eq_one

/-- Good state `|G⟩ = (1/√|M|)·Σ_{x∈M} |x⟩|pₓ⟩` (marked edges).
Requires `M` nonempty. -/
public def goodState (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (M : Finset (Fin (2 ^ n))) :
  HilbertVector (Qubits (n + n))
:=
  ((Real.sqrt (M.card : ℝ))⁻¹ : ℂ) • (∑ x ∈ M, (edgeBasis P x : HilbertVector (Qubits (n + n))))

/-- Bad state `|B⟩ = (1/√(2ⁿ-|M|))·Σ_{x∉M} |x⟩|pₓ⟩` (unmarked edges).
Requires `M ≠ univ`. -/
public def badState (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (M : Finset (Fin (2 ^ n))) :
  HilbertVector (Qubits (n + n)) :=
  ((Real.sqrt (((2 : ℝ) ^ n) - (M.card : ℝ)))⁻¹ : ℂ) •
    (∑ x ∈ (Finset.univ : Finset (Fin (2 ^ n))) \ M, (edgeBasis P x : HilbertVector (Qubits (n +
      n))))
/-- Outer product `|ψ⟩⟨ψ|` for a state vector. -/
public def outerProductOp (ψ : HilbertVector (Qubits (n + n))) : HilbertOperator (Qubits (n + n)) :=
  Matrix.of fun i j => ψ i * conj (ψ j)

/-- Ideal reflection through `|U⟩`: `ref_U = 2|U⟩⟨U| - I`. -/
public def idealRefUOp (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) :
    UnitaryOperator (Qubits (n + n)) :=
  OrthogonalProjector.reflectionOp (OrthogonalProjector.rankOne (uniformEdgeState P))

@[simp]
public theorem idealRefUOp_coe (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) :
    (idealRefUOp P : HilbertOperator (Qubits (n + n))) =
      (2 : ℂ) • outerProductOp (uniformEdgeState P : HilbertVector (Qubits (n + n))) - 1 := (rfl)

/-- The marked subspace projector `P_M = Σ_{x∈M} |x⟩⟨x| ⊗ I`.
Each term is an orthogonal projector; different x terms are orthogonal. -/
public def markedProjectorOp (M : Finset (Fin (2 ^ n))) :
    HilbertOperator (Qubits (n + n)) :=
  ∑ x ∈ M, HilbertOperator.tensor (OrthogonalProjector.basisOp x) (1 : HilbertOperator (Qubits n))

/-- `‖|G⟩‖ = 1`: normalized sum over `|M|` orthogonal `edgeBasis` vectors.
Same proof pattern as `uniformEdgeState_norm`, restricted to the subset `M`. -/
public theorem goodState_norm (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (M : Finset (Fin (2 ^
  n)))
  (hM_nonempty :
M.Nonempty) :
    ‖goodState P M‖ = 1 := by
  rw [goodState, norm_smul]
  have h_abs_c :
      ‖((Real.sqrt (M.card : ℝ))⁻¹ : ℂ)‖ =
        (Real.sqrt (M.card : ℝ))⁻¹ := by
    simp [abs_of_nonneg]
  rw [h_abs_c, edgeBasis_sum_norm]
  exact inv_mul_cancel₀
    (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast Finset.card_pos.mpr hM_nonempty)))

/-- `‖|B⟩‖ = 1`: normalized sum over `N-|M|` orthogonal `edgeBasis` vectors. -/
public theorem badState_norm (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (M : Finset (Fin (2 ^
  n)))
  (hM_proper : M ≠
Finset.univ) :
    ‖badState P M‖ = 1 := by
  set S := (Finset.univ : Finset (Fin (2 ^ n))) \ M with hS
  have h_card_S_nat : S.card = 2 ^ n - M.card := by
    simp [hS, Finset.card_sdiff]
  have h_card_S :
      (S.card : ℝ) = ((2 : ℝ) ^ n) - (M.card : ℝ) := by
    have hM_le : M.card ≤ 2 ^ n := by
      simpa [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_univ M
    rw [h_card_S_nat]
    simpa using (Nat.cast_sub (R := ℝ) hM_le)
  have hS_nonempty : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h_empty
    have h_subset : (Finset.univ : Finset (Fin (2 ^ n))) ⊆ M := by
      intro x _
      by_contra hxM
      have hxS : x ∈ S := by simp [hS, hxM]
      rw [h_empty] at hxS
      simp at hxS
    apply hM_proper
    exact Finset.eq_univ_iff_forall.mpr
      (fun x => h_subset (Finset.mem_univ x))
  rw [badState, norm_smul]
  have h_abs_c :
      ‖((Real.sqrt (((2 : ℝ) ^ n) - (M.card : ℝ)))⁻¹ : ℂ)‖ =
        (Real.sqrt (((2 : ℝ) ^ n) - (M.card : ℝ)))⁻¹ := by
    simp [abs_of_nonneg]
  rw [h_abs_c]
  have h_sum_norm :
      ‖∑ x ∈ (Finset.univ : Finset (Fin (2 ^ n))) \ M, (edgeBasis P x : HilbertVector (Qubits (n +
        n)))‖ =
        Real.sqrt (((2 : ℝ) ^ n) - (M.card : ℝ)) := by
    rw [← hS]
    rw [edgeBasis_sum_norm, h_card_S]
  rw [h_sum_norm]
  exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by
    rw [← h_card_S]
    exact_mod_cast Finset.card_pos.mpr hS_nonempty)))

/-- `⟨G|B⟩ = 0` — good/bad states are orthogonal because the index sets `M` and `univ\M` are
disjoint. -/
public theorem goodState_inner_badState_eq_zero (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (M :
  Finset (Fin (2 ^ n))) :
    inner ℂ (goodState P M) (badState P M) = 0 := by
  set S := (Finset.univ : Finset (Fin (2 ^ n))) \ M with hS
  rw [goodState, badState]
  simp only [inner_smul_right, inner_smul_left]
  suffices
      inner ℂ (∑ x ∈ M, (edgeBasis P x : HilbertVector (Qubits (n + n)))) (∑ y ∈ S, (edgeBasis P y
        : HilbertVector (Qubits (n + n)))) = 0 by
    rw [← hS]
    rw [this]
    simp
  calc
    inner ℂ (∑ x ∈ M, (edgeBasis P x : HilbertVector (Qubits (n + n)))) (∑ y ∈ S, (edgeBasis P y :
      HilbertVector (Qubits (n + n))))
        = ∑ x ∈ M, ∑ y ∈ S, inner ℂ ((edgeBasis P x : HilbertVector (Qubits (n + n)))) ((edgeBasis
          P y : HilbertVector (Qubits (n + n)))) := by
      rw [sum_inner]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [inner_sum]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      apply Finset.sum_eq_zero
      intro y hy
      have hne : x ≠ y := by
        intro hxy
        subst y
        have hx_not_mem : x ∉ M := by
          simpa [hS] using hy
        exact hx_not_mem hx
      exact inner_edgeBasis_eq_zero_of_ne P hne

/-- `⟨U|G⟩ = √(|M|/2ⁿ)`. Inner product of uniform and good edge states.
Each `e_x` is orthogonal/normalized, so `⟨Σ_univ e_x | Σ_M e_y⟩ = |M|`.
Requires `M` nonempty for the `|G⟩` normalization. -/
public theorem uniformEdgeState_inner_goodState (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (M :
  Finset (Fin (2 ^ n)))
    (hM_nonempty : M.Nonempty) :
    inner ℂ ((uniformEdgeState P : HilbertVector (Qubits (n + n)))) (goodState P M) =
      Real.sqrt ((M.card : ℝ) / ((2 : ℝ) ^ n)) := by
  have hN_pos : 0 < ((2 : ℝ) ^ n) := by positivity
  have hM_pos : 0 < (M.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hM_nonempty
  rw [uniformEdgeState_coe, goodState]
  simp only [inner_smul_right, inner_smul_left]
  rw [edgeBasis_univ_sum_inner P M]
  norm_num
  exact_mod_cast inv_sqrt_mul_inv_sqrt_mul_eq_sqrt_div hN_pos hM_pos

/-- `⟨U|B⟩ = √((2ⁿ-|M|)/2ⁿ)`. Symmetric to uniform-inner-good. -/
public theorem uniformEdgeState_inner_badState (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (M :
  Finset
  (Fin (2 ^ n)))
    (hM_proper : M ≠ Finset.univ) :
    inner ℂ ((uniformEdgeState P : HilbertVector (Qubits (n + n)))) (badState P M) =
      Real.sqrt ((((2 : ℝ) ^ n - M.card) : ℝ) / ((2 : ℝ) ^ n)) := by
  set S := (Finset.univ : Finset (Fin (2 ^ n))) \ M with hS
  have h_card_S_nat : S.card = 2 ^ n - M.card := by
    simp [hS, Finset.card_sdiff]
  have h_card_S :
      (S.card : ℝ) = ((2 : ℕ) ^ n - M.card : ℝ) := by
    have hM_le : M.card ≤ 2 ^ n := by
      simpa [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_univ M
    rw [h_card_S_nat]
    simpa using (Nat.cast_sub (R := ℝ) hM_le)
  have h_card_S_real :
      (S.card : ℝ) = ((2 : ℝ) ^ n - (M.card : ℝ)) := by
    rw [h_card_S]
    norm_num
  have hN_pos : 0 < ((2 : ℝ) ^ n) := by positivity
  have hS_nonempty : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h_empty
    have h_subset : (Finset.univ : Finset (Fin (2 ^ n))) ⊆ M := by
      intro x _
      by_contra hxM
      have hxS : x ∈ S := by simp [hS, hxM]
      rw [h_empty] at hxS
      simp at hxS
    apply hM_proper
    exact Finset.eq_univ_iff_forall.mpr
      (fun x => h_subset (Finset.mem_univ x))
  have hS_pos : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hS_nonempty
  have hdiff_pos : 0 < ((2 : ℝ) ^ n - (M.card : ℝ)) := by
    rw [← h_card_S_real]
    exact hS_pos
  rw [uniformEdgeState_coe, badState]
  simp only [inner_smul_right, inner_smul_left]
  have h_inner :
      inner ℂ (∑ x : Fin (2 ^ n), (edgeBasis P x : HilbertVector (Qubits (n + n))))
        (∑ y ∈ (Finset.univ : Finset (Fin (2 ^ n))) \ M, (edgeBasis P y : HilbertVector (Qubits (n
          + n)))) =
          ((2 : ℕ) ^ n - M.card : ℂ) := by
    rw [← hS]
    rw [edgeBasis_univ_sum_inner P S]
    norm_num
    exact_mod_cast h_card_S
  rw [h_inner]
  norm_num
  exact_mod_cast inv_sqrt_mul_inv_sqrt_mul_eq_sqrt_div hN_pos hdiff_pos

/-- `markedProjectorOp` is self-adjoint: sum of self-adjoint terms. -/
public theorem markedProjectorOp_conjTranspose (M : Finset (Fin (2 ^ n))) :
    (markedProjectorOp M).conjTranspose = markedProjectorOp M := by
  rw [markedProjectorOp]
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [HilbertOperator.conjTranspose_tensor]
  rw [OrthogonalProjector.basisOp_conjTranspose, Matrix.conjTranspose_one]

private lemma basisOp_mul_basisOp_of_ne
    {x y : Fin (2 ^ n)} (hxy : x ≠ y) :
    OrthogonalProjector.basisOp x * OrthogonalProjector.basisOp y =
      (0 : HilbertOperator (Qubits n)) := by
  ext r c
  rw [Matrix.mul_apply]
  by_cases hr : r = x <;> by_cases hc : c = y <;>
    simp [OrthogonalProjector.basisOp, hr, hc, hxy.symm]

/-- `markedProjectorOp` is idempotent. -/
public theorem markedProjectorOp_idempotent (M : Finset (Fin (2 ^ n))) :
    markedProjectorOp M * markedProjectorOp M = markedProjectorOp M := by
  rw [markedProjectorOp]
  calc
    (∑ x ∈ M, (OrthogonalProjector.basisOp x).tensor 1) *
        (∑ x ∈ M, (OrthogonalProjector.basisOp x).tensor 1)
        = ∑ x ∈ M, ((OrthogonalProjector.basisOp x).tensor 1 *
            (∑ y ∈ M, (OrthogonalProjector.basisOp y).tensor 1)) := by
      rw [Finset.sum_mul]
    _ = ∑ x ∈ M, ∑ y ∈ M,
            ((OrthogonalProjector.basisOp x).tensor 1 * (OrthogonalProjector.basisOp y).tensor 1)
            := by
      refine Finset.sum_congr rfl (fun _ _ => ?_)
      rw [Finset.mul_sum]
    _ = ∑ x ∈ M, (OrthogonalProjector.basisOp x).tensor 1 := by
      refine Finset.sum_congr rfl (fun x hx => ?_)
      rw [Finset.sum_eq_single x]
      · rw [HilbertOperator.tensor_mul_tensor, OrthogonalProjector.basisOp_idempotent,
          Matrix.one_mul]
      · intro y _ hne
        rw [HilbertOperator.tensor_mul_tensor, basisOp_mul_basisOp_of_ne hne.symm,
          HilbertOperator.zero_tensor]
      · intro hx'
        exact False.elim (hx' hx)

/-- The reflection that fixes the unmarked subspace and negates marked states. -/
public def refBglobalOp (M : Finset (Fin (2 ^ n))) :
    UnitaryOperator (Qubits (n + n)) :=
  OrthogonalProjector.reflectionOp {
    op := 1 - markedProjectorOp M
    selfAdjoint := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
        markedProjectorOp_conjTranspose]
    idempotent := by
      rw [sub_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one,
        markedProjectorOp_idempotent M]
      abel }

@[simp]
public theorem refBglobalOp_coe (M : Finset (Fin (2 ^ n))) :
    (refBglobalOp M : HilbertOperator (Qubits (n + n))) =
      1 - (2 : ℂ) • markedProjectorOp M := by
  change (2 : ℂ) • (1 - markedProjectorOp M) - 1 = _
  module

/-- `refBglobalOp` is a reflection, hence preserves inner products. -/
public lemma refBglobalOp_inner_preserving (M : Finset (Fin (2 ^ n))) (x y : HilbertVector (Qubits
  (n + n))) :
    inner ℂ ((refBglobalOp M).applyVec x) ((refBglobalOp M).applyVec y) = inner ℂ x y :=
  (refBglobalOp M).inner_applyVec_applyVec x y

/-- Idempotence for `|ψ⟩⟨ψ|` when `‖ψ‖ = 1`. -/
public lemma outerProductOp_mul_self_of_norm_one (ψ : HilbertVector (Qubits (n + n))) (h : ‖ψ‖ =
  1) :
    outerProductOp ψ * outerProductOp ψ = outerProductOp ψ := by
  have hinner : (∑ k : Fin (2 ^ (n + n)), ψ k * star (ψ k)) = (1 : ℂ) := by
    have hself : inner ℂ ψ ψ = (1 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      rw [h]
      simp
    rw [PiLp.inner_apply] at hself
    have hsum_norm : (∑ k : Fin (2 ^ (n + n)), (‖ψ k‖ : ℂ) ^ 2) = (1 : ℂ) := by
      simpa [RCLike.inner_apply] using hself
    calc
      (∑ k : Fin (2 ^ (n + n)), ψ k * star (ψ k))
          = ∑ k : Fin (2 ^ (n + n)), (‖ψ k‖ : ℂ) ^ 2 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show star (ψ k) = conj (ψ k) from rfl]
        rw [Complex.mul_conj']
      _ = 1 := hsum_norm
  ext i j
  rw [Matrix.mul_apply]
  simp only [outerProductOp, Matrix.of_apply]
  calc
    ∑ k : Fin (2 ^ (n + n)), (ψ i * star (ψ k)) * (ψ k * star (ψ j))
        = ψ i * (∑ k : Fin (2 ^ (n + n)), ψ k * star (ψ k)) * star (ψ j) := by
      simp [Finset.mul_sum, mul_comm, mul_left_comm]
    _ = ψ i * star (ψ j) := by rw [hinner]; ring

/-- `outerProductOp` of a normalized state is self-adjoint. -/
public lemma outerProductOp_conjTranspose (ψ : HilbertVector (Qubits (n + n))) :
    (outerProductOp ψ).conjTranspose = outerProductOp ψ := by
  ext i j
  simp [outerProductOp, Matrix.conjTranspose_apply, mul_comm]

/-- `idealRefUOp` is a reflection `2|U⟩⟨U| - I`, hence preserves inner products. -/
public lemma idealRefUOp_inner_preserving (P : Matrix.SymmetricStochastic (Fin (2 ^ n)))
    (x y : HilbertVector (Qubits (n + n))) :
    inner ℂ ((idealRefUOp P).applyVec x) ((idealRefUOp P).applyVec y) = inner ℂ x y :=
  (idealRefUOp P).inner_applyVec_applyVec x y


end
end QuantumAlg.QuantumWalk

end
