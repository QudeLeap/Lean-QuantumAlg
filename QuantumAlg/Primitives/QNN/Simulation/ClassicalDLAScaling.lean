/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Interface.RagoneInterface
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Weight-state purity and classical-family variance scaling

For a state `ρ` whose dynamical-Lie-algebra projection lies in a Cartan sub-basis, the
`g`-purity is the squared length of the corresponding weight vector. Combining this
with the proved Ragone variance formula gives the weight-state variance
`Var = ‖λ‖² * Tr[O^2] / dim g` for an observable `O` whose projection is itself.

For classical families, the coroot and highest-weight estimate is carried as an
explicit weight-scaling hypothesis. From that estimate and exponential growth of
`dim g`, this module derives a relaxed `base > 1` barren-plateau law.
-/

@[expose] public section

namespace QuantumAlg

open Matrix

variable {N : ℕ}

/-! ### Weight states: `P_g(ρ) = ‖λ‖²` and the weight-state variance -/

/-- Weight-state data for a state `ρ` relative to a `DLAHermBasis b`. The defining datum is
that the `g`-projection of `ρ` is a real coordinate combination of a Hermitian
Hilbert-Schmidt-orthonormal Cartan sub-basis. -/
structure WeightStateData {gens : Set (Matrix (Fin N) (Fin N) ℂ)}
    (b : DLAHermBasis gens) (ρ : Matrix (Fin N) (Fin N) ℂ) where
  /-- The Cartan rank, i.e. the number of weight coordinates. -/
  dimH : ℕ
  /-- The Hermitian Cartan sub-basis. -/
  H : Fin dimH → Matrix (Fin N) (Fin N) ℂ
  /-- Each Cartan basis element is Hermitian. -/
  H_herm : ∀ j, (H j)ᴴ = H j
  /-- The Cartan sub-basis is Hilbert-Schmidt orthonormal. -/
  H_ortho : ∀ i j, hsInner (H i) (H j) = if i = j then 1 else 0
  /-- The real weight coordinates. -/
  lam : Fin dimH → ℝ
  /-- The weight-state projection identity. -/
  proj_eq : b.gProj ρ = ∑ j, (lam j : ℂ) • H j

namespace WeightStateData

variable {gens : Set (Matrix (Fin N) (Fin N) ℂ)} {b : DLAHermBasis gens}
  {ρ O : Matrix (Fin N) (Fin N) ℂ}

/-- For a weight state, `g`-purity is the squared length of the weight vector. -/
theorem gPurity_eq (w : WeightStateData b ρ) (hρ : ρᴴ = ρ) :
    b.gPurity ρ = ((∑ j, (w.lam j) ^ 2 : ℝ) : ℂ) := by
  have htr : ∀ j k, (w.H j * w.H k).trace = if j = k then (1 : ℂ) else 0 := by
    intro j k
    have h := w.H_ortho j k
    rwa [hsInner, w.H_herm j] at h
  rw [b.gPurity_eq_trace hρ, w.proj_eq, Matrix.sum_mul, Matrix.trace_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_sum, Matrix.trace_sum]
  have hk : ∀ k, (((w.lam j : ℂ) • w.H j) * ((w.lam k : ℂ) • w.H k)).trace
      = if j = k then ((w.lam k : ℂ)) ^ 2 else 0 := by
    intro k
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul,
      smul_eq_mul, smul_eq_mul, htr j k]
    rcases eq_or_ne j k with h | h
    · subst h
      rw [if_pos rfl, if_pos rfl]
      ring
    · rw [if_neg h, if_neg h]
      ring
  rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_ite_eq]
  simp

/-- Weight-state variance: with `ρ` a weight state and `O` already in the DLA projection,
the Ragone variance formula becomes `‖λ‖² * Tr[O^2] / dim g`. -/
theorem variance_eq (w : WeightStateData b ρ) (M : RagoneSecondMoment b ρ O)
    (hρ : ρᴴ = ρ) (hO : Oᴴ = O) (hdimpos : 0 < b.dim) (hO_in_g : b.gProj O = O) :
    (M.variance : ℂ)
      = ((∑ j, (w.lam j) ^ 2 : ℝ) : ℂ) * (O * O).trace / (b.dim : ℂ) := by
  rw [M.variance_eq_gPurity hρ hO hdimpos, w.gPurity_eq hρ, b.gPurity_eq_trace hO, hO_in_g]

end WeightStateData

/-! ### The classical-family barren plateau with `base > 1` -/

/-- If the observable has Hilbert-Schmidt bound `2^n`, the weight vector obeys
`‖λ‖² ≤ C * sqrt(dim g) / 2^n`, and `dim g ≥ base^n` with `base > 1`, then the
loss variance is exponentially concentrated with rate `sqrt base`. -/
theorem hasBarrenPlateau_of_weightScale_of_expDim {sz : ℕ → ℕ}
    {gens : (n : ℕ) → Set (Matrix (Fin (sz n)) (Fin (sz n)) ℂ)}
    {ρ O : (n : ℕ) → Matrix (Fin (sz n)) (Fin (sz n)) ℂ}
    {b : (n : ℕ) → DLAHermBasis (gens n)}
    (M : (n : ℕ) → RagoneSecondMoment (b n) (ρ n) (O n))
    (w : (n : ℕ) → WeightStateData (b n) (ρ n))
    (hρ : ∀ n, (ρ n)ᴴ = ρ n) (hO : ∀ n, (O n)ᴴ = O n) (hdimpos : ∀ n, 0 < (b n).dim)
    (hOnorm : ∀ n, (hsInner (O n) (O n)).re ≤ (2 : ℝ) ^ n)
    {C : ℝ} (hC : 0 ≤ C)
    (hweightscale : ∀ n, (∑ j, ((w n).lam j) ^ 2) ≤ C * Real.sqrt ((b n).dim) / 2 ^ n)
    {base : ℝ} (hbase : 1 < base) (hexp : ∀ n, base ^ n ≤ ((b n).dim : ℝ)) :
    HasBarrenPlateau (fun n => (M n).variance) := by
  have hbase0 : (0 : ℝ) < base := lt_trans zero_lt_one hbase
  have hsb1 : 1 < Real.sqrt base := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) hbase
  refine ⟨Real.sqrt base, hsb1, C, hC, fun n => ?_⟩
  have hdimC : (0 : ℝ) < ((b n).dim : ℝ) := by exact_mod_cast hdimpos n
  have hsdpos : 0 < Real.sqrt ((b n).dim) := Real.sqrt_pos.mpr hdimC
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hρeq : ‖(b n).gPurity (ρ n)‖ = ∑ j, ((w n).lam j) ^ 2 := by
    rw [(b n).norm_gPurity_eq_re, (w n).gPurity_eq (hρ n), Complex.ofReal_re]
  have hOle : ‖(b n).gPurity (O n)‖ ≤ (2 : ℝ) ^ n := by
    rw [(b n).norm_gPurity_eq_re]
    exact ((b n).gPurity_le_normSq (O n)).trans (hOnorm n)
  have hscale : (∑ j, ((w n).lam j) ^ 2) ≤ C * Real.sqrt ((b n).dim) / 2 ^ n :=
    hweightscale n
  have hsqrtdim : (Real.sqrt base) ^ n ≤ Real.sqrt ((b n).dim) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    calc ((Real.sqrt base) ^ n) ^ 2 = (Real.sqrt base ^ 2) ^ n := by
          rw [← pow_mul, Nat.mul_comm, pow_mul]
      _ = base ^ n := by rw [Real.sq_sqrt hbase0.le]
      _ ≤ ((b n).dim : ℝ) := hexp n
  have hdivsqrt : Real.sqrt ((b n).dim) / ((b n).dim : ℝ) =
      1 / Real.sqrt ((b n).dim) := by
    rw [div_eq_div_iff hdimC.ne' hsdpos.ne', one_mul]
    exact Real.mul_self_sqrt hdimC.le
  have hv : ((M n).variance : ℂ)
      = (b n).gPurity (ρ n) * (b n).gPurity (O n) / ((b n).dim : ℂ) :=
    (M n).variance_eq_gPurity (hρ n) (hO n) (hdimpos n)
  have hcast : |(M n).variance| = ‖((M n).variance : ℂ)‖ := (RCLike.norm_ofReal (K := ℂ) _).symm
  rw [sub_zero, hcast, hv, norm_div, norm_mul, RCLike.norm_natCast, hρeq]
  calc (∑ j, ((w n).lam j) ^ 2) * ‖(b n).gPurity (O n)‖ / ((b n).dim : ℝ)
      ≤ (C * Real.sqrt ((b n).dim) / 2 ^ n) * (2 : ℝ) ^ n / ((b n).dim : ℝ) := by
        gcongr
    _ = C * (Real.sqrt ((b n).dim) / ((b n).dim : ℝ)) := by
        rw [div_mul_eq_mul_div, mul_div_assoc, div_self h2n.ne', mul_one]
        ring
    _ = C * (1 / Real.sqrt ((b n).dim)) := by rw [hdivsqrt]
    _ ≤ C * (1 / (Real.sqrt base) ^ n) :=
        mul_le_mul_of_nonneg_left
          (one_div_le_one_div_of_le (pow_pos (Real.sqrt_pos.mpr hbase0) n) hsqrtdim) hC
    _ = C / (Real.sqrt base) ^ n := by ring

/-! ### Non-vacuity of the weight-state bundle -/

/-- The weight-state bundle is inhabited nondegenerately by the identity state on the
one-dimensional identity DLA. -/
noncomputable def weightStateDataId :
    WeightStateData trivialDLAHermBasis (1 : Matrix (Fin 1) (Fin 1) ℂ) where
  dimH := 1
  H := fun _ => 1
  H_herm := fun _ => conjTranspose_one
  H_ortho := fun i j => by
    rw [Subsingleton.elim i j, if_pos rfl]
    simp [hsInner, conjTranspose_one, Matrix.trace_one]
  lam := fun _ => 1
  proj_eq := by
    simp [DLAHermBasis.gProj, trivialDLAHermBasis, hsInner, conjTranspose_one, Matrix.trace_one]

end QuantumAlg
