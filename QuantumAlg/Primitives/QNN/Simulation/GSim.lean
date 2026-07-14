/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import QuantumAlg.Primitives.QNN.Interface.CasimirInvariant
public import QuantumAlg.Primitives.QNN.Designs.QubitTwoDesign
public import QuantumAlg.Primitives.QNN.Interface.RagoneInterface
public import QuantumAlg.Primitives.QNN.Algebras.SimpleDLA

/-!
# Lie-algebraic classical simulation (g-sim): correctness

For a circuit whose gate generators lie in the dynamical Lie algebra `g` and an
observable `O ∈ g`, the Heisenberg-evolved observable stays in `g`
(`exp_conj_mem_dla`), its coordinates in a Hermitian orthonormal DLA basis
update by an explicit `dim g × dim g` matrix (`gsimAd` / `gsim_conj_coords`),
and the loss `Tr[U ρ U⁻¹ O]` is exactly reconstructible from the `dim g`
quantum data `Tr[ρ B_j]` (`gsim_loss_reconstruction`). Pairing this with the
variance law `RagoneSecondMoment.variance_eq_gPurity` — whose analytic content
enters through the **named Haar/twirl/Schur hypothesis bundle**
    `RagoneSecondMoment` (`RagoneInterface`), discharged unconditionally for
    `su(2)` by the concrete Clifford doubled-twirl bundle `QubitTwoDesign.main` — yields the
g-sim variance–reconstruction capstone (`gsim_variance_and_reconstruction`):
one hypothesis bundle forces the loss variance to `P_g(ρ)·P_g(O)/dim g` AND
makes the loss classically reconstructible from a `dim g`-sized data vector.
The reconstruction half is proved from algebra alone; the variance half is
conditional on the bundle. `su2_variance_and_reconstruction_unconditional`
instantiates the capstone at `QubitTwoDesign.main`, where nothing is deferred.

The statements are algebraic: gates enter as `NormedSpace.exp A` with `A ∈ g`
(for the physical unitary `U = exp(-iθH)` take `A = (-θ) • (Complex.I • H)`,
which is in `g` since `g` is a complex submodule and `Complex.I • H ∈ g`), and
the inverse side is `NormedSpace.exp (-A)`; no unitarity is needed for the
reconstruction identity.
-/

@[expose] public section

namespace QuantumAlg

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {N : ℕ} {gens : Set (Matrix (Fin N) (Fin N) ℂ)}

section ExpAdConjugation

variable (A : Matrix (Fin N) (Fin N) ℂ)

/-- The left factor of the sandwiched exponential series: `k!⁻¹ • (Aᵏ · X)`. -/
private noncomputable def expTermL (X : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (k.factorial : ℂ)⁻¹ • (A ^ k * X)

/-- The right factor of the sandwiched exponential series: `l!⁻¹ • (-A)ˡ`. -/
private noncomputable def expTermR (l : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  (l.factorial : ℂ)⁻¹ • (-A) ^ l

/-- The Cauchy antidiagonal sums of the sandwiched series; by
`cauchyTerm_eq_hadamardSeq` the `n`-th term is `n!⁻¹ · ad_A^n X`. -/
private noncomputable def cauchyTerm (X : Matrix (Fin N) (Fin N) ℂ) (n : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  ∑ kl ∈ Finset.antidiagonal n, expTermL A X kl.1 * expTermR A kl.2

/-- The normalized Hadamard sequence `H₀ = X`, `H_{n+1} = (n+1)⁻¹ · [A, H_n]`. -/
private noncomputable def hadamardSeq (X : Matrix (Fin N) (Fin N) ℂ) :
    ℕ → Matrix (Fin N) (Fin N) ℂ
  | 0 => X
  | n + 1 =>
      ((n : ℂ) + 1)⁻¹ • (A * hadamardSeq X n - hadamardSeq X n * A)

/-- The total entry mass `Σ_{a,b} ‖A_{ab}‖`, an elementary submultiplicative
bound for entries of powers. -/
private noncomputable def entryBound (A : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ∑ a, ∑ b, ‖A a b‖

private theorem entryBound_nonneg (A : Matrix (Fin N) (Fin N) ℂ) :
    0 ≤ entryBound A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

private theorem norm_entry_le_entryBound (A : Matrix (Fin N) (Fin N) ℂ)
    (i j : Fin N) : ‖A i j‖ ≤ entryBound A := by
  calc ‖A i j‖ ≤ ∑ b, ‖A i b‖ :=
        Finset.single_le_sum (fun b _ => norm_nonneg (A i b)) (Finset.mem_univ j)
    _ ≤ entryBound A :=
        Finset.single_le_sum
          (fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg (A a b))
          (Finset.mem_univ i)

private theorem norm_col_sum_le_entryBound (A : Matrix (Fin N) (Fin N) ℂ)
    (j : Fin N) : ∑ m, ‖A m j‖ ≤ entryBound A := by
  refine Finset.sum_le_sum fun m _ => ?_
  exact Finset.single_le_sum (fun b _ => norm_nonneg (A m b)) (Finset.mem_univ j)

private theorem norm_pow_entry_le (A : Matrix (Fin N) (Fin N) ℂ) (n : ℕ)
    (i j : Fin N) : ‖(A ^ n) i j‖ ≤ entryBound A ^ n := by
  induction n generalizing i j with
  | zero =>
      rw [pow_zero, pow_zero, Matrix.one_apply]
      split <;> simp
  | succ n ih =>
      rw [pow_succ, Matrix.mul_apply]
      calc ‖∑ m, (A ^ n) i m * A m j‖
          ≤ ∑ m, ‖(A ^ n) i m * A m j‖ := norm_sum_le _ _
        _ ≤ ∑ m, entryBound A ^ n * ‖A m j‖ := by
            refine Finset.sum_le_sum fun m _ => ?_
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (ih i m) (norm_nonneg _)
        _ = entryBound A ^ n * ∑ m, ‖A m j‖ := by rw [Finset.mul_sum]
        _ ≤ entryBound A ^ n * entryBound A :=
            mul_le_mul_of_nonneg_left (norm_col_sum_le_entryBound A j)
              (pow_nonneg (entryBound_nonneg A) n)
        _ = entryBound A ^ (n + 1) := (pow_succ _ _).symm

/-- The matrix exponential series has its sum at `NormedSpace.exp`, in the
ambient (entrywise/pi) topology: entrywise the series is dominated by
`entryBound^n / n!`, and the topological `exp_eq_tsum` identifies the limit. -/
private theorem hasSum_expSeries (A : Matrix (Fin N) (Fin N) ℂ) :
    HasSum (fun n => (n.factorial : ℂ)⁻¹ • A ^ n) (NormedSpace.exp A) := by
  have hsummable : Summable fun n => (n.factorial : ℂ)⁻¹ • A ^ n := by
    refine Pi.summable.mpr fun i => Pi.summable.mpr fun j => ?_
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      (Real.summable_pow_div_factorial (entryBound A))
    rw [Matrix.smul_apply, norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (norm_pow_entry_le A n i j)
      (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hexp : NormedSpace.exp A = ∑' n, (n.factorial : ℂ)⁻¹ • A ^ n := by
    simpa using congrFun (NormedSpace.exp_eq_tsum (𝔸 := Matrix (Fin N) (Fin N) ℂ) ℂ) A
  rw [hexp]
  exact hsummable.hasSum

private theorem hasSum_expTermL (X : Matrix (Fin N) (Fin N) ℂ) :
    HasSum (expTermL A X) (NormedSpace.exp A * X) := by
  have h2 := (hasSum_expSeries A).map (AddMonoidHom.mulRight X)
    (continuous_mul_const X)
  simp only [Function.comp_def, AddMonoidHom.coe_mulRight, AddMonoidHom.mulRight_apply,
    smul_mul_assoc] at h2
  exact h2

private theorem hasSum_expTermR :
    HasSum (expTermR A) (NormedSpace.exp (-A)) :=
  hasSum_expSeries (-A)

private theorem summable_norm_expTermL_entry (X : Matrix (Fin N) (Fin N) ℂ)
    (i m : Fin N) : Summable fun k => ‖expTermL A X k i m‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    ((Real.summable_pow_div_factorial (entryBound A)).mul_right (entryBound X))
  rw [expTermL, Matrix.smul_apply, norm_smul, norm_inv, Complex.norm_natCast,
    Matrix.mul_apply]
  rw [div_eq_inv_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Nat.cast_nonneg _))
  calc ‖∑ p, (A ^ k) i p * X p m‖
      ≤ ∑ p, ‖(A ^ k) i p * X p m‖ := norm_sum_le _ _
    _ ≤ ∑ p, entryBound A ^ k * ‖X p m‖ := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (norm_pow_entry_le A k i p) (norm_nonneg _)
    _ = entryBound A ^ k * ∑ p, ‖X p m‖ := by rw [Finset.mul_sum]
    _ ≤ entryBound A ^ k * entryBound X :=
        mul_le_mul_of_nonneg_left (norm_col_sum_le_entryBound X m)
          (pow_nonneg (entryBound_nonneg A) k)

private theorem summable_norm_expTermR_entry (m j : Fin N) :
    Summable fun l => ‖expTermR A l m j‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_)
    (Real.summable_pow_div_factorial (entryBound (-A)))
  rw [expTermR, Matrix.smul_apply, norm_smul, norm_inv, Complex.norm_natCast,
    div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (norm_pow_entry_le (-A) l m j)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- Weighted step for the left factor: `(k+1) · L_{k+1} = A · L_k`. -/
private theorem expTermL_succ_smul (X : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) :
    ((k : ℂ) + 1) • expTermL A X (k + 1) = A * expTermL A X k := by
  rw [expTermL, expTermL, mul_smul_comm, smul_smul, pow_succ', Matrix.mul_assoc]
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv, ← mul_assoc,
    show ((k + 1 : ℕ) : ℂ) = (k : ℂ) + 1 by push_cast; ring,
    mul_inv_cancel₀ (Nat.cast_add_one_ne_zero k), one_mul]

/-- Weighted step for the right factor: `(l+1) · R_{l+1} = R_l · (-A)`. -/
private theorem expTermR_succ_smul (l : ℕ) :
    ((l : ℂ) + 1) • expTermR A (l + 1) = expTermR A l * -A := by
  rw [expTermR, expTermR, smul_mul_assoc, smul_smul, pow_succ]
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv, ← mul_assoc,
    show ((l + 1 : ℕ) : ℂ) = (l : ℂ) + 1 by push_cast; ring,
    mul_inv_cancel₀ (Nat.cast_add_one_ne_zero l), one_mul]

/-- The Cauchy sums satisfy the normalized Hadamard recursion
`(n+1) · C_{n+1} = [A, C_n]`, by the reciprocal-factorial Pascal identity. -/
private theorem cauchyTerm_succ_smul (X : Matrix (Fin N) (Fin N) ℂ) (n : ℕ) :
    ((n : ℂ) + 1) • cauchyTerm A X (n + 1)
      = A * cauchyTerm A X n - cauchyTerm A X n * A := by
  have hsplit : ((n : ℂ) + 1) • cauchyTerm A X (n + 1)
      = (∑ kl ∈ Finset.antidiagonal (n + 1),
          (kl.1 : ℂ) • (expTermL A X kl.1 * expTermR A kl.2))
        + ∑ kl ∈ Finset.antidiagonal (n + 1),
            (kl.2 : ℂ) • (expTermL A X kl.1 * expTermR A kl.2) := by
    rw [cauchyTerm, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    have hmem := Finset.mem_antidiagonal.mp hkl
    have hcast : (kl.1 : ℂ) + (kl.2 : ℂ) = (n : ℂ) + 1 := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℂ)) hmem
    rw [← add_smul, hcast]
  have h1 : (∑ kl ∈ Finset.antidiagonal (n + 1),
      (kl.1 : ℂ) • (expTermL A X kl.1 * expTermR A kl.2))
      = A * cauchyTerm A X n := by
    rw [Finset.Nat.sum_antidiagonal_succ]
    simp only [Nat.cast_zero, zero_smul, zero_add]
    rw [cauchyTerm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun kl _ => ?_
    rw [show ((kl.1 + 1 : ℕ) : ℂ) = (kl.1 : ℂ) + 1 by push_cast; ring,
      ← smul_mul_assoc, expTermL_succ_smul, Matrix.mul_assoc]
  have h2 : (∑ kl ∈ Finset.antidiagonal (n + 1),
      (kl.2 : ℂ) • (expTermL A X kl.1 * expTermR A kl.2))
      = -(cauchyTerm A X n * A) := by
    rw [Finset.Nat.sum_antidiagonal_succ']
    simp only [Nat.cast_zero, zero_smul, zero_add]
    rw [cauchyTerm, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun kl _ => ?_
    rw [show ((kl.2 + 1 : ℕ) : ℂ) = (kl.2 : ℂ) + 1 by push_cast; ring,
      ← mul_smul_comm, expTermR_succ_smul, ← Matrix.mul_assoc, mul_neg]
  rw [hsplit, h1, h2, sub_eq_add_neg]

/-- The Cauchy antidiagonal sums are exactly the normalized Hadamard terms. -/
private theorem cauchyTerm_eq_hadamardSeq (X : Matrix (Fin N) (Fin N) ℂ) (n : ℕ) :
    cauchyTerm A X n = hadamardSeq A X n := by
  induction n with
  | zero =>
      simp [cauchyTerm, hadamardSeq, expTermL, expTermR]
  | succ n ih =>
      have h := cauchyTerm_succ_smul A X n
      rw [ih] at h
      calc cauchyTerm A X (n + 1)
          = ((n : ℂ) + 1)⁻¹ • (((n : ℂ) + 1) • cauchyTerm A X (n + 1)) := by
            rw [smul_smul, inv_mul_cancel₀ (Nat.cast_add_one_ne_zero n), one_smul]
        _ = ((n : ℂ) + 1)⁻¹
              • (A * hadamardSeq A X n - hadamardSeq A X n * A) := by rw [h]
        _ = hadamardSeq A X (n + 1) := rfl

/-- The sandwiched exponential is the sum of the Cauchy antidiagonal series:
entrywise, each `(i,j)` entry is a finite sum over the middle index of scalar
Cauchy products of absolutely convergent complex series. -/
private theorem hasSum_cauchyTerm (X : Matrix (Fin N) (Fin N) ℂ) :
    HasSum (cauchyTerm A X) (NormedSpace.exp A * X * NormedSpace.exp (-A)) := by
  refine Pi.hasSum.mpr fun i => Pi.hasSum.mpr fun j => ?_
  have hm : ∀ m : Fin N,
      HasSum (fun n => ∑ kl ∈ Finset.antidiagonal n,
          expTermL A X kl.1 i m * expTermR A kl.2 m j)
        ((NormedSpace.exp A * X) i m * NormedSpace.exp (-A) m j) := by
    intro m
    have hFn := summable_norm_expTermL_entry A X i m
    have hGn := summable_norm_expTermR_entry A m j
    have hsum : Summable fun n => ∑ kl ∈ Finset.antidiagonal n,
        expTermL A X kl.1 i m * expTermR A kl.2 m j :=
      (summable_norm_sum_mul_antidiagonal_of_summable_norm hFn hGn).of_norm
    have hL : HasSum (fun k => expTermL A X k i m)
        ((NormedSpace.exp A * X) i m) :=
      Pi.hasSum.mp (Pi.hasSum.mp (hasSum_expTermL A X) i) m
    have hR : HasSum (fun l => expTermR A l m j)
        (NormedSpace.exp (-A) m j) :=
      Pi.hasSum.mp (Pi.hasSum.mp (hasSum_expTermR A) m) j
    have hts := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hFn hGn
    rw [hL.tsum_eq, hR.tsum_eq] at hts
    rw [hts]
    exact hsum.hasSum
  have h := hasSum_sum fun m (_ : m ∈ Finset.univ) => hm m
  have hfun : (fun n => cauchyTerm A X n i j)
      = fun n => ∑ m, ∑ kl ∈ Finset.antidiagonal n,
          expTermL A X kl.1 i m * expTermR A kl.2 m j := by
    funext n
    rw [cauchyTerm, Matrix.sum_apply]
    simp only [Matrix.mul_apply]
    exact Finset.sum_comm
  have hval : (NormedSpace.exp A * X * NormedSpace.exp (-A)) i j
      = ∑ m, (NormedSpace.exp A * X) i m * NormedSpace.exp (-A) m j :=
    Matrix.mul_apply
  rw [hfun, hval]
  exact h

/-- Each normalized Hadamard term stays in the dynamical Lie algebra. -/
private theorem hadamardSeq_mem {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A ∈ (dynamicalLieAlgebra gens).toSubmodule)
    {X : Matrix (Fin N) (Fin N) ℂ}
    (hX : X ∈ (dynamicalLieAlgebra gens).toSubmodule) :
    ∀ n, hadamardSeq A X n ∈ (dynamicalLieAlgebra gens).toSubmodule
  | 0 => hX
  | n + 1 => by
      refine Submodule.smul_mem _ _ ?_
      have h : ⁅A, hadamardSeq A X n⁆ ∈ dynamicalLieAlgebra gens :=
        (dynamicalLieAlgebra gens).lie_mem hA (hadamardSeq_mem hA hX n)
      rw [Ring.lie_def] at h
      exact h

end ExpAdConjugation

/-- **The DLA is invariant under conjugation by exponentials of its own
elements.** For `A, O ∈ g`, `e^A · O · e^{-A} ∈ g` — the adjoint (Heisenberg)
action of a Lie-algebraic gate keeps the observable inside the dynamical Lie
algebra. This is the crux lemma of the g-sim correctness chain: the sandwiched
exponential is the sum of the Hadamard series `Σ n!⁻¹ ad_A^n O` (Cauchy product
of the two exponential series, regrouped by the reciprocal-factorial Pascal
identity), each series term stays in `g` by bracket closure, and the
finite-dimensional submodule is closed, so the limit stays as well. -/
theorem exp_conj_mem_dla {A O : Matrix (Fin N) (Fin N) ℂ}
    (hA : A ∈ (dynamicalLieAlgebra gens).toSubmodule)
    (hO : O ∈ (dynamicalLieAlgebra gens).toSubmodule) :
    NormedSpace.exp A * O * NormedSpace.exp (-A)
      ∈ (dynamicalLieAlgebra gens).toSubmodule := by
  have hsum := hasSum_cauchyTerm A O
  refine (Submodule.closed_of_finiteDimensional _).mem_of_tendsto
    hsum.tendsto_sum_nat (Filter.Eventually.of_forall fun k => ?_)
  refine Submodule.sum_mem _ fun n _ => ?_
  rw [cauchyTerm_eq_hadamardSeq]
  exact hadamardSeq_mem hA hO n

/-! ## The g-sim transfer matrix and coordinate update -/

/-- Every Hermitian basis element lies in the dynamical Lie algebra. -/
theorem DLAHermBasis.basis_mem_dla (b : DLAHermBasis gens) (j : Fin b.dim) :
    b.B j ∈ (dynamicalLieAlgebra gens).toSubmodule :=
  b.span_eq ▸ Submodule.subset_span (Set.mem_range_self j)

/-- The g-sim transfer matrix: the matrix of the conjugation
`X ↦ e^A · X · e^{-A}` restricted to `g`, in the Hermitian orthonormal basis
`b`. Its entries `⟪Bᵢ, e^A Bⱼ e^{-A}⟫` are the classical data a Lie-algebraic
simulator multiplies by. -/
noncomputable def gsimAd (b : DLAHermBasis gens)
    (A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin b.dim) (Fin b.dim) ℂ :=
  fun i j => hsInner (b.B i) (NormedSpace.exp A * b.B j * NormedSpace.exp (-A))

/-- Coordinates of a matrix in the Hermitian DLA basis, measured by the
Hilbert-Schmidt pairing against each basis element. -/
noncomputable def gsimCoords (b : DLAHermBasis gens)
    (X : Matrix (Fin N) (Fin N) ℂ) : Fin b.dim → ℂ :=
  fun j => hsInner (b.B j) X

/-- **Coordinate update law.** For `A, O ∈ g` the conjugated observable is the
basis expansion whose coefficient vector is `gsimAd b A` applied to the
coefficient vector of `O`. -/
theorem gsim_conj_coords (b : DLAHermBasis gens)
    {A O : Matrix (Fin N) (Fin N) ℂ}
    (hA : A ∈ (dynamicalLieAlgebra gens).toSubmodule)
    (hO : O ∈ (dynamicalLieAlgebra gens).toSubmodule) :
    NormedSpace.exp A * O * NormedSpace.exp (-A)
      = ∑ i, (∑ j, gsimAd b A i j * hsInner (b.B j) O) • b.B i := by
  -- Expand `O` in the basis and push the conjugation through the finite sum.
  conv_lhs => rw [← gProj_eq_self_of_mem b hO, DLAHermBasis.gProj]
  rw [Finset.mul_sum, Finset.sum_mul]
  -- Each conjugated basis element expands in the basis with `gsimAd` entries.
  have hBconj : ∀ j : Fin b.dim,
      NormedSpace.exp A * b.B j * NormedSpace.exp (-A)
        = ∑ i, gsimAd b A i j • b.B i := by
    intro j
    conv_lhs => rw [← gProj_eq_self_of_mem b
      (exp_conj_mem_dla hA (b.basis_mem_dla j)), DLAHermBasis.gProj]
    rfl
  calc ∑ j, NormedSpace.exp A * (hsInner (b.B j) O • b.B j) * NormedSpace.exp (-A)
      = ∑ j, hsInner (b.B j) O • ∑ i, gsimAd b A i j • b.B i := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.mul_smul, Matrix.smul_mul, hBconj j]
    _ = ∑ j, ∑ i, (gsimAd b A i j * hsInner (b.B j) O) • b.B i := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, mul_comm]
    _ = ∑ i, (∑ j, gsimAd b A i j * hsInner (b.B j) O) • b.B i := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => (Finset.sum_smul).symm

/-! ### The transfer matrix is the exponential of the ad-matrix

`gsimAd b A` is defined through the ambient `2ⁿ`-dimensional exponential
`e^A · Bⱼ · e^{-A}`. The identity that gives g-sim its `poly(dim g)` meaning is
that this `dim g × dim g` matrix is the exponential of the (also `dim g × dim g`)
matrix of `ad A = ⁅A, ·⁆` in the basis `b`. The `g`-invariance of the adjoint
action does the work: `ad A` restricts to an endomorphism of `g`, represented in
the orthonormal basis `b` by `adMatrix b A`, and matrix powers track operator
powers of `ad A`. -/

/-- The matrix of the restricted adjoint action `ad A = ⁅A, ·⁆` on `g`, in the
Hermitian orthonormal basis `b`: entry `(i,j)` is `⟪Bᵢ, ⁅A, Bⱼ⁆⟫`. A
`dim g × dim g` object, in contrast to the ambient `2ⁿ`-dimensional exponential
through which `gsimAd` is defined; `gsimAd_eq_exp_adMatrix` is the identity that
links them. -/
noncomputable def DLAHermBasis.adMatrix (b : DLAHermBasis gens)
    (A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin b.dim) (Fin b.dim) ℂ :=
  fun i j => hsInner (b.B i) ⁅A, b.B j⁆

/-- The `n`-fold nested adjoint action `ad_A^n X = ⁅A, ⁅A, … ⁅A, X⁆…⁆⁆`. -/
private noncomputable def adIterate (A : Matrix (Fin N) (Fin N) ℂ) :
    ℕ → Matrix (Fin N) (Fin N) ℂ → Matrix (Fin N) (Fin N) ℂ
  | 0, X => X
  | n + 1, X => ⁅A, adIterate A n X⁆

/-- `ad A = ⁅A, ·⁆` distributes over a finite `ℂ`-linear combination. -/
private theorem lie_sum_smul (A : Matrix (Fin N) (Fin N) ℂ) {m : ℕ}
    (c : Fin m → ℂ) (v : Fin m → Matrix (Fin N) (Fin N) ℂ) :
    ⁅A, ∑ k, c k • v k⁆ = ∑ k, c k • ⁅A, v k⁆ := by
  simp only [Ring.lie_def, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
    mul_smul_comm, smul_mul_assoc, smul_sub]

/-- The nested adjoint action keeps `X ∈ g` inside `g` (bracket closure). -/
private theorem adIterate_mem {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A ∈ (dynamicalLieAlgebra gens).toSubmodule)
    {X : Matrix (Fin N) (Fin N) ℂ}
    (hX : X ∈ (dynamicalLieAlgebra gens).toSubmodule) :
    ∀ n, adIterate A n X ∈ (dynamicalLieAlgebra gens).toSubmodule
  | 0 => hX
  | n + 1 => (dynamicalLieAlgebra gens).lie_mem hA (adIterate_mem hA hX n)

/-- The normalized Hadamard term is the nested adjoint action scaled by `1/n!`. -/
private theorem hadamardSeq_eq_adIterate (A X : Matrix (Fin N) (Fin N) ℂ) :
    ∀ n, hadamardSeq A X n = (n.factorial : ℂ)⁻¹ • adIterate A n X
  | 0 => by simp [hadamardSeq, adIterate]
  | n + 1 => by
      rw [hadamardSeq, hadamardSeq_eq_adIterate A X n, adIterate, Ring.lie_def,
        mul_smul_comm, smul_mul_assoc, ← smul_sub, smul_smul]
      congr 1
      rw [Nat.factorial_succ, Nat.cast_mul, mul_inv,
        show ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 by push_cast; ring]

/-- Matrix powers of `adMatrix` track the nested adjoint action: the `(i,j)` entry
of `(adMatrix b A)ⁿ` is `⟪Bᵢ, ad_A^n Bⱼ⟫`. The `g`-invariance of `ad A` (bracket
closure) lets each power act inside the orthonormal basis. -/
private theorem adMatrix_pow_apply (b : DLAHermBasis gens)
    {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A ∈ (dynamicalLieAlgebra gens).toSubmodule) (j : Fin b.dim) :
    ∀ (n : ℕ) (i : Fin b.dim),
      ((b.adMatrix A) ^ n) i j = hsInner (b.B i) (adIterate A n (b.B j)) := by
  intro n
  induction n with
  | zero =>
      intro i
      rw [pow_zero, Matrix.one_apply]
      simp only [adIterate]
      rw [b.ortho i j]
  | succ n ih =>
      intro i
      rw [pow_succ', Matrix.mul_apply]
      simp only [adIterate]
      have hY : adIterate A n (b.B j) ∈ (dynamicalLieAlgebra gens).toSubmodule :=
        adIterate_mem hA (b.basis_mem_dla j) n
      have hexp : ⁅A, adIterate A n (b.B j)⁆
          = ∑ k, hsInner (b.B k) (adIterate A n (b.B j)) • ⁅A, b.B k⁆ := by
        conv_lhs => rw [← gProj_eq_self_of_mem b hY, DLAHermBasis.gProj]
        exact lie_sum_smul A _ _
      rw [hexp, hsInner_sum_right]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hsInner_smul_right, ih k]
      simp only [DLAHermBasis.adMatrix]
      ring

/-- **The g-sim transfer matrix is the exponential of the ad-matrix.** For a gate
generator `A ∈ g`, the ambient conjugation matrix `gsimAd b A` (defined through the
full `2ⁿ`-dimensional `e^A · · · e^{-A}`) equals `exp (adMatrix b A)`, an
exponential of the `dim g × dim g` matrix of `ad A = ⁅A, ·⁆`. This is the missing
identity that makes the g-sim data classical and `poly(dim g)`-sized: it is the
finite-dimensional `Ad(e^A) = e^{ad A}` restricted to `g`. The `g`-invariance of
the adjoint action carries the whole proof — `e^A Bⱼ e^{-A}` is the sum of the
Hadamard series `Σ n!⁻¹ ad_A^n Bⱼ`, each term stays in `g`, and its `Bᵢ`-coordinate
is exactly the `(i,j)` entry of `(adMatrix b A)ⁿ`. -/
theorem gsimAd_eq_exp_adMatrix (b : DLAHermBasis gens)
    {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A ∈ (dynamicalLieAlgebra gens).toSubmodule) :
    gsimAd b A = NormedSpace.exp (b.adMatrix A) := by
  ext i j
  -- The Hilbert–Schmidt functional `⟪Bᵢ, ·⟫` as a continuous `ℂ`-linear map.
  let ψ : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] ℂ :=
    (Matrix.traceLinearMap (Fin N) ℂ ℂ).comp (LinearMap.mulLeft ℂ (b.B i)ᴴ)
  have hψ : ∀ X, ψ X = hsInner (b.B i) X := fun X => by
    simp only [ψ, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      Matrix.traceLinearMap_apply, hsInner]
  have hψc : Continuous ψ := ψ.continuous_of_finiteDimensional
  -- LHS: apply `⟪Bᵢ, ·⟫` to the Hadamard/Cauchy series of `e^A Bⱼ e^{-A}`.
  have hLHS : HasSum (fun n => (n.factorial : ℂ)⁻¹ * ((b.adMatrix A) ^ n) i j)
      (gsimAd b A i j) := by
    have h := (hasSum_cauchyTerm A (b.B j)).map ψ.toAddMonoidHom hψc
    have hterm : ∀ n, ψ.toAddMonoidHom (cauchyTerm A (b.B j) n)
        = (n.factorial : ℂ)⁻¹ * ((b.adMatrix A) ^ n) i j := by
      intro n
      rw [LinearMap.toAddMonoidHom_coe, hψ, cauchyTerm_eq_hadamardSeq,
        hadamardSeq_eq_adIterate, hsInner_smul_right, ← adMatrix_pow_apply b hA j n i]
    have hval : ψ.toAddMonoidHom (NormedSpace.exp A * b.B j * NormedSpace.exp (-A))
        = gsimAd b A i j := by
      rw [LinearMap.toAddMonoidHom_coe, hψ]; rfl
    simpa only [Function.comp_def, hterm, hval] using h
  -- RHS: extract the `(i,j)` entry of the matrix exponential series.
  have hRHS : HasSum (fun n => (n.factorial : ℂ)⁻¹ * ((b.adMatrix A) ^ n) i j)
      (NormedSpace.exp (b.adMatrix A) i j) := by
    have h := Pi.hasSum.mp (Pi.hasSum.mp (hasSum_expSeries (b.adMatrix A)) i) j
    simpa only [Matrix.smul_apply, smul_eq_mul] using h
  exact hLHS.unique hRHS

/-! ## Loss reconstruction from `dim g` quantum data -/

/-- **g-sim correctness (single gate).** The loss `Tr[e^A ρ e^{-A} · O]` is the
finite classical contraction of the transfer data `gsimAd b (-A)` and the
observable coordinates — classical, `dim g`-sized — with the quantum data
vector `Tr[ρ Bⱼ]`, `j = 1..dim g`. Nothing about `ρ` beyond those `dim g`
traces enters the loss. -/
theorem gsim_loss_reconstruction (b : DLAHermBasis gens)
    {A O : Matrix (Fin N) (Fin N) ℂ} (ρ : Matrix (Fin N) (Fin N) ℂ)
    (hA : A ∈ (dynamicalLieAlgebra gens).toSubmodule)
    (hO : O ∈ (dynamicalLieAlgebra gens).toSubmodule) :
    (NormedSpace.exp A * ρ * NormedSpace.exp (-A) * O).trace
      = ∑ j, (∑ i, gsimAd b (-A) j i * hsInner (b.B i) O)
          * (ρ * b.B j).trace := by
  have hOconj := gsim_conj_coords b (Submodule.neg_mem _ hA) hO
  rw [neg_neg] at hOconj
  have hcyc : (NormedSpace.exp A * ρ * NormedSpace.exp (-A) * O).trace
      = (ρ * (NormedSpace.exp (-A) * O * NormedSpace.exp A)).trace := by
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle, ← Matrix.mul_assoc,
      Matrix.trace_mul_comm]
  rw [hcyc, hOconj, Finset.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- Conjugation by one gate in the Heisenberg direction: `X ↦ e^{-A} X e^A`. -/
noncomputable def gsimHeisenbergStep (A X : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  NormedSpace.exp (-A) * X * NormedSpace.exp A

/-- One Heisenberg step keeps the observable in `g`. -/
theorem gsimHeisenbergStep_mem {A O : Matrix (Fin N) (Fin N) ℂ}
    (hA : A ∈ (dynamicalLieAlgebra gens).toSubmodule)
    (hO : O ∈ (dynamicalLieAlgebra gens).toSubmodule) :
    gsimHeisenbergStep A O ∈ (dynamicalLieAlgebra gens).toSubmodule := by
  have h := exp_conj_mem_dla (Submodule.neg_mem _ hA) hO
  rw [neg_neg] at h
  exact h

/-- One Heisenberg step updates DLA coordinates by the transfer matrix
`gsimAd b (-A)`. -/
theorem gsimHeisenbergStep_coords (b : DLAHermBasis gens)
    {A O : Matrix (Fin N) (Fin N) ℂ}
    (hA : A ∈ (dynamicalLieAlgebra gens).toSubmodule)
    (hO : O ∈ (dynamicalLieAlgebra gens).toSubmodule) :
    gsimCoords b (gsimHeisenbergStep A O)
      = (gsimAd b (-A)).mulVec (gsimCoords b O) := by
  funext i
  have h := congrArg (fun X => hsInner (b.B i) X)
    (gsim_conj_coords b (Submodule.neg_mem _ hA) hO)
  simp only [neg_neg] at h
  rw [gsimCoords, gsimHeisenbergStep, h]
  rw [hsInner_sum_right]
  simp only [hsInner_smul_right]
  rw [Finset.sum_eq_single i]
  · have horth : hsInner (b.B i) (b.B i) = 1 := by
      simpa using b.ortho i i
    rw [horth, mul_one]
    simp [Matrix.mulVec, dotProduct, gsimCoords, hsInner]
  · intro x _ hx
    have horth : hsInner (b.B i) (b.B x) = 0 := by
      simpa [if_neg (Ne.symm hx)] using b.ortho i x
    rw [horth, mul_zero]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- The Heisenberg-evolved observable of a gate list: the head of the list is
the leftmost factor of `U` — the last gate applied to the state — hence the
innermost conjugation on the Heisenberg observable. -/
noncomputable def gsimEvolved (Gs : List (Matrix (Fin N) (Fin N) ℂ))
    (O : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Gs.foldl (fun X A => gsimHeisenbergStep A X) O

@[simp] theorem gsimEvolved_nil (O : Matrix (Fin N) (Fin N) ℂ) :
    gsimEvolved ([] : List (Matrix (Fin N) (Fin N) ℂ)) O = O := rfl

@[simp] theorem gsimEvolved_cons (A : Matrix (Fin N) (Fin N) ℂ)
    (Gs : List (Matrix (Fin N) (Fin N) ℂ)) (O : Matrix (Fin N) (Fin N) ℂ) :
    gsimEvolved (A :: Gs) O = gsimEvolved Gs (gsimHeisenbergStep A O) := rfl

/-- The Heisenberg-evolved observable of a gate list stays in `g`. -/
theorem gsimEvolved_mem {Gs : List (Matrix (Fin N) (Fin N) ℂ)}
    (hGs : ∀ A ∈ Gs, A ∈ (dynamicalLieAlgebra gens).toSubmodule)
    {O : Matrix (Fin N) (Fin N) ℂ}
    (hO : O ∈ (dynamicalLieAlgebra gens).toSubmodule) :
    gsimEvolved Gs O ∈ (dynamicalLieAlgebra gens).toSubmodule := by
  induction Gs generalizing O with
  | nil => simpa using hO
  | cons A Gs ih =>
      rw [gsimEvolved_cons]
      exact ih (fun B hB => hGs B (List.mem_cons_of_mem A hB))
        (gsimHeisenbergStep_mem (hGs A (by simp)) hO)

/-- Folding transfer matrices over a gate list composes an existing transfer
matrix on the right. -/
private theorem gsimTransfer_foldl_mul (b : DLAHermBasis gens)
    (Gs : List (Matrix (Fin N) (Fin N) ℂ))
    (P : Matrix (Fin b.dim) (Fin b.dim) ℂ) :
    Gs.foldl (fun Q A => gsimAd b (-A) * Q) P =
      Gs.foldl (fun Q A => gsimAd b (-A) * Q) 1 * P := by
  induction Gs generalizing P with
  | nil => simp
  | cons A Gs ih =>
      simp only [List.foldl_cons]
      rw [ih (gsimAd b (-A) * P), ih (gsimAd b (-A) * 1)]
      simp [Matrix.mul_assoc]

/-- The transfer product for `A :: Gs` first applies the head gate's transfer
matrix, then the tail product. -/
private theorem gsimTransfer_cons (b : DLAHermBasis gens)
    (A : Matrix (Fin N) (Fin N) ℂ) (Gs : List (Matrix (Fin N) (Fin N) ℂ)) :
    (A :: Gs).foldl (fun P B => gsimAd b (-B) * P) 1 =
      Gs.foldl (fun P B => gsimAd b (-B) * P) 1 * gsimAd b (-A) := by
  simp only [List.foldl_cons, mul_one]
  exact gsimTransfer_foldl_mul b Gs (gsimAd b (-A))

/-- Coordinates of the Heisenberg-evolved observable are obtained by applying
the folded per-gate transfer matrices to the initial coordinate vector. Since
`gsimEvolved` is a `List.foldl`, the head of `Gs` is the leftmost factor of
`U`, the last gate applied to the state, and therefore the innermost
Heisenberg conjugation. Accordingly the transfer product folds with each new
matrix on the left; for `[A, B]` it is `gsimAd b (-B) * gsimAd b (-A)`. -/
theorem gsimEvolved_coords (b : DLAHermBasis gens)
    {Gs : List (Matrix (Fin N) (Fin N) ℂ)}
    (hGs : ∀ A ∈ Gs, A ∈ (dynamicalLieAlgebra gens).toSubmodule)
    {O : Matrix (Fin N) (Fin N) ℂ}
    (hO : O ∈ (dynamicalLieAlgebra gens).toSubmodule) :
    gsimCoords b (gsimEvolved Gs O) =
      (Gs.foldl (fun P A => gsimAd b (-A) * P) 1).mulVec (gsimCoords b O) := by
  induction Gs generalizing O with
  | nil =>
      simp
  | cons A Gs ih =>
      have hAmem : A ∈ (dynamicalLieAlgebra gens).toSubmodule := hGs A (by simp)
      have htail : ∀ B ∈ Gs, B ∈ (dynamicalLieAlgebra gens).toSubmodule :=
        fun B hB => hGs B (List.mem_cons_of_mem A hB)
      have hstep : gsimHeisenbergStep A O ∈ (dynamicalLieAlgebra gens).toSubmodule :=
        gsimHeisenbergStep_mem hAmem hO
      rw [gsimEvolved_cons]
      rw [ih htail hstep]
      rw [gsimHeisenbergStep_coords b hAmem hO]
      rw [Matrix.mulVec_mulVec]
      rw [← gsimTransfer_cons b A Gs]

/-- Cycling the head gate of the circuit onto the observable under the trace. -/
private theorem trace_conj_step (P Q ρ O A : Matrix (Fin N) (Fin N) ℂ) :
    (NormedSpace.exp A * P * ρ * (Q * NormedSpace.exp (-A)) * O).trace
      = (P * ρ * Q * gsimHeisenbergStep A O).trace := by
  simp only [gsimHeisenbergStep, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- **g-sim correctness (multi-gate ansatz).** For `U = ∏ₖ e^{Aₖ}` (List
product) the loss `Tr[U ρ U⁻¹ O]` equals the contraction of the Heisenberg
observable's coordinates — computable from the per-gate transfer matrices
(`gsim_conj_coords`) — with the `dim g` quantum data `Tr[ρ Bⱼ]`. -/
theorem gsim_loss_reconstruction_ansatz (b : DLAHermBasis gens)
    {Gs : List (Matrix (Fin N) (Fin N) ℂ)}
    (hGs : ∀ A ∈ Gs, A ∈ (dynamicalLieAlgebra gens).toSubmodule)
    {O : Matrix (Fin N) (Fin N) ℂ} (ρ : Matrix (Fin N) (Fin N) ℂ)
    (hO : O ∈ (dynamicalLieAlgebra gens).toSubmodule) :
    ((Gs.map NormedSpace.exp).prod * ρ
        * ((Gs.reverse).map (fun A => NormedSpace.exp (-A))).prod * O).trace
      = ∑ j, hsInner (b.B j) (gsimEvolved Gs O) * (ρ * b.B j).trace := by
  induction Gs generalizing O with
  | nil =>
      simp only [List.map_nil, List.prod_nil, List.reverse_nil, one_mul, mul_one,
        gsimEvolved_nil]
      conv_lhs => rw [← gProj_eq_self_of_mem b hO, DLAHermBasis.gProj]
      rw [Finset.mul_sum, Matrix.trace_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  | cons A Gs ih =>
      have hAmem : A ∈ (dynamicalLieAlgebra gens).toSubmodule := hGs A (by simp)
      have htail : ∀ B ∈ Gs, B ∈ (dynamicalLieAlgebra gens).toSubmodule :=
        fun B hB => hGs B (List.mem_cons_of_mem A hB)
      have ih' := ih htail (gsimHeisenbergStep_mem hAmem hO)
      simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
        List.map_nil, List.prod_append, List.prod_nil, mul_one, gsimEvolved_cons]
      rw [trace_conj_step, ih']

/-! ## Non-vacuity and the variance–reconstruction capstone -/

/-- **Non-vacuity.** The g-sim reconstruction is exercised on the concrete
`su(2)` DLA: for the gate generator `I • (X/√2) ∈ su(2)` and observable
`X/√2`, the loss reconstructs from the `3` quantum data `Tr[ρ Bⱼ]`. -/
theorem gsim_su2_witness (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (NormedSpace.exp (Complex.I • su2HermBasis.B su2i0) * ρ
        * NormedSpace.exp (-(Complex.I • su2HermBasis.B su2i0))
        * su2HermBasis.B su2i0).trace
      = ∑ j, (∑ i, gsimAd su2HermBasis (-(Complex.I • su2HermBasis.B su2i0)) j i
            * hsInner (su2HermBasis.B i) (su2HermBasis.B su2i0))
          * (ρ * su2HermBasis.B j).trace :=
  gsim_loss_reconstruction su2HermBasis ρ
    (Submodule.smul_mem _ _ (su2HermBasis.basis_mem_dla su2i0))
    (su2HermBasis.basis_mem_dla su2i0)

/-- **g-sim variance–reconstruction capstone for Lie-algebraic circuits.** At a
fixed dynamical Lie algebra `g`, one hypothesis bundle — a Hermitian orthonormal
DLA basis `b`, Hermitian `ρ`, `O`, the second-moment data `M` (the **named
Haar/twirl/Schur hypothesis bundle** of `RagoneInterface`; the variance
conclusion is conditional on it, and it is discharged unconditionally for `su(2)`
by `QubitTwoDesign.main` — see `su2_variance_and_reconstruction_unconditional`),
and gate generators drawn from `g` — yields the **conjunction** of two
independent conclusions:

1. *(variance / trainability)* the loss variance is `P_g(ρ) · P_g(O) / dim g` —
   for polynomially large `dim g` the landscape is barren-plateau-free at rate
   `1/dim g`;
2. *(reconstruction)* for every gate list from `g`, the loss is exactly
   reconstructible from the `dim g` quantum data `Tr[ρ Bⱼ]`.

This is a conjunction at fixed `g`: the two halves share only the basis `b` (the
first ignores the gate list, the second ignores the bundle `M`). The same
algebraic smallness that protects the gradient signal hands the loss to a
classical simulator with quantum-data access. The informal "dichotomy" framing is
prose; the theorem states the conjunction. -/
theorem gsim_variance_and_reconstruction (b : DLAHermBasis gens)
    {ρ O : Matrix (Fin N) (Fin N) ℂ} (M : RagoneSecondMoment b ρ O)
    (hρ : ρᴴ = ρ) (hO : Oᴴ = O) (hdim : 0 < b.dim)
    (hOg : O ∈ (dynamicalLieAlgebra gens).toSubmodule) :
    ((M.variance : ℂ) = b.gPurity ρ * b.gPurity O / (b.dim : ℂ))
    ∧ ∀ (Gs : List (Matrix (Fin N) (Fin N) ℂ)),
        (∀ A ∈ Gs, A ∈ (dynamicalLieAlgebra gens).toSubmodule) →
        ((Gs.map NormedSpace.exp).prod * ρ
            * ((Gs.reverse).map (fun A => NormedSpace.exp (-A))).prod * O).trace
          = ∑ j, hsInner (b.B j) (gsimEvolved Gs O) * (ρ * b.B j).trace :=
  ⟨M.variance_eq_gPurity hρ hO hdim,
    fun _ hGs => gsim_loss_reconstruction_ansatz b hGs ρ hOg⟩

/-- **The capstone, unconditionally discharged on `su(2)`.** Instantiating
`gsim_variance_and_reconstruction` at the concrete Clifford doubled-twirl
second moment `QubitTwoDesign.main` — the finite twirl input is discharged by
the doubled-commutant-completeness surrogate, and H2 by Schur, so nothing is
deferred — gives a concrete end-to-end witness: the `su(2)` loss variance is `P_g(ρ)·P_g(O)/3`
(numerically `1/3` by `QubitTwoDesign.main_variance_eq_third`), and
simultaneously the loss of every `su(2)`-generated gate list reconstructs from
the `3` quantum data `Tr[ρ Bⱼ]`. -/
theorem su2_variance_and_reconstruction_unconditional :
    ((QubitTwoDesign.main.variance : ℂ)
        = su2HermBasis.gPurity (su2HermBasis.B su2i0)
            * su2HermBasis.gPurity (su2HermBasis.B su2i0)
            / (su2HermBasis.dim : ℂ))
    ∧ ∀ (Gs : List (Matrix (Fin 2) (Fin 2) ℂ)),
        (∀ A ∈ Gs, A ∈ (dynamicalLieAlgebra su2Gens).toSubmodule) →
        ((Gs.map NormedSpace.exp).prod * su2HermBasis.B su2i0
            * ((Gs.reverse).map (fun A => NormedSpace.exp (-A))).prod
            * su2HermBasis.B su2i0).trace
          = ∑ j, hsInner (su2HermBasis.B j)
                (gsimEvolved Gs (su2HermBasis.B su2i0))
              * (su2HermBasis.B su2i0 * su2HermBasis.B j).trace :=
  gsim_variance_and_reconstruction su2HermBasis QubitTwoDesign.main
    (su2HermBasis.herm su2i0) (su2HermBasis.herm su2i0)
    su2HermBasis_dim_pos (su2HermBasis.basis_mem_dla su2i0)

/-- **The nondegenerate capstone, unconditionally discharged on `su(2)`.**
Instantiating `gsim_variance_and_reconstruction` at the concrete Clifford
doubled-twirl second moment `QubitTwoDesign.su2NondegenerateSecondMoment` gives
the same conjunction as `su2_variance_and_reconstruction_unconditional`, but at
`ρ = (1/2) • B₀` and `O = (1/3) • B₀`. Both sides are nondegenerate, and
nothing is deferred: the doubled-commutant-completeness surrogate and Schur
hypotheses are proved in the bundle. The variance side is therefore `P_g(ρ) P_g(O) / 3`,
numerically `1/108` by
`QubitTwoDesign.su2NondegenerateSecondMoment_variance_eq`. -/
theorem su2_variance_and_reconstruction_nondegenerate :
    ((QubitTwoDesign.su2NondegenerateSecondMoment.variance : ℂ)
        = su2HermBasis.gPurity ((1 / 2 : ℂ) • su2HermBasis.B su2i0)
            * su2HermBasis.gPurity ((1 / 3 : ℂ) • su2HermBasis.B su2i0)
            / (su2HermBasis.dim : ℂ))
    ∧ ∀ (Gs : List (Matrix (Fin 2) (Fin 2) ℂ)),
        (∀ A ∈ Gs, A ∈ (dynamicalLieAlgebra su2Gens).toSubmodule) →
        ((Gs.map NormedSpace.exp).prod * ((1 / 2 : ℂ) • su2HermBasis.B su2i0)
            * ((Gs.reverse).map (fun A => NormedSpace.exp (-A))).prod
            * ((1 / 3 : ℂ) • su2HermBasis.B su2i0)).trace
          = ∑ j, hsInner (su2HermBasis.B j)
                (gsimEvolved Gs ((1 / 3 : ℂ) • su2HermBasis.B su2i0))
              * (((1 / 2 : ℂ) • su2HermBasis.B su2i0)
                  * su2HermBasis.B j).trace := by
  have hOg :
      QubitTwoDesign.su2NondegenerateO ∈
        (dynamicalLieAlgebra su2Gens).toSubmodule := by
    rw [QubitTwoDesign.su2NondegenerateO]
    exact Submodule.smul_mem _ _ (su2HermBasis.basis_mem_dla su2i0)
  simpa [QubitTwoDesign.su2NondegenerateRho, QubitTwoDesign.su2NondegenerateO]
    using gsim_variance_and_reconstruction su2HermBasis
      QubitTwoDesign.su2NondegenerateSecondMoment
      QubitTwoDesign.su2NondegenerateRho_isHermitian
      QubitTwoDesign.su2NondegenerateO_isHermitian
      su2HermBasis_dim_pos hOg

/-- **Reductive g-sim variance–reconstruction capstone.** The reductive-bundle
form of `gsim_variance_and_reconstruction`: from a reductive decomposition
`g = ⊕ⱼ gⱼ` (a `RagoneReductive` bundle `R`) together with a Hermitian orthonormal
basis `b` of the whole `g`, one gets the **conjunction** of the same two
conclusions, now carrying the per-ideal variance law:

1. *(variance / trainability)* the total loss variance is the per-ideal purity
   sum `Σⱼ P_{gⱼ}(ρ) · P_{gⱼ}(O) / dim gⱼ` (`RagoneReductive.totalVariance_eq`);
2. *(reconstruction)* for every gate list from `g`, the loss is exactly
   reconstructible from the `dim g` quantum data `Tr[ρ Bⱼ]`
   (`gsim_loss_reconstruction_ansatz`).

As with `gsim_variance_and_reconstruction`, this is a conjunction at fixed `g`:
`b` and `R` are logically independent — the reconstruction half uses only the
union basis `b`, the variance half only the bundle `R`. It is the single-`g` form
that an `n`-indexed family result routes through. -/
theorem gsim_variance_and_reconstruction_reductive (b : DLAHermBasis gens)
    {ρ O : Matrix (Fin N) (Fin N) ℂ} (R : RagoneReductive ρ O)
    (hρ : ρᴴ = ρ) (hO : Oᴴ = O) (hdim : ∀ j, 0 < (R.basis j).dim)
    (hOg : O ∈ (dynamicalLieAlgebra gens).toSubmodule) :
    ((R.variance : ℂ)
        = ∑ j, (R.basis j).gPurity ρ * (R.basis j).gPurity O / ((R.basis j).dim : ℂ))
    ∧ ∀ (Gs : List (Matrix (Fin N) (Fin N) ℂ)),
        (∀ A ∈ Gs, A ∈ (dynamicalLieAlgebra gens).toSubmodule) →
        ((Gs.map NormedSpace.exp).prod * ρ
            * ((Gs.reverse).map (fun A => NormedSpace.exp (-A))).prod * O).trace
          = ∑ j, hsInner (b.B j) (gsimEvolved Gs O) * (ρ * b.B j).trace :=
  ⟨R.totalVariance_eq hρ hO hdim,
    fun _ hGs => gsim_loss_reconstruction_ansatz b hGs ρ hOg⟩

end QuantumAlg
