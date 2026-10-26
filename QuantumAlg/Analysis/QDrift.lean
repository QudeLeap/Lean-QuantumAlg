/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.Noncommutative
public import QuantumAlg.Analysis.Trotter.Evolution
public import QuantumAlg.Util.ExpRemainder
public import QuantumAlg.Util.Matrix.Trace.Norm
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# qDRIFT averaged-channel error analysis

This file starts the qDRIFT formalization at the linear-algebra layer.  A
superoperator is just a complex-linear map on finite-register Hilbert
operators; channel positivity, trace preservation, and probability theory are
kept out of this interface.  The file contains the algebraic cancellation
lemmas, an induced trace-norm instance for finite matrices, and the concrete
operator-norm estimates used to prove the concrete induced trace-norm qDRIFT
bounds. The averaging and hybrid construction follow
[C19, qDRIFT_arXiv_V2submit.tex:152-185]. This is a comparison
of averaged channels; no diamond-norm, sampled
execution, or circuit-resource theorem is asserted.
-/

@[expose] public section

namespace QuantumAlg

open HilbertOperator

noncomputable section

open scoped ComplexOrder MatrixOrder

/-- A superoperator is a complex-linear map on raw Hilbert operators. -/
abbrev SuperOp (R : Register) : Type :=
  HilbertOperator R →ₗ[ℂ] HilbertOperator R

/-- Reinterpret an algebraic superoperator as a continuous linear map.

The domain is finite dimensional, so Mathlib's
`LinearMap.toContinuousLinearMap` supplies continuity without adding channel
assumptions. -/
def continuousSuperOp {R : Register} (Φ : SuperOp R) :
    HilbertOperator R →L[ℂ] HilbertOperator R :=
  LinearMap.toContinuousLinearMap Φ

@[simp]
lemma continuousSuperOp_apply {R : Register} (Φ : SuperOp R)
    (X : HilbertOperator R) :
    continuousSuperOp Φ X = Φ X := by
  rfl

@[simp]
lemma continuousSuperOp_coe {R : Register} (Φ : SuperOp R) :
    ((continuousSuperOp Φ) : HilbertOperator R →ₗ[ℂ] HilbertOperator R) = Φ := by
  rfl

/-- Reinterpret a superoperator as a linear map on matrices equipped with the trace norm. -/
def traceNormedSuperOp {R : Register} (Φ : SuperOp R) :
    TraceNormedMatrix R.Index →ₗ[ℂ] TraceNormedMatrix R.Index where
  toFun X := ⟨Φ (X : HilbertOperator R)⟩
  map_add' X Y := by
    apply TraceNormedMatrix.ext
    simp
  map_smul' c X := by
    apply TraceNormedMatrix.ext
    simp

@[simp]
lemma traceNormedSuperOp_apply {R : Register} (Φ : SuperOp R)
    (X : TraceNormedMatrix R.Index) :
    ((traceNormedSuperOp Φ X : TraceNormedMatrix R.Index) : HilbertOperator R) =
      Φ (X : HilbertOperator R) := by
  rfl

@[simp]
lemma traceNormedSuperOp_zero {R : Register} :
    traceNormedSuperOp (0 : SuperOp R) = 0 := by
  ext X
  simp

@[simp]
lemma traceNormedSuperOp_add {R : Register} (Φ Ψ : SuperOp R) :
    traceNormedSuperOp (Φ + Ψ) = traceNormedSuperOp Φ + traceNormedSuperOp Ψ := by
  ext X
  simp

@[simp]
lemma traceNormedSuperOp_smul {R : Register} (c : ℂ) (Φ : SuperOp R) :
    traceNormedSuperOp (c • Φ) = c • traceNormedSuperOp Φ := by
  ext X
  simp

@[simp]
lemma traceNormedSuperOp_neg {R : Register} (Φ : SuperOp R) :
    traceNormedSuperOp (-Φ) = -traceNormedSuperOp Φ := by
  ext X
  simp

@[simp]
lemma traceNormedSuperOp_sub {R : Register} (Φ Ψ : SuperOp R) :
    traceNormedSuperOp (Φ - Ψ) = traceNormedSuperOp Φ - traceNormedSuperOp Ψ := by
  ext X
  simp [sub_eq_add_neg]

@[simp]
lemma traceNormedSuperOp_sum {R : Register} {ι : Type} [Fintype ι]
    (Φ : ι → SuperOp R) :
    traceNormedSuperOp (∑ i, Φ i) = ∑ i, traceNormedSuperOp (Φ i) := by
  classical
  ext X
  simp

/-- The induced superoperator norm from the trace norm on matrices. -/
def inducedTraceNorm {R : Register} (Φ : SuperOp R) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (traceNormedSuperOp Φ)‖

/-- Pull a chosen norm-like functional on continuous linear maps back to
algebraic superoperators.  When a concrete normed-space instance is available,
the intended argument is `fun Φc => ‖Φc‖`. -/
def continuousSuperOpNorm {R : Register}
    (continuousNorm : (HilbertOperator R →L[ℂ] HilbertOperator R) → ℝ)
    (Φ : SuperOp R) : ℝ :=
  continuousNorm (continuousSuperOp Φ)

/-- Composition of superoperators. -/
def superOpComp {R : Register} (Φ Ψ : SuperOp R) : SuperOp R :=
  Φ.comp Ψ

@[simp]
lemma superOpComp_apply {R : Register} (Φ Ψ : SuperOp R) (X : HilbertOperator R) :
    superOpComp Φ Ψ X = Φ (Ψ X) := by
  rfl

/-- Iterated composition power of a superoperator. -/
def superOpPower {R : Register} (Φ : SuperOp R) (n : ℕ) : SuperOp R :=
  Φ ^ n

@[simp]
lemma superOpPower_zero {R : Register} (Φ : SuperOp R) :
    superOpPower Φ 0 = LinearMap.id := by
  rfl

@[simp]
lemma superOpPower_succ {R : Register} (Φ : SuperOp R) (n : ℕ) :
    superOpPower Φ (n + 1) = superOpComp (superOpPower Φ n) Φ := by
  rfl

/-- Telescoping identity for powers of superoperators under composition. -/
lemma superOpPower_diff_eq_sum {R : Register} (U E : SuperOp R) (r : ℕ) :
    superOpPower U r - superOpPower E r =
      ∑ k ∈ Finset.range r,
        superOpComp (superOpPower U (r - 1 - k))
          (superOpComp (U - E) (superOpPower E k)) := by
  simpa [superOpPower, superOpComp, Module.End.mul_eq_comp, LinearMap.comp_assoc,
    mul_assoc] using
    (noncomm_power_diff U E r)

/-- Abstract norm assumptions for superoperators.

This packages the functional-analytic facts needed by qDRIFT error estimates
without choosing a concrete induced norm in this file.  Later developments can
instantiate this interface with a trace-induced norm or a different operator
norm. -/
structure SuperOpNormProperties {R : Register} (superOpNorm : SuperOp R → ℝ)
    (scalarNorm : ℂ → ℝ) : Prop where
  norm_sum_le : ∀ {ι : Type} [Fintype ι] (Φ : ι → SuperOp R),
    superOpNorm (∑ j, Φ j) ≤ ∑ j, superOpNorm (Φ j)
  norm_smul : ∀ (c : ℂ) (Φ : SuperOp R),
    superOpNorm (c • Φ) = scalarNorm c * superOpNorm Φ
  norm_sub_le : ∀ (Φ Ψ : SuperOp R),
    superOpNorm (Φ - Ψ) ≤ superOpNorm Φ + superOpNorm Ψ

namespace SuperOpNormProperties

lemma norm_add_le {R : Register} {superOpNorm : SuperOp R → ℝ}
    {scalarNorm : ℂ → ℝ}
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (Φ Ψ : SuperOp R) :
    superOpNorm (Φ + Ψ) ≤ superOpNorm Φ + superOpNorm Ψ := by
  let f : Fin 2 → SuperOp R := fun i => if i = 0 then Φ else Ψ
  have h := hnorm.norm_sum_le f
  simpa [f, Fin.sum_univ_two] using h

end SuperOpNormProperties

lemma inducedTraceNorm_properties {R : Register} :
    SuperOpNormProperties (R := R) inducedTraceNorm (fun c : ℂ => ‖c‖) where
  norm_sum_le := by
    intro ι _ Φ
    classical
    simpa [inducedTraceNorm] using
      (norm_sum_le Finset.univ
        (fun i => LinearMap.toContinuousLinearMap (traceNormedSuperOp (Φ i))))
  norm_smul := by
    intro c Φ
    simp [inducedTraceNorm, norm_smul]
  norm_sub_le := by
    intro Φ Ψ
    simpa [inducedTraceNorm] using
      (norm_sub_le
        (LinearMap.toContinuousLinearMap (traceNormedSuperOp Φ))
        (LinearMap.toContinuousLinearMap (traceNormedSuperOp Ψ)))

@[simp]
lemma inducedTraceNorm_neg {R : Register} (Φ : SuperOp R) :
    inducedTraceNorm (-Φ) = inducedTraceNorm Φ := by
  simp [inducedTraceNorm,
    (norm_neg (LinearMap.toContinuousLinearMap (traceNormedSuperOp Φ)))]

/-- A superoperator is nonexpansive for left composition under an abstract norm. -/
structure SuperOpLeftNonexpansive {R : Register} (superOpNorm : SuperOp R → ℝ)
    (Φ : SuperOp R) : Prop where
  norm_comp_le : ∀ Ψ, superOpNorm (superOpComp Φ Ψ) ≤ superOpNorm Ψ

/-- A superoperator is nonexpansive for right composition under an abstract norm. -/
structure SuperOpRightNonexpansive {R : Register} (superOpNorm : SuperOp R → ℝ)
    (Φ : SuperOp R) : Prop where
  norm_comp_le : ∀ Ψ, superOpNorm (superOpComp Ψ Φ) ≤ superOpNorm Ψ

/-- Abstract qDRIFT weight conditions for a chosen scalar norm. -/
structure QDriftWeightConditions {ι : Type} [Fintype ι]
    (scalarNorm : ℂ → ℝ) (p : ι → ℝ) : Prop where
  sum_eq_one : ∑ j, (p j : ℂ) = 1
  scalar_weights_bound : ∑ j, scalarNorm (p j : ℂ) ≤ 1
  scalar_nonneg : ∀ j, 0 ≤ scalarNorm (p j : ℂ)

/-- Real qDRIFT probability weights. -/
structure QDriftProbabilityWeights {ι : Type} [Fintype ι] (p : ι → ℝ) : Prop where
  nonneg : ∀ j, 0 ≤ p j
  sum_eq_one : ∑ j, p j = 1

/-- The coefficient mass `λ = ∑_j h_j` used by qDRIFT. -/
def qdriftLambda {ι : Type} [Fintype ι] (h : ι → ℝ) : ℝ :=
  ∑ j, h j

/-- qDRIFT samples term `j` with probability `h_j / λ`. -/
def qdriftProbabilities {ι : Type} [Fintype ι] (h : ι → ℝ) : ι → ℝ :=
  fun j => h j / qdriftLambda h

/-- qDRIFT uses a scaled segment time `t λ / steps`. -/
def qdriftStepTime {ι : Type} [Fintype ι]
    (h : ι → ℝ) (t : ℝ) (steps : ℕ) : ℝ :=
  t * qdriftLambda h / steps

lemma qdriftProbabilities_nonneg {ι : Type} [Fintype ι]
    (h : ι → ℝ) (h_nonneg : ∀ j, 0 ≤ h j) :
    ∀ j, 0 ≤ qdriftProbabilities h j := by
  intro j
  exact div_nonneg (h_nonneg j) (Finset.sum_nonneg fun i _ => h_nonneg i)

lemma qdriftProbabilities_sum_eq_one {ι : Type} [Fintype ι]
    (h : ι → ℝ) (h_lambda_ne_zero : qdriftLambda h ≠ 0) :
    ∑ j, qdriftProbabilities h j = 1 := by
  rw [show (∑ j, qdriftProbabilities h j) = qdriftLambda h / qdriftLambda h by
    simp [qdriftProbabilities, qdriftLambda, Finset.sum_div]]
  exact div_self h_lambda_ne_zero

lemma qdriftProbabilityWeights {ι : Type} [Fintype ι]
    (h : ι → ℝ) (h_nonneg : ∀ j, 0 ≤ h j)
    (h_lambda_ne_zero : qdriftLambda h ≠ 0) :
    QDriftProbabilityWeights (qdriftProbabilities h) :=
  ⟨qdriftProbabilities_nonneg h h_nonneg,
    qdriftProbabilities_sum_eq_one h h_lambda_ne_zero⟩

namespace QDriftWeightConditions

/-- Build abstract qDRIFT weight conditions from real probability weights. -/
lemma of_probability_weights {ι : Type} [Fintype ι]
    (scalarNorm : ℂ → ℝ) (p : ι → ℝ)
    (hscalar : ∀ j, scalarNorm (p j : ℂ) = p j)
    (hprob : QDriftProbabilityWeights p) :
    QDriftWeightConditions scalarNorm p where
  sum_eq_one := by
    exact_mod_cast hprob.sum_eq_one
  scalar_weights_bound := by
    calc
      ∑ j, scalarNorm (p j : ℂ) = ∑ j, p j := by
        simp [hscalar]
      _ = 1 := hprob.sum_eq_one
      _ ≤ 1 := le_rfl
  scalar_nonneg := by
    intro j
    rw [hscalar j]
    exact hprob.nonneg j

/-- Real probability weights are valid for the usual complex norm. -/
lemma of_probability_weights_norm {ι : Type} [Fintype ι]
    (p : ι → ℝ) (hprob : QDriftProbabilityWeights p) :
    QDriftWeightConditions (fun c : ℂ => ‖c‖) p :=
  of_probability_weights (fun c : ℂ => ‖c‖) p
    (by
      intro j
      simp [Complex.norm_real, abs_of_nonneg (hprob.nonneg j)])
    hprob

end QDriftWeightConditions

/-- Left multiplication as a superoperator, `X ↦ A * X`. -/
def leftMulSuperOp {R : Register} (A : HilbertOperator R) : SuperOp R :=
  LinearMap.mulLeft ℂ A

/-- Right multiplication as a superoperator, `X ↦ X * A`. -/
def rightMulSuperOp {R : Register} (A : HilbertOperator R) : SuperOp R :=
  LinearMap.mulRight ℂ A

@[simp]
lemma leftMulSuperOp_apply {R : Register} (A X : HilbertOperator R) :
    leftMulSuperOp A X = A * X := by
  rfl

@[simp]
lemma rightMulSuperOp_apply {R : Register} (A X : HilbertOperator R) :
    rightMulSuperOp A X = X * A := by
  rfl

/-- Two-sided multiplication as a superoperator, `X ↦ A * X * B`. -/
def twoSidedMulSuperOp {R : Register} (A B : HilbertOperator R) : SuperOp R :=
  (leftMulSuperOp A).comp (rightMulSuperOp B)

@[simp]
lemma twoSidedMulSuperOp_apply {R : Register} (A B X : HilbertOperator R) :
    twoSidedMulSuperOp A B X = A * (X * B) := by
  rfl

/-- Abstract control of the norm of a two-sided multiplication superoperator.

Concrete induced trace-norm or operator-norm instances should prove this in a
separate layer. -/
structure SuperOpTwoSidedMulNormControl {R : Register}
    (superOpNorm : SuperOp R → ℝ) (matrixNorm : HilbertOperator R → ℝ) : Prop where
  norm_nonneg : ∀ A, 0 ≤ matrixNorm A
  norm_two_sided : ∀ A B,
    superOpNorm (twoSidedMulSuperOp A B) ≤ matrixNorm A * matrixNorm B

/-- Pure matrix inequality needed to instantiate the induced trace norm for
two-sided multiplication.

This is the pointwise linear-algebra theorem behind
`‖X ↦ A * X * B‖₁→₁ ≤ ‖A‖op * ‖B‖op`: once the pointwise trace-norm inequality
is available, the induced superoperator bound follows formally. -/
structure TraceNormTwoSidedMulControl (R : Register) : Prop where
  traceNorm_two_sided :
    ∀ A B X : HilbertOperator R,
      Matrix.traceNorm (A * (X * B)) ≤
        opNorm A * opNorm B * Matrix.traceNorm X

/-- Trace-pairing Hölder inequality for the trace norm and the L2/operator norm.

This is the usual duality estimate `|Tr(C X)| ≤ ‖C‖op ‖X‖₁`.  Once available,
the two-sided multiplication control follows by applying it to the polar
unitary that attains the trace norm of `A * X * B`. -/
structure TraceNormHolderControl (R : Register) : Prop where
  trace_abs_mul_le :
    ∀ C X : HilbertOperator R,
      ‖(C * X).trace‖ ≤ opNorm C * Matrix.traceNorm X

private lemma opNorm_entry_le {R : Register}
    (A : HilbertOperator R) (i j : R.Index) :
    ‖A i j‖ ≤ opNorm A := by
  unfold opNorm
  open scoped Matrix.Norms.L2Operator in
  let e : EuclideanSpace ℂ R.Index := EuclideanSpace.basisFun R.Index ℂ j
  have hcoord :
      ‖A i j‖ ≤ ‖Matrix.toEuclideanCLM (n := R.Index) (𝕜 := ℂ) A e‖ := by
    simpa [e, Matrix.ofLp_toEuclideanCLM, EuclideanSpace.basisFun_apply,
      Matrix.mulVec_single_one] using
      (PiLp.norm_apply_le
        (Matrix.toEuclideanCLM (n := R.Index) (𝕜 := ℂ) A e) i)
  have hop :=
    ContinuousLinearMap.le_opNorm
      (Matrix.toEuclideanCLM (n := R.Index) (𝕜 := ℂ) A) e
  have he : ‖e‖ = 1 := by
    simp [e]
  calc
    ‖A i j‖ ≤ ‖Matrix.toEuclideanCLM (n := R.Index) (𝕜 := ℂ) A e‖ := hcoord
    _ ≤ ‖Matrix.toEuclideanCLM (n := R.Index) (𝕜 := ℂ) A‖ * ‖e‖ := hop
    _ = ‖A‖ * 1 := by rw [← Matrix.cstar_norm_def A, he]
    _ = ‖A‖ := by ring

private lemma trace_mul_posSemidef_abs_le_operatorNorm_mul_trace
    {R : Register} (D P : HilbertOperator R)
    (hP : P.PosSemidef) :
    ‖(D * P).trace‖ ≤ opNorm D * RCLike.re P.trace := by
  let V : Matrix.unitaryGroup R.Index ℂ := hP.1.eigenvectorUnitary
  let E : HilbertOperator R := Matrix.diagonal (fun i => (hP.1.eigenvalues i : ℂ))
  let W : HilbertOperator R := (V : HilbertOperator R).conjTranspose * D * V
  have hP_spectral :
      P = ((V : HilbertOperator R) * E) *
        (V : HilbertOperator R).conjTranspose := by
    simpa [V, E, Matrix.star_eq_conjTranspose, Function.comp_def] using
      hP.1.spectral_theorem
  have htrace :
      (D * P).trace =
        ∑ i, (hP.1.eigenvalues i : ℂ) * W i i := by
    have hDP :
        D * P =
          D * (((V : HilbertOperator R) * E) *
            (V : HilbertOperator R).conjTranspose) := by
      rw [hP_spectral]
    have hcycle :
        (D * (((V : HilbertOperator R) * E) *
            (V : HilbertOperator R).conjTranspose)).trace =
          (W * E).trace := by
      rw [Matrix.trace_mul_cycle'
        (A := D) (B := (V : HilbertOperator R) * E)
        (C := (V : HilbertOperator R).conjTranspose)]
      simp [W, V, E, Matrix.mul_assoc]
    rw [show (D * P).trace =
        (D * (((V : HilbertOperator R) * E) *
          (V : HilbertOperator R).conjTranspose)).trace by rw [hDP]]
    rw [hcycle]
    simp [W, E, Matrix.trace, Matrix.mul_apply, Matrix.diagonal, mul_comm]
  have hWnorm : opNorm W = opNorm D := by
    have hVstar : (V : HilbertOperator R).conjTranspose ∈
        Matrix.unitaryGroup R.Index ℂ := by
      rw [Matrix.mem_unitaryGroup_iff]
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
      exact Matrix.UnitaryGroup.star_mul_self V
    calc
      opNorm W =
          opNorm (((V : HilbertOperator R).conjTranspose * D) *
            (V : HilbertOperator R)) := by
        simp [W, Matrix.mul_assoc]
      _ = opNorm ((V : HilbertOperator R).conjTranspose * D) := by
        simpa using opNorm_unitary_mul_right
          (A := (V : HilbertOperator R).conjTranspose * D) (U := V)
      _ = opNorm D := by
        simpa using opNorm_unitary_mul_left
          (U := ⟨(V : HilbertOperator R).conjTranspose, hVstar⟩) (A := D)
  have htraceP : RCLike.re P.trace = ∑ i, hP.1.eigenvalues i := by
    rw [hP.1.trace_eq_sum_eigenvalues]
    simp
  calc
    ‖(D * P).trace‖
        = ‖∑ i, (hP.1.eigenvalues i : ℂ) * W i i‖ := by
          rw [htrace]
    _ ≤ ∑ i, ‖(hP.1.eigenvalues i : ℂ) * W i i‖ := norm_sum_le _ _
    _ ≤ ∑ i, hP.1.eigenvalues i * opNorm D := by
      apply Finset.sum_le_sum
      intro i _
      have heig_nonneg : 0 ≤ hP.1.eigenvalues i := hP.eigenvalues_nonneg i
      calc
        ‖(hP.1.eigenvalues i : ℂ) * W i i‖
            = hP.1.eigenvalues i * ‖W i i‖ := by
              simp [Complex.norm_real, abs_of_nonneg heig_nonneg]
        _ ≤ hP.1.eigenvalues i * opNorm W := by
          exact mul_le_mul_of_nonneg_left
            (opNorm_entry_le W i i) heig_nonneg
        _ = hP.1.eigenvalues i * opNorm D := by rw [hWnorm]
    _ = opNorm D * RCLike.re P.trace := by
      rw [htraceP]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

lemma traceNormHolderControl_of_operatorNorm {R : Register} :
    TraceNormHolderControl R where
  trace_abs_mul_le C X := by
    let P : HilbertOperator R := CFC.sqrt (X.conjTranspose * X)
    let U : Matrix.unitaryGroup R.Index ℂ := Matrix.polarUnitary X
    have hP_pos : P.PosSemidef := by
      exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (X.conjTranspose * X))
    have hpolar : (U : HilbertOperator R) * P = X := by
      simpa [P, U] using
        Matrix.polarUnitary_mul_cfc_sqrt_conjTranspose_mul_self (A := X)
    have htrace :
        (C * X).trace = ((C * (U : HilbertOperator R)) * P).trace := by
      rw [← hpolar]
      simp [Matrix.mul_assoc]
    calc
      ‖(C * X).trace‖
          = ‖((C * (U : HilbertOperator R)) * P).trace‖ := by rw [htrace]
      _ ≤ opNorm (C * (U : HilbertOperator R)) * RCLike.re P.trace :=
          trace_mul_posSemidef_abs_le_operatorNorm_mul_trace
            (C * (U : HilbertOperator R)) P hP_pos
      _ = opNorm C * Matrix.traceNorm X := by
          rw [opNorm_unitary_mul_right (A := C)]
          rfl

/-- Left multiplication is linear in the multiplier. -/
lemma leftMulSuperOp_sum {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (w : ι → ℂ) :
    leftMulSuperOp (∑ j, w j • H j)
      = ∑ j, w j • leftMulSuperOp (H j) := by
  ext X
  simp [leftMulSuperOp, Finset.sum_mul]

/-- Right multiplication is linear in the multiplier. -/
lemma rightMulSuperOp_sum {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (w : ι → ℂ) :
    rightMulSuperOp (∑ j, w j • H j)
      = ∑ j, w j • rightMulSuperOp (H j) := by
  ext X
  simp [rightMulSuperOp, Finset.mul_sum]

/-- The Liouvillian commutator superoperator, `X ↦ H * X - X * H`. -/
def commutatorSuperOp {R : Register} (H : HilbertOperator R) : SuperOp R :=
  leftMulSuperOp H - rightMulSuperOp H

@[simp]
lemma commutatorSuperOp_apply {R : Register} (H X : HilbertOperator R) :
    commutatorSuperOp H X = H * X - X * H := by
  rfl

/-- The commutator superoperator is linear in its Hamiltonian argument. -/
lemma commutatorSuperOp_sum {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (w : ι → ℂ) :
    commutatorSuperOp (∑ j, w j • H j)
      = ∑ j, w j • commutatorSuperOp (H j) := by
  rw [commutatorSuperOp, leftMulSuperOp_sum, rightMulSuperOp_sum]
  ext X
  simp [commutatorSuperOp, smul_sub, Finset.sum_sub_distrib]

/-- The first-order generator of unitary conjugation, `X ↦ -i • (H * X - X * H)`. -/
def liouvillianSuperOp {R : Register} (H : HilbertOperator R) : SuperOp R :=
  (-Complex.I) • commutatorSuperOp H

@[simp]
lemma liouvillianSuperOp_apply {R : Register} (H X : HilbertOperator R) :
    liouvillianSuperOp H X = (-Complex.I) • (H * X - X * H) := by
  rfl

/-- The Liouvillian generator is linear in its Hamiltonian argument. -/
lemma liouvillianSuperOp_sum {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (w : ι → ℂ) :
    liouvillianSuperOp (∑ j, w j • H j)
      = ∑ j, w j • liouvillianSuperOp (H j) := by
  rw [liouvillianSuperOp, commutatorSuperOp_sum]
  ext X
  simp [liouvillianSuperOp, Finset.smul_sum, smul_smul, mul_comm]

/-- The formal first-order superoperator `id + τ • G`. -/
def firstOrderSuperOp {R : Register} (G : SuperOp R) (τ : ℝ) : SuperOp R :=
  LinearMap.id + (τ : ℂ) • G

@[simp]
lemma firstOrderSuperOp_apply {R : Register} (G : SuperOp R) (τ : ℝ)
    (X : HilbertOperator R) :
    firstOrderSuperOp G τ X = X + (τ : ℂ) • G X := by
  rfl

@[simp]
lemma firstOrderSuperOp_zero {R : Register} (G : SuperOp R) :
    firstOrderSuperOp G 0 = LinearMap.id := by
  ext X
  simp [firstOrderSuperOp]

/-- Unitary conjugation, viewed only as a linear map on matrices. -/
def conjugationSuperOp {R : Register} (U : HilbertOperator R) : SuperOp R :=
  (leftMulSuperOp U).comp (rightMulSuperOp (star U))

@[simp]
lemma conjugationSuperOp_apply {R : Register} (U X : HilbertOperator R) :
    conjugationSuperOp U X = U * (X * star U) := by
  rfl

/-- A superoperator is nonexpansive for the matrix trace norm. -/
def TraceNormNonexpansive {R : Register} (Φ : SuperOp R) : Prop :=
  ∀ X : HilbertOperator R, Matrix.traceNorm (Φ X) ≤ Matrix.traceNorm X

namespace TraceNormNonexpansive

lemma one {R : Register} : TraceNormNonexpansive (1 : SuperOp R) := by
  intro X
  simp

lemma comp {R : Register} {Φ Ψ : SuperOp R}
    (hΦ : TraceNormNonexpansive Φ) (hΨ : TraceNormNonexpansive Ψ) :
    TraceNormNonexpansive (superOpComp Φ Ψ) := by
  intro X
  exact (hΦ (Ψ X)).trans (hΨ X)

lemma power {R : Register} {Φ : SuperOp R}
    (hΦ : TraceNormNonexpansive Φ) :
    ∀ n : ℕ, TraceNormNonexpansive (superOpPower Φ n)
  | 0 => by
      simpa [superOpPower] using (one (R := R))
  | n + 1 => by
      rw [superOpPower_succ]
      exact comp (power hΦ n) hΦ

end TraceNormNonexpansive

lemma inducedTraceNorm_le_one_of_traceNorm_nonexpansive {R : Register}
    {Φ : SuperOp R} (hΦ : TraceNormNonexpansive Φ) :
    inducedTraceNorm Φ ≤ 1 := by
  unfold inducedTraceNorm
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro X
  simpa using hΦ (X : HilbertOperator R)

lemma traceNormNonexpansive_left_inducedTraceNorm_nonexpansive {R : Register}
    {pre : SuperOp R} (hpre : TraceNormNonexpansive pre) :
    SuperOpLeftNonexpansive inducedTraceNorm pre where
  norm_comp_le Ψ := by
    unfold inducedTraceNorm
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
    intro X
    calc
      ‖LinearMap.toContinuousLinearMap (traceNormedSuperOp (superOpComp pre Ψ)) X‖
          ≤ ‖LinearMap.toContinuousLinearMap (traceNormedSuperOp Ψ) X‖ := by
            simpa using hpre (Ψ (X : HilbertOperator R))
      _ ≤ ‖LinearMap.toContinuousLinearMap (traceNormedSuperOp Ψ)‖ * ‖X‖ :=
          ContinuousLinearMap.le_opNorm _ _

lemma traceNormNonexpansive_right_inducedTraceNorm_nonexpansive {R : Register}
    {post : SuperOp R} (hpost : TraceNormNonexpansive post) :
    SuperOpRightNonexpansive inducedTraceNorm post where
  norm_comp_le Ψ := by
    unfold inducedTraceNorm
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
    intro X
    calc
      ‖LinearMap.toContinuousLinearMap (traceNormedSuperOp (superOpComp Ψ post)) X‖
          = ‖LinearMap.toContinuousLinearMap (traceNormedSuperOp Ψ)
              (traceNormedSuperOp post X)‖ := by
            rfl
      _ ≤ ‖LinearMap.toContinuousLinearMap (traceNormedSuperOp Ψ)‖ *
            ‖traceNormedSuperOp post X‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖LinearMap.toContinuousLinearMap (traceNormedSuperOp Ψ)‖ * ‖X‖ := by
          exact mul_le_mul_of_nonneg_left
            (by simpa using hpost (X : HilbertOperator R))
            (norm_nonneg _)

lemma inducedTraceNorm_twoSidedMul_control_of_matrix_control {R : Register}
    (hcontrol : TraceNormTwoSidedMulControl R) :
    SuperOpTwoSidedMulNormControl (R := R) inducedTraceNorm opNorm where
  norm_nonneg := opNorm_nonneg
  norm_two_sided A B := by
    unfold inducedTraceNorm
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (opNorm_nonneg A) (opNorm_nonneg B)) ?_
    intro X
    simpa [twoSidedMulSuperOp_apply, mul_assoc] using
      hcontrol.traceNorm_two_sided A B (X : HilbertOperator R)

lemma traceNormTwoSidedMulControl_of_holder {R : Register} [Nonempty R.Index]
    (hholder : TraceNormHolderControl R) :
    TraceNormTwoSidedMulControl R where
  traceNorm_two_sided A B X := by
    let Y : HilbertOperator R := A * (X * B)
    let U : Matrix.unitaryGroup R.Index ℂ := Matrix.polarUnitary Y
    have hpolar :
        Matrix.traceNorm Y =
          RCLike.re (((U : HilbertOperator R).conjTranspose * Y).trace) := by
      simpa [Y, U] using Matrix.traceNorm_eq_re_trace_polarUnitary (A := Y)
    calc
      Matrix.traceNorm (A * (X * B))
          = RCLike.re (((((U : HilbertOperator R).conjTranspose * A) * X * B).trace)) := by
            simpa [Y, Matrix.mul_assoc] using hpolar
      _ ≤ ‖(((((U : HilbertOperator R).conjTranspose * A) * X * B).trace))‖ :=
          RCLike.re_le_norm _
      _ = ‖((B * ((U : HilbertOperator R).conjTranspose * A)) * X).trace‖ := by
          congr 1
          rw [Matrix.trace_mul_cycle]
      _ ≤ opNorm (B * ((U : HilbertOperator R).conjTranspose * A)) * Matrix.traceNorm X :=
          hholder.trace_abs_mul_le (B * ((U : HilbertOperator R).conjTranspose * A)) X
      _ ≤ (opNorm B * opNorm ((U : HilbertOperator R).conjTranspose * A)) *
            Matrix.traceNorm X := by
          exact mul_le_mul_of_nonneg_right
            (opNorm_mul_le B ((U : HilbertOperator R).conjTranspose * A))
            (Matrix.traceNorm_nonneg X)
      _ ≤ (opNorm B * (opNorm (U : HilbertOperator R).conjTranspose * opNorm A)) *
            Matrix.traceNorm X := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (opNorm_mul_le (U : HilbertOperator R).conjTranspose A)
              (opNorm_nonneg B))
            (Matrix.traceNorm_nonneg X)
      _ = (opNorm B * (1 * opNorm A)) * Matrix.traceNorm X := by
          have hUstar : (U : HilbertOperator R).conjTranspose ∈
              Matrix.unitaryGroup R.Index ℂ := by
            rw [Matrix.mem_unitaryGroup_iff]
            rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
            exact Matrix.UnitaryGroup.star_mul_self U
          rw [opNorm_unitary (U := ⟨(U : HilbertOperator R).conjTranspose, hUstar⟩)]
      _ = opNorm A * opNorm B * Matrix.traceNorm X := by
          ring

lemma inducedTraceNorm_twoSidedMul_control_of_holder {R : Register}
    [Nonempty R.Index] (hholder : TraceNormHolderControl R) :
    SuperOpTwoSidedMulNormControl (R := R) inducedTraceNorm opNorm :=
  inducedTraceNorm_twoSidedMul_control_of_matrix_control
    (traceNormTwoSidedMulControl_of_holder hholder)

lemma traceNormTwoSidedMulControl_operatorNorm {R : Register} [Nonempty R.Index] :
    TraceNormTwoSidedMulControl R :=
  traceNormTwoSidedMulControl_of_holder traceNormHolderControl_of_operatorNorm

lemma inducedTraceNorm_twoSidedMul_control_operatorNorm {R : Register}
    [Nonempty R.Index] :
    SuperOpTwoSidedMulNormControl (R := R) inducedTraceNorm opNorm :=
  inducedTraceNorm_twoSidedMul_control_of_holder traceNormHolderControl_of_operatorNorm

private lemma conjugationSuperOp_traceNorm_nonexpansive {R : Register}
    (U : HilbertOperator R) (hU : U ∈ Matrix.unitaryGroup R.Index ℂ) :
    TraceNormNonexpansive (conjugationSuperOp U) := by
  intro X
  let U' : Matrix.unitaryGroup R.Index ℂ := ⟨U, hU⟩
  simpa [TraceNormNonexpansive, conjugationSuperOp_apply, U', Matrix.mul_assoc,
    Matrix.star_eq_conjTranspose] using
    le_of_eq (Matrix.traceNorm_unitary_conj (A := X) (U := U'))

/-- Ideal one-step evolution as a superoperator, `X ↦ U X Uᴴ`. -/
def idealStepSuperOp {R : Register} (H : HilbertOperator R) (τ : ℝ) : SuperOp R :=
  conjugationSuperOp (timeEvolutionOp H τ)

@[simp]
lemma idealStepSuperOp_apply {R : Register} (H X : HilbertOperator R) (τ : ℝ) :
    idealStepSuperOp H τ X =
      timeEvolutionOp H τ * (X * star (timeEvolutionOp H τ)) := by
  rfl

lemma idealStepSuperOp_traceNorm_nonexpansive {R : Register}
    (H : HilbertOperator R) (τ : ℝ) (hH : H.IsHermitian) :
    TraceNormNonexpansive (idealStepSuperOp H τ) :=
  conjugationSuperOp_traceNorm_nonexpansive (timeEvolutionOp H τ)
    (timeEvolutionOp_mem_unitaryGroup hH τ)

lemma idealStepSuperOp_inducedTraceNorm_le_one {R : Register}
    (H : HilbertOperator R) (τ : ℝ) (hH : H.IsHermitian) :
    inducedTraceNorm (idealStepSuperOp H τ) ≤ 1 :=
  inducedTraceNorm_le_one_of_traceNorm_nonexpansive
    (idealStepSuperOp_traceNorm_nonexpansive H τ hH)

lemma idealStepSuperOp_left_inducedTraceNorm_nonexpansive {R : Register}
    (H : HilbertOperator R) (τ : ℝ) (hH : H.IsHermitian) :
    SuperOpLeftNonexpansive inducedTraceNorm (idealStepSuperOp H τ) :=
  traceNormNonexpansive_left_inducedTraceNorm_nonexpansive
    (idealStepSuperOp_traceNorm_nonexpansive H τ hH)

lemma idealStepSuperOp_right_inducedTraceNorm_nonexpansive {R : Register}
    (H : HilbertOperator R) (τ : ℝ) (hH : H.IsHermitian) :
    SuperOpRightNonexpansive inducedTraceNorm (idealStepSuperOp H τ) :=
  traceNormNonexpansive_right_inducedTraceNorm_nonexpansive
    (idealStepSuperOp_traceNorm_nonexpansive H τ hH)

@[simp]
lemma idealStepSuperOp_zero {R : Register} (H : HilbertOperator R) :
    idealStepSuperOp H 0 = LinearMap.id := by
  ext X
  simp [idealStepSuperOp, conjugationSuperOp, timeEvolutionOp]

/-- The second-order remainder of one unitary-conjugation step. -/
def unitaryStepRemainderSuperOp {R : Register} (H : HilbertOperator R) (τ : ℝ) : SuperOp R :=
  idealStepSuperOp H τ - firstOrderSuperOp (liouvillianSuperOp H) τ

@[simp]
lemma unitaryStepRemainderSuperOp_apply {R : Register}
    (H X : HilbertOperator R) (τ : ℝ) :
    unitaryStepRemainderSuperOp H τ X =
      idealStepSuperOp H τ X - firstOrderSuperOp (liouvillianSuperOp H) τ X := by
  rfl

/-- Pointwise algebraic decomposition of a one-step unitary-conjugation
remainder into left and right exponential remainders plus the quadratic
cross term. -/
lemma unitaryStepRemainderSuperOp_apply_decompose {R : Register}
    (H X : HilbertOperator R) (τ : ℝ) :
    let U : HilbertOperator R := timeEvolutionOp H τ
    let A : HilbertOperator R := (-((τ : ℂ) * Complex.I)) • H
    let leftR : HilbertOperator R := U - 1 - A
    let rightR : HilbertOperator R := star U - 1 + A
    unitaryStepRemainderSuperOp H τ X =
      leftR * (X * star U) + (1 + A) * (X * rightR) - A * (X * A) := by
  dsimp
  let U : HilbertOperator R := timeEvolutionOp H τ
  let A : HilbertOperator R := (-((τ : ℂ) * Complex.I)) • H
  have hgen : (τ : ℂ) • liouvillianSuperOp H X = A * X - X * A := by
    ext i j
    simp [A, liouvillianSuperOp, commutatorSuperOp, leftMulSuperOp,
      rightMulSuperOp, Matrix.sub_apply, Matrix.smul_apply, smul_sub,
      neg_smul]
    ring
  calc
    unitaryStepRemainderSuperOp H τ X
        = U * X * star U - (X + (A * X - X * A)) := by
          rw [unitaryStepRemainderSuperOp_apply, idealStepSuperOp_apply,
            firstOrderSuperOp_apply, hgen]
          simp [U, mul_assoc]
    _ = (U - 1 - A) * (X * star U) + (1 + A) * (X * (star U - 1 + A)) -
          A * (X * A) := by
      simpa [U, A] using
        noncomm_conj_first_order_remainder_decompose U (star U) A X

/-- Superoperator-level version of
`unitaryStepRemainderSuperOp_apply_decompose`. -/
lemma unitaryStepRemainderSuperOp_eq_twoSidedMul {R : Register}
    (H : HilbertOperator R) (τ : ℝ) :
    let U : HilbertOperator R := timeEvolutionOp H τ
    let A : HilbertOperator R := (-((τ : ℂ) * Complex.I)) • H
    let leftR : HilbertOperator R := U - 1 - A
    let rightR : HilbertOperator R := star U - 1 + A
    unitaryStepRemainderSuperOp H τ =
      twoSidedMulSuperOp leftR (star U) +
        twoSidedMulSuperOp (1 + A) rightR -
          twoSidedMulSuperOp A A := by
  ext X
  dsimp
  rw [unitaryStepRemainderSuperOp_apply_decompose]
  simp [twoSidedMulSuperOp, sub_eq_add_neg]

/-- Abstract norm bound for a unitary-conjugation first-order remainder from
two-sided multiplication control. -/
lemma unitaryStepRemainderSuperOp_norm_le_twoSided_budget {R : Register}
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (matrixNorm : HilbertOperator R → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (hmul : SuperOpTwoSidedMulNormControl superOpNorm matrixNorm)
    (H : HilbertOperator R) (τ : ℝ)
    (leftBudget rightBudget unitaryBudget oneABudget aBudget : ℝ)
    (hleft :
      let U : HilbertOperator R := timeEvolutionOp H τ
      let A : HilbertOperator R := (-((τ : ℂ) * Complex.I)) • H
      matrixNorm (U - 1 - A) ≤ leftBudget)
    (hright :
      let U : HilbertOperator R := timeEvolutionOp H τ
      let A : HilbertOperator R := (-((τ : ℂ) * Complex.I)) • H
      matrixNorm (star U - 1 + A) ≤ rightBudget)
    (hunit :
      let U : HilbertOperator R := timeEvolutionOp H τ
      matrixNorm (star U) ≤ unitaryBudget)
    (honeA :
      let A : HilbertOperator R := (-((τ : ℂ) * Complex.I)) • H
      matrixNorm (1 + A) ≤ oneABudget)
    (hA :
      let A : HilbertOperator R := (-((τ : ℂ) * Complex.I)) • H
      matrixNorm A ≤ aBudget)
    (hleftBudget : 0 ≤ leftBudget)
    (honeABudget : 0 ≤ oneABudget)
    (haBudget : 0 ≤ aBudget) :
    superOpNorm (unitaryStepRemainderSuperOp H τ)
      ≤ leftBudget * unitaryBudget + oneABudget * rightBudget + aBudget * aBudget := by
  let U : HilbertOperator R := timeEvolutionOp H τ
  let A : HilbertOperator R := (-((τ : ℂ) * Complex.I)) • H
  let leftR : HilbertOperator R := U - 1 - A
  let rightR : HilbertOperator R := star U - 1 + A
  let Φ : SuperOp R := twoSidedMulSuperOp leftR (star U)
  let Ψ : SuperOp R := twoSidedMulSuperOp (1 + A) rightR
  let Ω : SuperOp R := twoSidedMulSuperOp A A
  have hΦ : superOpNorm Φ ≤ leftBudget * unitaryBudget := by
    calc
      superOpNorm Φ ≤ matrixNorm leftR * matrixNorm (star U) := by
        exact hmul.norm_two_sided leftR (star U)
      _ ≤ leftBudget * unitaryBudget := by
        exact mul_le_mul hleft hunit (hmul.norm_nonneg (star U)) hleftBudget
  have hΨ : superOpNorm Ψ ≤ oneABudget * rightBudget := by
    calc
      superOpNorm Ψ ≤ matrixNorm (1 + A) * matrixNorm rightR := by
        exact hmul.norm_two_sided (1 + A) rightR
      _ ≤ oneABudget * rightBudget := by
        exact mul_le_mul honeA hright (hmul.norm_nonneg rightR) honeABudget
  have hΩ : superOpNorm Ω ≤ aBudget * aBudget := by
    calc
      superOpNorm Ω ≤ matrixNorm A * matrixNorm A := by
        exact hmul.norm_two_sided A A
      _ ≤ aBudget * aBudget := by
        exact mul_le_mul hA hA (hmul.norm_nonneg A) haBudget
  calc
    superOpNorm (unitaryStepRemainderSuperOp H τ)
        = superOpNorm (Φ + Ψ - Ω) := by
          rw [unitaryStepRemainderSuperOp_eq_twoSidedMul H τ]
    _ ≤ superOpNorm (Φ + Ψ) + superOpNorm Ω := hnorm.norm_sub_le (Φ + Ψ) Ω
    _ ≤ (superOpNorm Φ + superOpNorm Ψ) + superOpNorm Ω := by
      simpa [add_assoc, add_comm, add_left_comm] using
        add_le_add_right (hnorm.norm_add_le Φ Ψ) (superOpNorm Ω)
    _ ≤ leftBudget * unitaryBudget + oneABudget * rightBudget + aBudget * aBudget := by
      linarith

/-- Packaged two-sided multiplication budget for a single unitary-conjugation
first-order remainder. -/
structure UnitaryStepRemainderNormBudget {R : Register}
    (matrixNorm : HilbertOperator R → ℝ)
    (H : HilbertOperator R) (τ budget : ℝ) : Type where
  /-- Budget for the left second-order exponential remainder. -/
  leftBudget : ℝ
  /-- Budget for the right adjoint second-order exponential remainder. -/
  rightBudget : ℝ
  /-- Budget for the adjoint time-evolution factor. -/
  unitaryBudget : ℝ
  /-- Budget for the first-order factor `1 + A`. -/
  oneABudget : ℝ
  /-- Budget for the generator `A = -i τ H`. -/
  aBudget : ℝ
  left_bound :
    let U : HilbertOperator R := timeEvolutionOp H τ
    let A : HilbertOperator R := (-((τ : ℂ) * Complex.I)) • H
    matrixNorm (U - 1 - A) ≤ leftBudget
  right_bound :
    let U : HilbertOperator R := timeEvolutionOp H τ
    let A : HilbertOperator R := (-((τ : ℂ) * Complex.I)) • H
    matrixNorm (star U - 1 + A) ≤ rightBudget
  unitary_bound :
    let U : HilbertOperator R := timeEvolutionOp H τ
    matrixNorm (star U) ≤ unitaryBudget
  one_add_generator_bound :
    let A : HilbertOperator R := (-((τ : ℂ) * Complex.I)) • H
    matrixNorm (1 + A) ≤ oneABudget
  generator_bound :
    let A : HilbertOperator R := (-((τ : ℂ) * Complex.I)) • H
    matrixNorm A ≤ aBudget
  leftBudget_nonneg : 0 ≤ leftBudget
  oneABudget_nonneg : 0 ≤ oneABudget
  aBudget_nonneg : 0 ≤ aBudget
  total_bound :
    leftBudget * unitaryBudget + oneABudget * rightBudget + aBudget * aBudget ≤ budget

namespace UnitaryStepRemainderNormBudget

lemma norm_le {R : Register}
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (matrixNorm : HilbertOperator R → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (hmul : SuperOpTwoSidedMulNormControl superOpNorm matrixNorm)
    (H : HilbertOperator R) (τ budget : ℝ)
    (hbudget : UnitaryStepRemainderNormBudget matrixNorm H τ budget) :
    superOpNorm (unitaryStepRemainderSuperOp H τ) ≤ budget := by
  exact le_trans
    (unitaryStepRemainderSuperOp_norm_le_twoSided_budget
      (superOpNorm := superOpNorm) (scalarNorm := scalarNorm)
      (matrixNorm := matrixNorm) (hnorm := hnorm) (hmul := hmul)
      (H := H) (τ := τ)
      (leftBudget := hbudget.leftBudget)
      (rightBudget := hbudget.rightBudget)
      (unitaryBudget := hbudget.unitaryBudget)
      (oneABudget := hbudget.oneABudget)
      (aBudget := hbudget.aBudget)
      hbudget.left_bound hbudget.right_bound hbudget.unitary_bound
      hbudget.one_add_generator_bound hbudget.generator_bound
      hbudget.leftBudget_nonneg hbudget.oneABudget_nonneg
      hbudget.aBudget_nonneg)
    hbudget.total_bound

end UnitaryStepRemainderNormBudget

@[simp]
lemma unitaryStepRemainderSuperOp_zero {R : Register} (H : HilbertOperator R) :
    unitaryStepRemainderSuperOp H 0 = 0 := by
  rw [unitaryStepRemainderSuperOp, idealStepSuperOp_zero, firstOrderSuperOp_zero]
  simp

/-- A superoperator is explicitly a quadratic remainder in the step size `τ`. -/
def IsQuadraticRemainder {R : Register} (τ : ℝ) (Φ : SuperOp R) : Prop :=
  ∃ Ψ : SuperOp R, Φ = ((τ : ℂ) ^ 2) • Ψ

namespace IsQuadraticRemainder

lemma zero {R : Register} (τ : ℝ) : IsQuadraticRemainder τ (0 : SuperOp R) := by
  use 0
  simp

lemma add {R : Register} {τ : ℝ} {Φ Ψ : SuperOp R}
    (hΦ : IsQuadraticRemainder τ Φ) (hΨ : IsQuadraticRemainder τ Ψ) :
    IsQuadraticRemainder τ (Φ + Ψ) := by
  rcases hΦ with ⟨Φ', rfl⟩
  rcases hΨ with ⟨Ψ', rfl⟩
  use Φ' + Ψ'
  simp [smul_add]

lemma neg {R : Register} {τ : ℝ} {Φ : SuperOp R}
    (hΦ : IsQuadraticRemainder τ Φ) :
    IsQuadraticRemainder τ (-Φ) := by
  rcases hΦ with ⟨Φ', rfl⟩
  use -Φ'
  simp

lemma sub {R : Register} {τ : ℝ} {Φ Ψ : SuperOp R}
    (hΦ : IsQuadraticRemainder τ Φ) (hΨ : IsQuadraticRemainder τ Ψ) :
    IsQuadraticRemainder τ (Φ - Ψ) := by
  simpa [sub_eq_add_neg] using hΦ.add hΨ.neg

lemma smul {R : Register} {τ : ℝ} (c : ℂ) {Φ : SuperOp R}
    (hΦ : IsQuadraticRemainder τ Φ) :
    IsQuadraticRemainder τ (c • Φ) := by
  rcases hΦ with ⟨Φ', rfl⟩
  use c • Φ'
  ext X
  simp [smul_smul, mul_comm, mul_assoc]

lemma sum {R : Register} {τ : ℝ} {ι : Type} [Fintype ι] (Φ : ι → SuperOp R)
    (hΦ : ∀ j, IsQuadraticRemainder τ (Φ j)) :
    IsQuadraticRemainder τ (∑ j, Φ j) := by
  classical
  choose Ψ hΨ using hΦ
  use ∑ j, Ψ j
  ext X
  simp [hΨ, Finset.smul_sum]

lemma comp_left {R : Register} {τ : ℝ} (pre : SuperOp R) {Φ : SuperOp R}
    (hΦ : IsQuadraticRemainder τ Φ) :
    IsQuadraticRemainder τ (superOpComp pre Φ) := by
  rcases hΦ with ⟨Φ', rfl⟩
  use superOpComp pre Φ'
  ext X
  simp [superOpComp]

lemma comp_right {R : Register} {τ : ℝ} (post : SuperOp R) {Φ : SuperOp R}
    (hΦ : IsQuadraticRemainder τ Φ) :
    IsQuadraticRemainder τ (superOpComp Φ post) := by
  rcases hΦ with ⟨Φ', rfl⟩
  use superOpComp Φ' post
  rfl

lemma comp_left_right {R : Register} {τ : ℝ} (pre post : SuperOp R) {Φ : SuperOp R}
    (hΦ : IsQuadraticRemainder τ Φ) :
    IsQuadraticRemainder τ (superOpComp pre (superOpComp Φ post)) :=
  (hΦ.comp_right post).comp_left pre

end IsQuadraticRemainder

/-- Norm budget for an explicitly quadratic superoperator remainder.

The structure keeps the analytic estimate on the normalized remainder `Ψ`
separate from the algebraic fact that the error is `τ^2 • Ψ`. -/
structure QuadraticRemainderNormBudget {R : Register}
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (τ : ℝ) (Λ : ℝ) (Φ : SuperOp R) : Prop where
  quadratic : IsQuadraticRemainder τ Φ
  remainder_bound : ∀ Ψ, Φ = ((τ : ℂ) ^ 2) • Ψ → superOpNorm Ψ ≤ Λ
  scalar_quadratic_nonneg : 0 ≤ scalarNorm ((τ : ℂ) ^ 2)

namespace QuadraticRemainderNormBudget

/-- A quadratic-remainder norm budget gives the expected `τ^2`-scaled norm
bound, expressed through the abstract scalar norm. -/
lemma norm_le {R : Register}
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (τ Λ : ℝ) (Φ : SuperOp R)
    (hbudget : QuadraticRemainderNormBudget superOpNorm scalarNorm τ Λ Φ) :
    superOpNorm Φ ≤ scalarNorm ((τ : ℂ) ^ 2) * Λ := by
  rcases hbudget.quadratic with ⟨Ψ, hΨ⟩
  calc
    superOpNorm Φ = superOpNorm (((τ : ℂ) ^ 2) • Ψ) := by
      rw [hΨ]
    _ = scalarNorm ((τ : ℂ) ^ 2) * superOpNorm Ψ := by
      rw [hnorm.norm_smul]
    _ ≤ scalarNorm ((τ : ℂ) ^ 2) * Λ :=
      mul_le_mul_of_nonneg_left
        (hbudget.remainder_bound Ψ hΨ)
        hbudget.scalar_quadratic_nonneg

end QuadraticRemainderNormBudget

/-- Weighted Hamiltonian sum used by the qDRIFT interface. -/
def weightedHamiltonianOp {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) : HilbertOperator R :=
  ∑ j, (p j : ℂ) • H j

/-- A real probability-weighted Hamiltonian remains Hermitian. -/
lemma weightedHamiltonianOp_isHermitian {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ)
    (hH : ∀ j, (H j).IsHermitian) :
    (weightedHamiltonianOp H p).IsHermitian := by
  classical
  unfold weightedHamiltonianOp
  have hermitian_term (j : ι) : ((p j : ℂ) • H j).IsHermitian := by
    simpa using (hH j).smul (by simp : starRingEnd ℂ (p j : ℂ) = (p j : ℂ))
  induction (Finset.univ : Finset ι) using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hermitian_term a).add ih

/-- A convex real weighting preserves a common operator-norm upper bound. -/
lemma opNorm_weightedHamiltonianOp_le {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (Λ : ℝ)
    (hprob : QDriftProbabilityWeights p)
    (hHnorm : ∀ j, opNorm (H j) ≤ Λ) :
    opNorm (weightedHamiltonianOp H p) ≤ Λ := by
  classical
  calc
    opNorm (weightedHamiltonianOp H p)
        ≤ ∑ j, opNorm ((p j : ℂ) • H j) := by
          simpa [weightedHamiltonianOp] using opNorm_sum_le
            (fun j => (p j : ℂ) • H j)
    _ = ∑ j, p j * opNorm (H j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [opNorm_smul]
      simp [Complex.norm_real, abs_of_nonneg (hprob.nonneg j)]
    _ ≤ ∑ j, p j * Λ := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hHnorm j) (hprob.nonneg j)
    _ = Λ := by rw [← Finset.sum_mul, hprob.sum_eq_one, one_mul]

lemma qdrift_weightedHamiltonian_scale {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (h : ι → ℝ)
    (h_lambda_ne_zero : qdriftLambda h ≠ 0) :
    (qdriftLambda h : ℂ) • weightedHamiltonianOp H (qdriftProbabilities h)
      = weightedHamiltonianOp H h := by
  rw [weightedHamiltonianOp, weightedHamiltonianOp, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [qdriftProbabilities, smul_smul]
  congr 1
  norm_cast
  field_simp [h_lambda_ne_zero]

/-- qDRIFT one-step map as an explicit weighted sum of conjugation superoperators. -/
def qdriftStepSuperOp {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ) : SuperOp R :=
  ∑ j, (p j : ℂ) • idealStepSuperOp (H j) τ

lemma qdriftStepSuperOp_traceNorm_nonexpansive {R : Register}
    {ι : Type} [Fintype ι] (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hH : ∀ j, (H j).IsHermitian) (hp : QDriftProbabilityWeights p) :
    TraceNormNonexpansive (qdriftStepSuperOp H p τ) := by
  intro X
  rw [qdriftStepSuperOp]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  calc
    Matrix.traceNorm (∑ j, (p j : ℂ) • idealStepSuperOp (H j) τ X)
        ≤ ∑ j, Matrix.traceNorm ((p j : ℂ) • idealStepSuperOp (H j) τ X) :=
      Matrix.traceNorm_sum_le _
    _ = ∑ j, p j * Matrix.traceNorm (idealStepSuperOp (H j) τ X) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.traceNorm_smul]
      simp [Complex.norm_real, abs_of_nonneg (hp.nonneg j)]
    _ ≤ ∑ j, p j * Matrix.traceNorm X := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (idealStepSuperOp_traceNorm_nonexpansive (H j) τ (hH j) X)
        (hp.nonneg j)
    _ = Matrix.traceNorm X := by
      rw [← Finset.sum_mul, hp.sum_eq_one, one_mul]

lemma qdriftStepSuperOp_inducedTraceNorm_le_one {R : Register}
    {ι : Type} [Fintype ι] (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hH : ∀ j, (H j).IsHermitian) (hp : QDriftProbabilityWeights p) :
    inducedTraceNorm (qdriftStepSuperOp H p τ) ≤ 1 :=
  inducedTraceNorm_le_one_of_traceNorm_nonexpansive
    (qdriftStepSuperOp_traceNorm_nonexpansive H p τ hH hp)

lemma qdriftStepSuperOp_left_inducedTraceNorm_nonexpansive {R : Register}
    {ι : Type} [Fintype ι] (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hH : ∀ j, (H j).IsHermitian) (hp : QDriftProbabilityWeights p) :
    SuperOpLeftNonexpansive inducedTraceNorm (qdriftStepSuperOp H p τ) :=
  traceNormNonexpansive_left_inducedTraceNorm_nonexpansive
    (qdriftStepSuperOp_traceNorm_nonexpansive H p τ hH hp)

lemma qdriftStepSuperOp_right_inducedTraceNorm_nonexpansive {R : Register}
    {ι : Type} [Fintype ι] (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hH : ∀ j, (H j).IsHermitian) (hp : QDriftProbabilityWeights p) :
    SuperOpRightNonexpansive inducedTraceNorm (qdriftStepSuperOp H p τ) :=
  traceNormNonexpansive_right_inducedTraceNorm_nonexpansive
    (qdriftStepSuperOp_traceNorm_nonexpansive H p τ hH hp)

/-- The ideal one-step map generated by the weighted qDRIFT Hamiltonian. -/
def qdriftIdealStepSuperOp {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ) : SuperOp R :=
  idealStepSuperOp (weightedHamiltonianOp H p) τ

/-- Campbell's averaged qDRIFT channel using coefficient weights `h`. -/
def qdriftAverageChannel {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (h : ι → ℝ) (t : ℝ) (steps : ℕ) : SuperOp R :=
  qdriftStepSuperOp H (qdriftProbabilities h) (qdriftStepTime h t steps)

/-- The target segment channel paired with `qdriftAverageChannel`. -/
def qdriftTargetSegmentChannel {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (h : ι → ℝ) (t : ℝ) (steps : ℕ) : SuperOp R :=
  qdriftIdealStepSuperOp H (qdriftProbabilities h) (qdriftStepTime h t steps)

/-- Campbell's averaged qDRIFT channel is nonexpansive for the matrix trace norm. -/
lemma qdriftAverageChannel_traceNorm_nonexpansive {R : Register}
    {ι : Type} [Fintype ι] (H : ι → HilbertOperator R) (h : ι → ℝ)
    (t : ℝ) (steps : ℕ)
    (h_nonneg : ∀ j, 0 ≤ h j) (h_lambda_ne_zero : qdriftLambda h ≠ 0)
    (hH : ∀ j, (H j).IsHermitian) :
    TraceNormNonexpansive (qdriftAverageChannel H h t steps) := by
  have hprob : QDriftProbabilityWeights (qdriftProbabilities h) :=
    qdriftProbabilityWeights h h_nonneg h_lambda_ne_zero
  simpa [qdriftAverageChannel] using
    qdriftStepSuperOp_traceNorm_nonexpansive
      H (qdriftProbabilities h) (qdriftStepTime h t steps) hH hprob

/-- The qDRIFT target segment channel is nonexpansive for the matrix trace norm. -/
lemma qdriftTargetSegmentChannel_traceNorm_nonexpansive {R : Register}
    {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (h : ι → ℝ) (t : ℝ) (steps : ℕ)
    (hH : ∀ j, (H j).IsHermitian) :
    TraceNormNonexpansive (qdriftTargetSegmentChannel H h t steps) := by
  exact conjugationSuperOp_traceNorm_nonexpansive
    (timeEvolutionOp (weightedHamiltonianOp H (qdriftProbabilities h))
      (qdriftStepTime h t steps))
    (timeEvolutionOp_mem_unitaryGroup
      (weightedHamiltonianOp_isHermitian H (qdriftProbabilities h) hH)
      (qdriftStepTime h t steps))

/-- Total evolution time for the normalized Hamiltonian underlying qDRIFT. -/
def qdriftAverageTotalTime {ι : Type} [Fintype ι] (h : ι → ℝ) (t : ℝ) : ℝ :=
  t * qdriftLambda h

/-- Difference between repeated target and averaged qDRIFT channels. -/
def qdriftAveragePowerError {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (h : ι → ℝ) (t : ℝ) (steps : ℕ) :
    SuperOp R :=
  superOpPower (qdriftTargetSegmentChannel H h t steps) steps
    - superOpPower (qdriftAverageChannel H h t steps) steps

/-- The raw one-step qDRIFT superoperator error. -/
def qdriftStepErrorSuperOp {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ) : SuperOp R :=
  qdriftStepSuperOp H p τ - qdriftIdealStepSuperOp H p τ

/-- A one-step qDRIFT error propagated by pre- and post-composition maps. -/
def qdriftPropagatedStepError {R : Register} {ι : Type} [Fintype ι]
    (pre post : SuperOp R) (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ) :
    SuperOp R :=
  superOpComp pre (superOpComp (qdriftStepErrorSuperOp H p τ) post)

/-- The first-order generator for the weighted qDRIFT Hamiltonian. -/
def qdriftIdealGeneratorSuperOp {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) : SuperOp R :=
  liouvillianSuperOp (weightedHamiltonianOp H p)

/-- The weighted average of the per-term qDRIFT first-order generators. -/
def qdriftWeightedGeneratorSuperOp {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) : SuperOp R :=
  ∑ j, (p j : ℂ) • liouvillianSuperOp (H j)

/-- The ideal first-order model generated by the weighted Hamiltonian. -/
def qdriftIdealFirstOrderSuperOp {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ) : SuperOp R :=
  firstOrderSuperOp (qdriftIdealGeneratorSuperOp H p) τ

/-- The qDRIFT weighted first-order model. -/
def qdriftWeightedFirstOrderSuperOp {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ) : SuperOp R :=
  firstOrderSuperOp (qdriftWeightedGeneratorSuperOp H p) τ

/-- The ideal one-step remainder after subtracting the shared first-order model. -/
def qdriftIdealRemainderSuperOp {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ) : SuperOp R :=
  qdriftIdealStepSuperOp H p τ - qdriftIdealFirstOrderSuperOp H p τ

/-- The qDRIFT weighted one-step remainder after subtracting its first-order model. -/
def qdriftWeightedRemainderSuperOp {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ) : SuperOp R :=
  qdriftStepSuperOp H p τ - qdriftWeightedFirstOrderSuperOp H p τ

/-- Abstract qDRIFT one-step remainder bounds.

This structure records only the analytic estimates needed after the algebraic
first-order cancellation has been formalized. -/
structure QDriftOneStepRemainderBounds {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (termBound idealBudget : ℝ) : Prop where
  term_bound : ∀ j, superOpNorm (unitaryStepRemainderSuperOp (H j) τ) ≤ termBound
  scalar_weights_bound : ∑ j, scalarNorm (p j : ℂ) ≤ 1
  scalar_nonneg : ∀ j, 0 ≤ scalarNorm (p j : ℂ)
  term_bound_nonneg : 0 ≤ termBound
  ideal_bound : superOpNorm (qdriftIdealRemainderSuperOp H p τ) ≤ idealBudget

/-- Packaged quadratic qDRIFT one-step remainder bounds. -/
structure QDriftOneStepQuadraticBounds {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (termBound idealBudget constant : ℝ) : Prop where
  remainder_bounds :
    QDriftOneStepRemainderBounds superOpNorm scalarNorm H p τ termBound idealBudget
  quadratic_budget : termBound + idealBudget ≤ constant * τ ^ 2

/-- Build qDRIFT one-step remainder bounds from sampled and ideal
unitary-step two-sided multiplication budgets. -/
lemma qdriftOneStepRemainderBounds_of_unitaryStepBudgets
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (matrixNorm : HilbertOperator R → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (hmul : SuperOpTwoSidedMulNormControl superOpNorm matrixNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (termBound idealBudget : ℝ)
    (hterms : ∀ j, UnitaryStepRemainderNormBudget matrixNorm (H j) τ termBound)
    (hideal :
      UnitaryStepRemainderNormBudget matrixNorm (weightedHamiltonianOp H p) τ
        idealBudget)
    (hweights : ∑ j, scalarNorm (p j : ℂ) ≤ 1)
    (hscalar_nonneg : ∀ j, 0 ≤ scalarNorm (p j : ℂ))
    (hterm_nonneg : 0 ≤ termBound) :
    QDriftOneStepRemainderBounds superOpNorm scalarNorm H p τ
      termBound idealBudget where
  term_bound := by
    intro j
    exact UnitaryStepRemainderNormBudget.norm_le
      (superOpNorm := superOpNorm) (scalarNorm := scalarNorm)
      (matrixNorm := matrixNorm) (hnorm := hnorm) (hmul := hmul)
      (H := H j) (τ := τ) (budget := termBound) (hterms j)
  scalar_weights_bound := hweights
  scalar_nonneg := hscalar_nonneg
  term_bound_nonneg := hterm_nonneg
  ideal_bound :=
    UnitaryStepRemainderNormBudget.norm_le
      (superOpNorm := superOpNorm) (scalarNorm := scalarNorm)
      (matrixNorm := matrixNorm) (hnorm := hnorm) (hmul := hmul)
      (H := weightedHamiltonianOp H p) (τ := τ) (budget := idealBudget)
      hideal

/-- Build qDRIFT quadratic one-step bounds from sampled and ideal
unitary-step two-sided multiplication budgets. -/
lemma qdriftOneStepQuadraticBounds_of_unitaryStepBudgets
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (matrixNorm : HilbertOperator R → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (hmul : SuperOpTwoSidedMulNormControl superOpNorm matrixNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (termBound idealBudget constant : ℝ)
    (hterms : ∀ j, UnitaryStepRemainderNormBudget matrixNorm (H j) τ termBound)
    (hideal :
      UnitaryStepRemainderNormBudget matrixNorm (weightedHamiltonianOp H p) τ
        idealBudget)
    (hweights : ∑ j, scalarNorm (p j : ℂ) ≤ 1)
    (hscalar_nonneg : ∀ j, 0 ≤ scalarNorm (p j : ℂ))
    (hterm_nonneg : 0 ≤ termBound)
    (hquadratic : termBound + idealBudget ≤ constant * τ ^ 2) :
    QDriftOneStepQuadraticBounds superOpNorm scalarNorm H p τ
      termBound idealBudget constant where
  remainder_bounds :=
    qdriftOneStepRemainderBounds_of_unitaryStepBudgets
      (superOpNorm := superOpNorm) (scalarNorm := scalarNorm)
      (matrixNorm := matrixNorm) (hnorm := hnorm) (hmul := hmul)
      (H := H) (p := p) (τ := τ)
      (termBound := termBound) (idealBudget := idealBudget)
      hterms hideal hweights hscalar_nonneg hterm_nonneg
  quadratic_budget := hquadratic

@[simp]
lemma qdriftStepSuperOp_apply {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ) (X : HilbertOperator R) :
    qdriftStepSuperOp H p τ X =
      ∑ j, (p j : ℂ) • idealStepSuperOp (H j) τ X := by
  simp [qdriftStepSuperOp]

@[simp]
lemma qdriftIdealStepSuperOp_apply {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ) (X : HilbertOperator R) :
    qdriftIdealStepSuperOp H p τ X =
      idealStepSuperOp (weightedHamiltonianOp H p) τ X := by
  rfl

@[simp]
lemma qdriftIdealStepSuperOp_zero {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) :
    qdriftIdealStepSuperOp H p 0 = LinearMap.id := by
  simp [qdriftIdealStepSuperOp]

lemma qdriftStepSuperOp_zero_of_sum_eq_one {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ)
    (hp : ∑ j, (p j : ℂ) = 1) :
    qdriftStepSuperOp H p 0 = LinearMap.id := by
  ext X
  simp [qdriftStepSuperOp, hp, ← Finset.sum_smul]

lemma qdriftStepErrorSuperOp_zero_of_sum_eq_one {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ)
    (hp : ∑ j, (p j : ℂ) = 1) :
    qdriftStepErrorSuperOp H p 0 = 0 := by
  rw [qdriftStepErrorSuperOp, qdriftStepSuperOp_zero_of_sum_eq_one H p hp,
    qdriftIdealStepSuperOp_zero]
  simp

@[simp]
lemma qdriftIdealFirstOrderSuperOp_zero {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) :
    qdriftIdealFirstOrderSuperOp H p 0 = LinearMap.id := by
  simp [qdriftIdealFirstOrderSuperOp]

@[simp]
lemma qdriftWeightedFirstOrderSuperOp_zero {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) :
    qdriftWeightedFirstOrderSuperOp H p 0 = LinearMap.id := by
  simp [qdriftWeightedFirstOrderSuperOp]

@[simp]
lemma qdriftStepErrorSuperOp_apply {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ) (X : HilbertOperator R) :
    qdriftStepErrorSuperOp H p τ X =
      qdriftStepSuperOp H p τ X - qdriftIdealStepSuperOp H p τ X := by
  rfl

@[simp]
lemma qdriftPropagatedStepError_apply {R : Register} {ι : Type} [Fintype ι]
    (pre post : SuperOp R) (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (X : HilbertOperator R) :
    qdriftPropagatedStepError pre post H p τ X =
      pre (qdriftStepErrorSuperOp H p τ (post X)) := by
  rfl

lemma qdriftPropagatedStepError_norm_le {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ)
    (pre post : SuperOp R) (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hpre : SuperOpLeftNonexpansive superOpNorm pre)
    (hpost : SuperOpRightNonexpansive superOpNorm post) :
    superOpNorm (qdriftPropagatedStepError pre post H p τ)
      ≤ superOpNorm (qdriftStepErrorSuperOp H p τ) :=
  le_trans
    (hpre.norm_comp_le (superOpComp (qdriftStepErrorSuperOp H p τ) post))
    (hpost.norm_comp_le (qdriftStepErrorSuperOp H p τ))

/-- Propagating a quadratic one-step error on the left and right preserves the
explicit quadratic-remainder shape. -/
lemma qdriftPropagatedStepError_isQuadraticRemainder
    {R : Register} {ι : Type} [Fintype ι]
    (pre post : SuperOp R) (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hstep : IsQuadraticRemainder τ (qdriftStepErrorSuperOp H p τ)) :
    IsQuadraticRemainder τ (qdriftPropagatedStepError pre post H p τ) := by
  rw [qdriftPropagatedStepError]
  exact IsQuadraticRemainder.comp_left_right pre post hstep

@[simp]
lemma qdriftIdealGeneratorSuperOp_apply {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (X : HilbertOperator R) :
    qdriftIdealGeneratorSuperOp H p X =
      liouvillianSuperOp (weightedHamiltonianOp H p) X := by
  rfl

@[simp]
lemma qdriftWeightedGeneratorSuperOp_apply {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (X : HilbertOperator R) :
    qdriftWeightedGeneratorSuperOp H p X =
      ∑ j, (p j : ℂ) • liouvillianSuperOp (H j) X := by
  simp [qdriftWeightedGeneratorSuperOp]

@[simp]
lemma qdriftIdealFirstOrderSuperOp_apply {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ) (X : HilbertOperator R) :
    qdriftIdealFirstOrderSuperOp H p τ X =
      X + (τ : ℂ) • qdriftIdealGeneratorSuperOp H p X := by
  rfl

@[simp]
lemma qdriftWeightedFirstOrderSuperOp_apply {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ) (X : HilbertOperator R) :
    qdriftWeightedFirstOrderSuperOp H p τ X =
      X + (τ : ℂ) • qdriftWeightedGeneratorSuperOp H p X := by
  rfl

@[simp]
lemma qdriftIdealRemainderSuperOp_apply {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ) (X : HilbertOperator R) :
    qdriftIdealRemainderSuperOp H p τ X =
      qdriftIdealStepSuperOp H p τ X - qdriftIdealFirstOrderSuperOp H p τ X := by
  rfl

@[simp]
lemma qdriftWeightedRemainderSuperOp_apply {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ) (X : HilbertOperator R) :
    qdriftWeightedRemainderSuperOp H p τ X =
      qdriftStepSuperOp H p τ X - qdriftWeightedFirstOrderSuperOp H p τ X := by
  rfl

@[simp]
lemma qdriftIdealRemainderSuperOp_zero {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) :
    qdriftIdealRemainderSuperOp H p 0 = 0 := by
  rw [qdriftIdealRemainderSuperOp, qdriftIdealStepSuperOp_zero,
    qdriftIdealFirstOrderSuperOp_zero]
  simp

lemma qdriftWeightedRemainderSuperOp_zero_of_sum_eq_one
    {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ)
    (hp : ∑ j, (p j : ℂ) = 1) :
    qdriftWeightedRemainderSuperOp H p 0 = 0 := by
  rw [qdriftWeightedRemainderSuperOp, qdriftStepSuperOp_zero_of_sum_eq_one H p hp,
    qdriftWeightedFirstOrderSuperOp_zero]
  simp

lemma qdriftIdealRemainderSuperOp_eq_unitaryStepRemainder
    {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ) :
    qdriftIdealRemainderSuperOp H p τ =
      unitaryStepRemainderSuperOp (weightedHamiltonianOp H p) τ := by
  rfl

-- Declaration-scoped exception: flexible simplification exposes the weighted sum
-- before the final pointwise `Finset.sum_congr`.
set_option linter.flexible false in
lemma qdriftWeightedRemainderSuperOp_eq_sum_unitaryStepRemainder
    {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hp : ∑ j, (p j : ℂ) = 1) :
    qdriftWeightedRemainderSuperOp H p τ =
      ∑ j, (p j : ℂ) • unitaryStepRemainderSuperOp (H j) τ := by
  rw [qdriftWeightedRemainderSuperOp, qdriftStepSuperOp, qdriftWeightedFirstOrderSuperOp,
    firstOrderSuperOp, qdriftWeightedGeneratorSuperOp]
  have hid : (LinearMap.id : SuperOp R) = ∑ j, (p j : ℂ) • (LinearMap.id : SuperOp R) := by
    rw [← Finset.sum_smul, hp]
    simp
  rw [hid]
  apply LinearMap.ext
  intro X
  simp only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, unitaryStepRemainderSuperOp, firstOrderSuperOp]
  simp [Finset.smul_sum, smul_smul, smul_add, smul_sub, mul_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp [mul_comm, mul_left_comm]

/-- Norm bound for the weighted qDRIFT remainder from abstract norm properties. -/
lemma qdriftWeightedRemainderSuperOp_norm_le_sum_unitaryStepRemainder
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hp : ∑ j, (p j : ℂ) = 1) :
    superOpNorm (qdriftWeightedRemainderSuperOp H p τ)
      ≤ ∑ j, scalarNorm (p j : ℂ)
          * superOpNorm (unitaryStepRemainderSuperOp (H j) τ) := by
  rw [qdriftWeightedRemainderSuperOp_eq_sum_unitaryStepRemainder H p τ hp]
  calc
    superOpNorm (∑ j, (p j : ℂ) • unitaryStepRemainderSuperOp (H j) τ)
        ≤ ∑ j, superOpNorm ((p j : ℂ) • unitaryStepRemainderSuperOp (H j) τ) :=
      hnorm.norm_sum_le
        (fun j => (p j : ℂ) • unitaryStepRemainderSuperOp (H j) τ)
    _ = ∑ j, scalarNorm (p j : ℂ)
          * superOpNorm (unitaryStepRemainderSuperOp (H j) τ) := by
      simp [hnorm.norm_smul]

/-- Budgeted version of the weighted qDRIFT remainder bound. -/
lemma qdriftWeightedRemainderSuperOp_norm_le_budget
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hp : ∑ j, (p j : ℂ) = 1) (budget : ℝ)
    (hbudget : ∑ j, scalarNorm (p j : ℂ)
          * superOpNorm (unitaryStepRemainderSuperOp (H j) τ) ≤ budget) :
    superOpNorm (qdriftWeightedRemainderSuperOp H p τ) ≤ budget :=
  le_trans
    (qdriftWeightedRemainderSuperOp_norm_le_sum_unitaryStepRemainder
      superOpNorm scalarNorm hnorm H p τ hp)
    hbudget

/-- Uniform single-term remainder bound implies a weighted qDRIFT remainder bound. -/
lemma qdriftWeightedRemainderSuperOp_norm_le_uniform_bound
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hp : ∑ j, (p j : ℂ) = 1)
    (termBound weightBudget : ℝ)
    (hterm : ∀ j, superOpNorm (unitaryStepRemainderSuperOp (H j) τ) ≤ termBound)
    (hweights : ∑ j, scalarNorm (p j : ℂ) ≤ weightBudget)
    (hscalar_nonneg : ∀ j, 0 ≤ scalarNorm (p j : ℂ))
    (hterm_nonneg : 0 ≤ termBound) :
    superOpNorm (qdriftWeightedRemainderSuperOp H p τ)
      ≤ weightBudget * termBound := by
  apply qdriftWeightedRemainderSuperOp_norm_le_budget
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm)
    (hnorm := hnorm) (H := H) (p := p) (τ := τ) (hp := hp)
  calc
    ∑ j, scalarNorm (p j : ℂ) * superOpNorm (unitaryStepRemainderSuperOp (H j) τ)
        ≤ ∑ j, scalarNorm (p j : ℂ) * termBound := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hterm j) (hscalar_nonneg j)
    _ = (∑ j, scalarNorm (p j : ℂ)) * termBound := by
      rw [Finset.sum_mul]
    _ ≤ weightBudget * termBound :=
      mul_le_mul_of_nonneg_right hweights hterm_nonneg

/-- qDRIFT and ideal evolution have the same first-order generator. -/
lemma qdriftGenerator_firstOrder_cancel {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) :
    qdriftIdealGeneratorSuperOp H p = qdriftWeightedGeneratorSuperOp H p := by
  rw [qdriftIdealGeneratorSuperOp, qdriftWeightedGeneratorSuperOp,
    weightedHamiltonianOp, liouvillianSuperOp_sum]

/-- The ideal and weighted qDRIFT first-order models coincide. -/
lemma qdriftFirstOrderSuperOp_eq {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ) :
    qdriftIdealFirstOrderSuperOp H p τ =
      qdriftWeightedFirstOrderSuperOp H p τ := by
  rw [qdriftIdealFirstOrderSuperOp, qdriftWeightedFirstOrderSuperOp,
    qdriftGenerator_firstOrder_cancel]

/-- The qDRIFT one-step error is the difference of the two second-order remainders. -/
lemma qdriftStepErrorSuperOp_eq_remainder_sub {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ) :
    qdriftStepErrorSuperOp H p τ =
      qdriftWeightedRemainderSuperOp H p τ - qdriftIdealRemainderSuperOp H p τ := by
  rw [qdriftStepErrorSuperOp, qdriftWeightedRemainderSuperOp,
    qdriftIdealRemainderSuperOp, qdriftFirstOrderSuperOp_eq H p τ]
  abel

/-- If every sampled unitary remainder is quadratic, then the weighted qDRIFT
remainder is quadratic. -/
lemma qdriftWeightedRemainderSuperOp_isQuadraticRemainder
    {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hp : ∑ j, (p j : ℂ) = 1)
    (hunit : ∀ j, IsQuadraticRemainder τ (unitaryStepRemainderSuperOp (H j) τ)) :
    IsQuadraticRemainder τ (qdriftWeightedRemainderSuperOp H p τ) := by
  rw [qdriftWeightedRemainderSuperOp_eq_sum_unitaryStepRemainder H p τ hp]
  exact IsQuadraticRemainder.sum
    (fun j => (p j : ℂ) • unitaryStepRemainderSuperOp (H j) τ)
    (fun j => IsQuadraticRemainder.smul (p j : ℂ) (hunit j))

/-- The ideal qDRIFT remainder is quadratic when the weighted Hamiltonian
unitary remainder is quadratic. -/
lemma qdriftIdealRemainderSuperOp_isQuadraticRemainder
    {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hideal :
      IsQuadraticRemainder τ
        (unitaryStepRemainderSuperOp (weightedHamiltonianOp H p) τ)) :
    IsQuadraticRemainder τ (qdriftIdealRemainderSuperOp H p τ) := by
  rw [qdriftIdealRemainderSuperOp_eq_unitaryStepRemainder]
  exact hideal

/-- The qDRIFT one-step error is quadratic once the weighted and ideal
remainders are quadratic. -/
lemma qdriftStepErrorSuperOp_isQuadraticRemainder_of_remainders
    {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hweighted : IsQuadraticRemainder τ (qdriftWeightedRemainderSuperOp H p τ))
    (hideal : IsQuadraticRemainder τ (qdriftIdealRemainderSuperOp H p τ)) :
    IsQuadraticRemainder τ (qdriftStepErrorSuperOp H p τ) := by
  rw [qdriftStepErrorSuperOp_eq_remainder_sub]
  exact IsQuadraticRemainder.sub hweighted hideal

/-- One-step qDRIFT error is quadratic from pointwise sampled-unitary
remainders and the ideal weighted-Hamiltonian remainder. -/
lemma qdriftStepErrorSuperOp_isQuadraticRemainder
    {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hp : ∑ j, (p j : ℂ) = 1)
    (hunit : ∀ j, IsQuadraticRemainder τ (unitaryStepRemainderSuperOp (H j) τ))
    (hideal :
      IsQuadraticRemainder τ
        (unitaryStepRemainderSuperOp (weightedHamiltonianOp H p) τ)) :
    IsQuadraticRemainder τ (qdriftStepErrorSuperOp H p τ) :=
  qdriftStepErrorSuperOp_isQuadraticRemainder_of_remainders H p τ
    (qdriftWeightedRemainderSuperOp_isQuadraticRemainder H p τ hp hunit)
    (qdriftIdealRemainderSuperOp_isQuadraticRemainder H p τ hideal)

/-- Abstract qDRIFT one-step error bound from weighted and ideal remainder budgets. -/
lemma qdriftStepErrorSuperOp_norm_le_remainder_budgets
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (weightedBudget idealBudget : ℝ)
    (hweighted : superOpNorm (qdriftWeightedRemainderSuperOp H p τ) ≤ weightedBudget)
    (hideal : superOpNorm (qdriftIdealRemainderSuperOp H p τ) ≤ idealBudget) :
    superOpNorm (qdriftStepErrorSuperOp H p τ) ≤ weightedBudget + idealBudget := by
  calc
    superOpNorm (qdriftStepErrorSuperOp H p τ)
        = superOpNorm
            (qdriftWeightedRemainderSuperOp H p τ - qdriftIdealRemainderSuperOp H p τ) := by
      rw [qdriftStepErrorSuperOp_eq_remainder_sub]
    _ ≤ superOpNorm (qdriftWeightedRemainderSuperOp H p τ)
          + superOpNorm (qdriftIdealRemainderSuperOp H p τ) :=
      hnorm.norm_sub_le
        (qdriftWeightedRemainderSuperOp H p τ)
        (qdriftIdealRemainderSuperOp H p τ)
    _ ≤ weightedBudget + idealBudget :=
      add_le_add hweighted hideal

/-- qDRIFT one-step error bound from uniform weighted and ideal remainder bounds. -/
lemma qdriftStepErrorSuperOp_norm_le_uniform_weighted_remainder_and_ideal
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hp : ∑ j, (p j : ℂ) = 1)
    (termBound weightBudget idealBudget : ℝ)
    (hterm : ∀ j, superOpNorm (unitaryStepRemainderSuperOp (H j) τ) ≤ termBound)
    (hweights : ∑ j, scalarNorm (p j : ℂ) ≤ weightBudget)
    (hscalar_nonneg : ∀ j, 0 ≤ scalarNorm (p j : ℂ))
    (hterm_nonneg : 0 ≤ termBound)
    (hideal : superOpNorm (qdriftIdealRemainderSuperOp H p τ) ≤ idealBudget) :
    superOpNorm (qdriftStepErrorSuperOp H p τ)
      ≤ weightBudget * termBound + idealBudget := by
  apply qdriftStepErrorSuperOp_norm_le_remainder_budgets
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
    (H := H) (p := p) (τ := τ)
  · exact qdriftWeightedRemainderSuperOp_norm_le_uniform_bound
      (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
      (H := H) (p := p) (τ := τ) (hp := hp)
      (termBound := termBound) (weightBudget := weightBudget)
      hterm hweights hscalar_nonneg hterm_nonneg
  · exact hideal

/-- Common qDRIFT specialization when the scalar weights have total norm at most one. -/
lemma qdriftStepErrorSuperOp_norm_le_uniform_remainder_and_ideal
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hp : ∑ j, (p j : ℂ) = 1)
    (termBound idealBudget : ℝ)
    (hterm : ∀ j, superOpNorm (unitaryStepRemainderSuperOp (H j) τ) ≤ termBound)
    (hweights : ∑ j, scalarNorm (p j : ℂ) ≤ 1)
    (hscalar_nonneg : ∀ j, 0 ≤ scalarNorm (p j : ℂ))
    (hterm_nonneg : 0 ≤ termBound)
    (hideal : superOpNorm (qdriftIdealRemainderSuperOp H p τ) ≤ idealBudget) :
    superOpNorm (qdriftStepErrorSuperOp H p τ) ≤ termBound + idealBudget := by
  simpa using
    qdriftStepErrorSuperOp_norm_le_uniform_weighted_remainder_and_ideal
      (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
      (H := H) (p := p) (τ := τ) (hp := hp)
      (termBound := termBound) (weightBudget := 1) (idealBudget := idealBudget)
      hterm hweights hscalar_nonneg hterm_nonneg hideal

/-- qDRIFT one-step error bound using packaged weight conditions. -/
lemma qdriftStepErrorSuperOp_norm_le_of_weight_conditions
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hweights : QDriftWeightConditions scalarNorm p)
    (termBound idealBudget : ℝ)
    (hterm : ∀ j, superOpNorm (unitaryStepRemainderSuperOp (H j) τ) ≤ termBound)
    (hterm_nonneg : 0 ≤ termBound)
    (hideal : superOpNorm (qdriftIdealRemainderSuperOp H p τ) ≤ idealBudget) :
    superOpNorm (qdriftStepErrorSuperOp H p τ) ≤ termBound + idealBudget :=
  qdriftStepErrorSuperOp_norm_le_uniform_remainder_and_ideal
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
    (H := H) (p := p) (τ := τ) (hp := hweights.sum_eq_one)
    (termBound := termBound) (idealBudget := idealBudget)
    hterm hweights.scalar_weights_bound hweights.scalar_nonneg hterm_nonneg hideal

/-- qDRIFT one-step error bound from packaged abstract remainder estimates. -/
lemma qdriftStepErrorSuperOp_norm_le_of_remainder_bounds
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hp : ∑ j, (p j : ℂ) = 1)
    (termBound idealBudget : ℝ)
    (hbounds :
      QDriftOneStepRemainderBounds superOpNorm scalarNorm H p τ termBound idealBudget) :
    superOpNorm (qdriftStepErrorSuperOp H p τ) ≤ termBound + idealBudget :=
  qdriftStepErrorSuperOp_norm_le_uniform_remainder_and_ideal
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
    (H := H) (p := p) (τ := τ) (hp := hp)
    (termBound := termBound) (idealBudget := idealBudget)
    hbounds.term_bound hbounds.scalar_weights_bound hbounds.scalar_nonneg
    hbounds.term_bound_nonneg hbounds.ideal_bound

/-- Abstract qDRIFT one-step error theorem with a caller-provided error budget. -/
lemma qdriftStepErrorSuperOp_norm_le_error_budget
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hp : ∑ j, (p j : ℂ) = 1)
    (termBound idealBudget errorBudget : ℝ)
    (hbounds :
      QDriftOneStepRemainderBounds superOpNorm scalarNorm H p τ termBound idealBudget)
    (hbudget : termBound + idealBudget ≤ errorBudget) :
    superOpNorm (qdriftStepErrorSuperOp H p τ) ≤ errorBudget :=
  le_trans
    (qdriftStepErrorSuperOp_norm_le_of_remainder_bounds
      (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
      (H := H) (p := p) (τ := τ) (hp := hp)
      (termBound := termBound) (idealBudget := idealBudget) hbounds)
    hbudget

/-- Abstract qDRIFT one-step error theorem with a quadratic step-size budget. -/
lemma qdriftStepErrorSuperOp_norm_le_quadratic_budget
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hp : ∑ j, (p j : ℂ) = 1)
    (termBound idealBudget constant : ℝ)
    (hbounds :
      QDriftOneStepRemainderBounds superOpNorm scalarNorm H p τ termBound idealBudget)
    (hbudget : termBound + idealBudget ≤ constant * τ ^ 2) :
    superOpNorm (qdriftStepErrorSuperOp H p τ) ≤ constant * τ ^ 2 :=
  qdriftStepErrorSuperOp_norm_le_error_budget
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
    (H := H) (p := p) (τ := τ) (hp := hp)
    (termBound := termBound) (idealBudget := idealBudget)
    (errorBudget := constant * τ ^ 2) hbounds hbudget

/-- qDRIFT one-step quadratic error bound from packaged estimates. -/
lemma qdriftStepErrorSuperOp_norm_le_of_quadratic_bounds
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hp : ∑ j, (p j : ℂ) = 1)
    (termBound idealBudget constant : ℝ)
    (hbounds :
      QDriftOneStepQuadraticBounds superOpNorm scalarNorm H p τ
        termBound idealBudget constant) :
    superOpNorm (qdriftStepErrorSuperOp H p τ) ≤ constant * τ ^ 2 :=
  qdriftStepErrorSuperOp_norm_le_quadratic_budget
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
    (H := H) (p := p) (τ := τ) (hp := hp)
    (termBound := termBound) (idealBudget := idealBudget)
    (constant := constant)
    hbounds.remainder_bounds hbounds.quadratic_budget

/-- qDRIFT quadratic error bound using packaged weight conditions. -/
lemma qdriftStepErrorSuperOp_norm_le_quadratic_of_weight_conditions
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hweights : QDriftWeightConditions scalarNorm p)
    (termBound idealBudget constant : ℝ)
    (hbounds :
      QDriftOneStepQuadraticBounds superOpNorm scalarNorm H p τ
        termBound idealBudget constant) :
    superOpNorm (qdriftStepErrorSuperOp H p τ) ≤ constant * τ ^ 2 :=
  qdriftStepErrorSuperOp_norm_le_of_quadratic_bounds
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
    (H := H) (p := p) (τ := τ) (hp := hweights.sum_eq_one)
    (termBound := termBound) (idealBudget := idealBudget)
    (constant := constant) hbounds

/-- qDRIFT quadratic error bound using real probability weights. -/
lemma qdriftStepErrorSuperOp_norm_le_quadratic_of_probability_weights
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hscalar : ∀ j, scalarNorm (p j : ℂ) = p j)
    (hprob : QDriftProbabilityWeights p)
    (termBound idealBudget constant : ℝ)
    (hbounds :
      QDriftOneStepQuadraticBounds superOpNorm scalarNorm H p τ
        termBound idealBudget constant) :
    superOpNorm (qdriftStepErrorSuperOp H p τ) ≤ constant * τ ^ 2 :=
  qdriftStepErrorSuperOp_norm_le_quadratic_of_weight_conditions
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
    (H := H) (p := p) (τ := τ)
    (hweights := QDriftWeightConditions.of_probability_weights scalarNorm p hscalar hprob)
    (termBound := termBound) (idealBudget := idealBudget)
    (constant := constant) hbounds

/-- Abstract qDRIFT one-step error theorem for the step size `t / steps`. -/
lemma qdriftStepErrorSuperOp_norm_le_time_div_steps_quadratic_budget
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (t : ℝ) (steps : ℕ)
    (hp : ∑ j, (p j : ℂ) = 1)
    (termBound idealBudget constant : ℝ)
    (hbounds :
      QDriftOneStepRemainderBounds superOpNorm scalarNorm H p
        (t / (steps : ℝ)) termBound idealBudget)
    (hbudget : termBound + idealBudget ≤ constant * (t / (steps : ℝ)) ^ 2) :
    superOpNorm (qdriftStepErrorSuperOp H p (t / (steps : ℝ)))
      ≤ constant * (t / (steps : ℝ)) ^ 2 :=
  qdriftStepErrorSuperOp_norm_le_quadratic_budget
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
    (H := H) (p := p) (τ := t / (steps : ℝ)) (hp := hp)
    (termBound := termBound) (idealBudget := idealBudget)
    (constant := constant) hbounds hbudget

/-- qDRIFT one-step quadratic error bound for the step size `t / steps`. -/
lemma qdriftStepErrorSuperOp_norm_le_time_div_steps_of_quadratic_bounds
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (t : ℝ) (steps : ℕ)
    (hp : ∑ j, (p j : ℂ) = 1)
    (termBound idealBudget constant : ℝ)
    (hbounds :
      QDriftOneStepQuadraticBounds superOpNorm scalarNorm H p
        (t / (steps : ℝ)) termBound idealBudget constant) :
    superOpNorm (qdriftStepErrorSuperOp H p (t / (steps : ℝ)))
      ≤ constant * (t / (steps : ℝ)) ^ 2 :=
  qdriftStepErrorSuperOp_norm_le_of_quadratic_bounds
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
    (H := H) (p := p) (τ := t / (steps : ℝ)) (hp := hp)
    (termBound := termBound) (idealBudget := idealBudget)
    (constant := constant) hbounds

/-- qDRIFT quadratic error bound for step size `t / steps` using packaged weights. -/
lemma qdriftStepErrorSuperOp_norm_le_time_div_steps_of_weight_conditions
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (t : ℝ) (steps : ℕ)
    (hweights : QDriftWeightConditions scalarNorm p)
    (termBound idealBudget constant : ℝ)
    (hbounds :
      QDriftOneStepQuadraticBounds superOpNorm scalarNorm H p
        (t / (steps : ℝ)) termBound idealBudget constant) :
    superOpNorm (qdriftStepErrorSuperOp H p (t / (steps : ℝ)))
      ≤ constant * (t / (steps : ℝ)) ^ 2 :=
  qdriftStepErrorSuperOp_norm_le_time_div_steps_of_quadratic_bounds
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
    (H := H) (p := p) (t := t) (steps := steps)
    (hp := hweights.sum_eq_one)
    (termBound := termBound) (idealBudget := idealBudget)
    (constant := constant) hbounds

/-- qDRIFT quadratic error bound for step size `t / steps` using probability weights. -/
lemma qdriftStepErrorSuperOp_norm_le_time_div_steps_of_probability_weights
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (t : ℝ) (steps : ℕ)
    (hscalar : ∀ j, scalarNorm (p j : ℂ) = p j)
    (hprob : QDriftProbabilityWeights p)
    (termBound idealBudget constant : ℝ)
    (hbounds :
      QDriftOneStepQuadraticBounds superOpNorm scalarNorm H p
        (t / (steps : ℝ)) termBound idealBudget constant) :
    superOpNorm (qdriftStepErrorSuperOp H p (t / (steps : ℝ)))
      ≤ constant * (t / (steps : ℝ)) ^ 2 :=
  qdriftStepErrorSuperOp_norm_le_time_div_steps_of_weight_conditions
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
    (H := H) (p := p) (t := t) (steps := steps)
    (hweights := QDriftWeightConditions.of_probability_weights scalarNorm p hscalar hprob)
    (termBound := termBound) (idealBudget := idealBudget)
    (constant := constant) hbounds

/-- qDRIFT one-step quadratic error bound written as `constant * t^2 / steps^2`. -/
lemma qdriftStepErrorSuperOp_norm_le_time_sq_div_steps_sq_of_weight_conditions
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (t : ℝ) (steps : ℕ)
    (hweights : QDriftWeightConditions scalarNorm p)
    (termBound idealBudget constant : ℝ)
    (hbounds :
      QDriftOneStepQuadraticBounds superOpNorm scalarNorm H p
        (t / (steps : ℝ)) termBound idealBudget constant) :
    superOpNorm (qdriftStepErrorSuperOp H p (t / (steps : ℝ)))
      ≤ constant * t ^ 2 / (steps : ℝ) ^ 2 := by
  calc
    superOpNorm (qdriftStepErrorSuperOp H p (t / (steps : ℝ)))
        ≤ constant * (t / (steps : ℝ)) ^ 2 :=
      qdriftStepErrorSuperOp_norm_le_time_div_steps_of_weight_conditions
        (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
        (H := H) (p := p) (t := t) (steps := steps)
        (hweights := hweights)
        (termBound := termBound) (idealBudget := idealBudget)
        (constant := constant) hbounds
    _ = constant * t ^ 2 / (steps : ℝ) ^ 2 := by
      ring_nf

/-- qDRIFT one-step error bound at `t / steps` with a caller-provided budget. -/
lemma qdriftStepErrorSuperOp_norm_le_time_sq_div_steps_sq_budget
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (t : ℝ) (steps : ℕ)
    (hweights : QDriftWeightConditions scalarNorm p)
    (termBound idealBudget constant errorBudget : ℝ)
    (hbounds :
      QDriftOneStepQuadraticBounds superOpNorm scalarNorm H p
        (t / (steps : ℝ)) termBound idealBudget constant)
    (hbudget : constant * t ^ 2 / (steps : ℝ) ^ 2 ≤ errorBudget) :
    superOpNorm (qdriftStepErrorSuperOp H p (t / (steps : ℝ))) ≤ errorBudget :=
  le_trans
    (qdriftStepErrorSuperOp_norm_le_time_sq_div_steps_sq_of_weight_conditions
      (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
      (H := H) (p := p) (t := t) (steps := steps)
      (hweights := hweights)
      (termBound := termBound) (idealBudget := idealBudget)
      (constant := constant) hbounds)
    hbudget

/-- qDRIFT one-step quadratic error bound using probability weights. -/
lemma qdriftStepErrorSuperOp_norm_le_time_sq_div_steps_sq_of_probability_weights
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (t : ℝ) (steps : ℕ)
    (hscalar : ∀ j, scalarNorm (p j : ℂ) = p j)
    (hprob : QDriftProbabilityWeights p)
    (termBound idealBudget constant : ℝ)
    (hbounds :
      QDriftOneStepQuadraticBounds superOpNorm scalarNorm H p
        (t / (steps : ℝ)) termBound idealBudget constant) :
    superOpNorm (qdriftStepErrorSuperOp H p (t / (steps : ℝ)))
      ≤ constant * t ^ 2 / (steps : ℝ) ^ 2 := by
  calc
    superOpNorm (qdriftStepErrorSuperOp H p (t / (steps : ℝ)))
        ≤ constant * (t / (steps : ℝ)) ^ 2 :=
      qdriftStepErrorSuperOp_norm_le_time_div_steps_of_probability_weights
        (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
        (H := H) (p := p) (t := t) (steps := steps)
        (hscalar := hscalar) (hprob := hprob)
        (termBound := termBound) (idealBudget := idealBudget)
        (constant := constant) hbounds
    _ = constant * t ^ 2 / (steps : ℝ) ^ 2 := by
      ring_nf

/-- The standard qDRIFT one-step quadratic budget at step size `t / steps`. -/
def qdriftOneStepQuadraticBudget (constant t : ℝ) (steps : ℕ) : ℝ :=
  constant * t ^ 2 / (steps : ℝ) ^ 2

/-- The formal budget obtained by summing the same one-step budget over all steps. -/
def qdriftTotalQuadraticBudget (constant t : ℝ) (steps : ℕ) : ℝ :=
  (steps : ℝ) * qdriftOneStepQuadraticBudget constant t steps

lemma qdriftTotalQuadraticBudget_eq (constant t : ℝ) (steps : ℕ) :
    qdriftTotalQuadraticBudget constant t steps = constant * t ^ 2 / (steps : ℝ) := by
  by_cases hsteps : (steps : ℝ) = 0
  · simp [qdriftTotalQuadraticBudget, qdriftOneStepQuadraticBudget, hsteps]
  · rw [qdriftTotalQuadraticBudget, qdriftOneStepQuadraticBudget]
    field_simp [hsteps]

/-- Abstract total qDRIFT error after `steps` steps.

This alias keeps the abstract hybrid-budget API separate from the concrete
choice of repeated averaged superoperators used in the final corollaries. -/
abbrev QDriftTotalError (R : Register) : Type :=
  SuperOp R

/-- The propagated one-step errors appearing in an abstract qDRIFT hybrid argument. -/
def qdriftHybridStepErrorFamily {R : Register} {ι : Type} [Fintype ι]
    {steps : ℕ} (pre post : Fin steps → SuperOp R)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ) :
    Fin steps → SuperOp R :=
  fun k => qdriftPropagatedStepError (pre k) (post k) H p τ

/-- A finite hybrid decomposition is quadratic when each step error is
quadratic in the same step size. -/
lemma qdriftTotalError_isQuadraticRemainder_of_step_error_family
    {R : Register} {steps : ℕ} (totalError : QDriftTotalError R)
    (stepError : Fin steps → SuperOp R) (τ : ℝ)
    (hdecomp : totalError = ∑ k, stepError k)
    (hstep : ∀ k, IsQuadraticRemainder τ (stepError k)) :
    IsQuadraticRemainder τ totalError := by
  rw [hdecomp]
  exact IsQuadraticRemainder.sum stepError hstep

/-- Hybrid qDRIFT total error is quadratic when each propagated hybrid step is
quadratic. -/
lemma qdriftTotalError_isQuadraticRemainder_of_hybrid_family
    {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ)
    (totalError : QDriftTotalError R) (τ : ℝ) (steps : ℕ)
    (pre post : Fin steps → SuperOp R)
    (hdecomp :
      totalError = ∑ k, qdriftHybridStepErrorFamily pre post H p τ k)
    (hstep : ∀ k,
      IsQuadraticRemainder τ (qdriftHybridStepErrorFamily pre post H p τ k)) :
    IsQuadraticRemainder τ totalError :=
  qdriftTotalError_isQuadraticRemainder_of_step_error_family
    (totalError := totalError)
    (stepError := qdriftHybridStepErrorFamily pre post H p τ)
    (τ := τ) hdecomp hstep

/-- Hybrid qDRIFT total error is quadratic from a quadratic unpropagated
one-step error. -/
lemma qdriftTotalError_isQuadraticRemainder_of_hybrid_propagation
    {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ)
    (totalError : QDriftTotalError R) (τ : ℝ) (steps : ℕ)
    (pre post : Fin steps → SuperOp R)
    (hdecomp :
      totalError = ∑ k, qdriftHybridStepErrorFamily pre post H p τ k)
    (hstep : IsQuadraticRemainder τ (qdriftStepErrorSuperOp H p τ)) :
    IsQuadraticRemainder τ totalError :=
  qdriftTotalError_isQuadraticRemainder_of_hybrid_family
    (H := H) (p := p) (totalError := totalError) (τ := τ)
    (steps := steps) (pre := pre) (post := post) hdecomp
    (fun k =>
      qdriftPropagatedStepError_isQuadraticRemainder
        (pre k) (post k) H p τ hstep)

/-- Total qDRIFT error statement with the budget `constant * t^2 / steps`. -/
def qdriftTotalErrorStatement {R : Register}
    (superOpNorm : SuperOp R → ℝ) (totalError : QDriftTotalError R)
    (constant t : ℝ) (steps : ℕ) : Prop :=
  superOpNorm totalError ≤ constant * t ^ 2 / (steps : ℝ)

lemma qdriftTotalError_norm_le_of_budget {R : Register}
    (superOpNorm : SuperOp R → ℝ) (totalError : QDriftTotalError R)
    (constant t : ℝ) (steps : ℕ)
    (hbudget : superOpNorm totalError ≤ qdriftTotalQuadraticBudget constant t steps) :
    qdriftTotalErrorStatement superOpNorm totalError constant t steps := by
  rw [qdriftTotalErrorStatement, qdriftTotalQuadraticBudget_eq] at *
  exact hbudget

lemma qdriftTotalError_norm_le_of_summed_one_step_budget {R : Register}
    (superOpNorm : SuperOp R → ℝ) (totalError : QDriftTotalError R)
    (constant t : ℝ) (steps : ℕ)
    (hbudget :
      superOpNorm totalError
        ≤ (steps : ℝ) * qdriftOneStepQuadraticBudget constant t steps) :
    qdriftTotalErrorStatement superOpNorm totalError constant t steps :=
  qdriftTotalError_norm_le_of_budget
    (superOpNorm := superOpNorm) (totalError := totalError)
    (constant := constant) (t := t) (steps := steps)
    hbudget

lemma qdriftTotalError_norm_le_of_fin_sum_one_step_budget {R : Register}
    (superOpNorm : SuperOp R → ℝ) (totalError : QDriftTotalError R)
    (constant t : ℝ) (steps : ℕ)
    (hbudget :
      superOpNorm totalError
        ≤ ∑ _k : Fin steps, qdriftOneStepQuadraticBudget constant t steps) :
    qdriftTotalErrorStatement superOpNorm totalError constant t steps := by
  apply qdriftTotalError_norm_le_of_summed_one_step_budget
    (superOpNorm := superOpNorm) (totalError := totalError)
    (constant := constant) (t := t) (steps := steps)
  calc
    superOpNorm totalError
        ≤ ∑ _k : Fin steps, qdriftOneStepQuadraticBudget constant t steps := hbudget
    _ = (steps : ℝ) * qdriftOneStepQuadraticBudget constant t steps := by
      simp

lemma qdriftTotalError_norm_le_of_fin_sum_step_budgets {R : Register}
    (superOpNorm : SuperOp R → ℝ) (totalError : QDriftTotalError R)
    (constant t : ℝ) (steps : ℕ) (stepBudget : Fin steps → ℝ)
    (hbudget : superOpNorm totalError ≤ ∑ k, stepBudget k)
    (hstep : ∀ k, stepBudget k ≤ qdriftOneStepQuadraticBudget constant t steps) :
    qdriftTotalErrorStatement superOpNorm totalError constant t steps := by
  apply qdriftTotalError_norm_le_of_fin_sum_one_step_budget
    (superOpNorm := superOpNorm) (totalError := totalError)
    (constant := constant) (t := t) (steps := steps)
  calc
    superOpNorm totalError ≤ ∑ k, stepBudget k := hbudget
    _ ≤ ∑ _k : Fin steps, qdriftOneStepQuadraticBudget constant t steps := by
      apply Finset.sum_le_sum
      intro k _
      exact hstep k

lemma qdriftTotalError_norm_le_of_step_error_family {R : Register}
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (totalError : QDriftTotalError R) (constant t : ℝ) (steps : ℕ)
    (stepError : Fin steps → SuperOp R)
    (hdecomp : totalError = ∑ k, stepError k)
    (hstep : ∀ k, superOpNorm (stepError k)
      ≤ qdriftOneStepQuadraticBudget constant t steps) :
    qdriftTotalErrorStatement superOpNorm totalError constant t steps := by
  apply qdriftTotalError_norm_le_of_fin_sum_step_budgets
    (superOpNorm := superOpNorm) (totalError := totalError)
    (constant := constant) (t := t) (steps := steps)
    (stepBudget := fun k => superOpNorm (stepError k))
  · rw [hdecomp]
    exact hnorm.norm_sum_le stepError
  · exact hstep

lemma qdriftTotalError_norm_le_of_hybrid_family {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ)
    (totalError : QDriftTotalError R) (constant t : ℝ) (steps : ℕ)
    (pre post : Fin steps → SuperOp R)
    (hdecomp :
      totalError = ∑ k, qdriftHybridStepErrorFamily pre post H p (t / (steps : ℝ)) k)
    (hstep : ∀ k,
      superOpNorm (qdriftHybridStepErrorFamily pre post H p (t / (steps : ℝ)) k)
        ≤ qdriftOneStepQuadraticBudget constant t steps) :
    qdriftTotalErrorStatement superOpNorm totalError constant t steps :=
  qdriftTotalError_norm_le_of_step_error_family
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
    (totalError := totalError) (constant := constant) (t := t) (steps := steps)
    (stepError := qdriftHybridStepErrorFamily pre post H p (t / (steps : ℝ)))
    hdecomp hstep

lemma qdriftTotalError_norm_le_of_hybrid_family_nonexpansive
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ)
    (totalError : QDriftTotalError R) (constant t : ℝ) (steps : ℕ)
    (pre post : Fin steps → SuperOp R)
    (hdecomp :
      totalError = ∑ k, qdriftHybridStepErrorFamily pre post H p (t / (steps : ℝ)) k)
    (hpre : ∀ k, SuperOpLeftNonexpansive superOpNorm (pre k))
    (hpost : ∀ k, SuperOpRightNonexpansive superOpNorm (post k))
    (honeStep : superOpNorm (qdriftStepErrorSuperOp H p (t / (steps : ℝ)))
      ≤ qdriftOneStepQuadraticBudget constant t steps) :
    qdriftTotalErrorStatement superOpNorm totalError constant t steps := by
  apply qdriftTotalError_norm_le_of_hybrid_family
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
    (H := H) (p := p)
    (totalError := totalError) (constant := constant) (t := t) (steps := steps)
    (pre := pre) (post := post)
    hdecomp
  intro k
  exact le_trans
    (qdriftPropagatedStepError_norm_le
      (superOpNorm := superOpNorm)
      (pre := pre k) (post := post k)
      (H := H) (p := p) (τ := t / (steps : ℝ))
      (hpre := hpre k) (hpost := hpost k))
    honeStep

/-- A hybrid decomposition with a uniform quadratic remainder budget on each
step accumulates to `steps * scalarNorm τ^2 * Λ`. -/
lemma qdriftTotalError_norm_le_of_quadratic_step_budgets
    {R : Register}
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (totalError : QDriftTotalError R) (steps : ℕ) (τ Λ : ℝ)
    (stepError : Fin steps → SuperOp R)
    (hdecomp : totalError = ∑ k, stepError k)
    (hbudget : ∀ k,
      QuadraticRemainderNormBudget superOpNorm scalarNorm τ Λ (stepError k)) :
    superOpNorm totalError ≤ (steps : ℝ) * (scalarNorm ((τ : ℂ) ^ 2) * Λ) := by
  calc
    superOpNorm totalError = superOpNorm (∑ k, stepError k) := by
      rw [hdecomp]
    _ ≤ ∑ k, superOpNorm (stepError k) :=
      hnorm.norm_sum_le stepError
    _ ≤ ∑ _k : Fin steps, scalarNorm ((τ : ℂ) ^ 2) * Λ := by
      apply Finset.sum_le_sum
      intro k _
      exact QuadraticRemainderNormBudget.norm_le
        (superOpNorm := superOpNorm) (scalarNorm := scalarNorm)
        (hnorm := hnorm) (τ := τ) (Λ := Λ)
        (Φ := stepError k) (hbudget := hbudget k)
    _ = (steps : ℝ) * (scalarNorm ((τ : ℂ) ^ 2) * Λ) := by
      simp

/-- Hybrid qDRIFT total error bound from uniform quadratic budgets on the
propagated hybrid summands. -/
lemma qdriftTotalError_norm_le_of_hybrid_quadratic_budgets
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ)
    (totalError : QDriftTotalError R) (steps : ℕ) (τ Λ : ℝ)
    (pre post : Fin steps → SuperOp R)
    (hdecomp :
      totalError = ∑ k, qdriftHybridStepErrorFamily pre post H p τ k)
    (hbudget : ∀ k,
      QuadraticRemainderNormBudget superOpNorm scalarNorm τ Λ
        (qdriftHybridStepErrorFamily pre post H p τ k)) :
    superOpNorm totalError ≤ (steps : ℝ) * (scalarNorm ((τ : ℂ) ^ 2) * Λ) :=
  qdriftTotalError_norm_le_of_quadratic_step_budgets
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
    (totalError := totalError) (steps := steps) (τ := τ) (Λ := Λ)
    (stepError := qdriftHybridStepErrorFamily pre post H p τ)
    hdecomp hbudget

/-- Final abstract qDRIFT global error bound.  The hypothesis `hscale` is where
an eventual concrete scalar norm turns `steps * ‖(t / steps)^2‖ * Λ` into
`t^2 / steps * Λ`. -/
lemma qdrift_global_error_bound_of_hybrid_quadratic_budgets
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ)
    (totalError : QDriftTotalError R) (t Λ : ℝ) (steps : ℕ)
    (pre post : Fin steps → SuperOp R)
    (hdecomp :
      totalError = ∑ k,
        qdriftHybridStepErrorFamily pre post H p (t / (steps : ℝ)) k)
    (hbudget : ∀ k,
      QuadraticRemainderNormBudget superOpNorm scalarNorm (t / (steps : ℝ)) Λ
        (qdriftHybridStepErrorFamily pre post H p (t / (steps : ℝ)) k))
    (hscale :
      (steps : ℝ) * (scalarNorm (((t / (steps : ℝ) : ℝ) : ℂ) ^ 2) * Λ)
        ≤ (t ^ 2 / (steps : ℝ)) * Λ) :
    superOpNorm totalError ≤ (t ^ 2 / (steps : ℝ)) * Λ :=
  le_trans
    (qdriftTotalError_norm_le_of_hybrid_quadratic_budgets
      (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
      (H := H) (p := p) (totalError := totalError) (steps := steps)
      (τ := t / (steps : ℝ)) (Λ := Λ) (pre := pre) (post := post)
      hdecomp hbudget)
    hscale

/-- Scalar-norm scale conversion for the qDRIFT global error bound. -/
lemma qdrift_global_error_scale_le
    (scalarNorm : ℂ → ℝ) (t Λ : ℝ) (steps : ℕ)
    (hsteps : steps ≠ 0)
    (hΛ : 0 ≤ Λ)
    (hscalar_sq :
      scalarNorm (((t / (steps : ℝ) : ℝ) : ℂ) ^ 2)
        ≤ (t / (steps : ℝ)) ^ 2) :
    (steps : ℝ) * (scalarNorm (((t / (steps : ℝ) : ℝ) : ℂ) ^ 2) * Λ)
      ≤ (t ^ 2 / (steps : ℝ)) * Λ := by
  have hsteps_pos : 0 < (steps : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hsteps
  calc
    (steps : ℝ) * (scalarNorm (((t / (steps : ℝ) : ℝ) : ℂ) ^ 2) * Λ)
        ≤ (steps : ℝ) * ((t / (steps : ℝ)) ^ 2 * Λ) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hscalar_sq hΛ)
        (le_of_lt hsteps_pos)
    _ = (t ^ 2 / (steps : ℝ)) * Λ := by
      field_simp [hsteps_pos.ne']

open scoped Matrix.Norms.L2Operator in
/-- Concrete second-order bound for the Hamiltonian time-evolution generator
`exp(-i τ H) - 1 - (-i τ H)`. -/
lemma timeEvolutionOp_generator_remainder_norm_le {R : Register}
    (H : HilbertOperator R) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖NormedSpace.exp ((-(Complex.I * (τ : ℂ))) • H) - 1 -
        ((-(Complex.I * (τ : ℂ))) • H)‖
      ≤ (1 / 2) * τ ^ 2 * ‖H‖ ^ 2 * Real.exp (τ * ‖H‖) := by
  let A : HilbertOperator R := (-(Complex.I * (τ : ℂ))) • H
  have hA := norm_exp_sub_one_sub_id_le_rclike ℂ A
  have hnormA : ‖A‖ = τ * ‖H‖ := by
    dsimp [A]
    rw [norm_smul]
    have hscalar : ‖-(Complex.I * (τ : ℂ))‖ = τ := by
      have hI : ‖Complex.I‖ = 1 := by
        have hsq : ‖Complex.I‖ ^ 2 = 1 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_I]
        nlinarith [norm_nonneg Complex.I]
      rw [norm_neg, norm_mul, hI, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ]
      ring
    rw [hscalar]
  calc
    ‖NormedSpace.exp ((-(Complex.I * (τ : ℂ))) • H) - 1 -
        ((-(Complex.I * (τ : ℂ))) • H)‖
        = ‖NormedSpace.exp A - 1 - A‖ := by
      rfl
    _ ≤ (1 / 2) * ‖A‖ ^ 2 * Real.exp ‖A‖ := hA
    _ = (1 / 2) * τ ^ 2 * ‖H‖ ^ 2 * Real.exp (τ * ‖H‖) := by
      rw [hnormA]
      ring

/-- The adjoint of a time-evolution operator is the exponential with the
opposite skew-Hermitian generator. -/
lemma star_timeEvolutionOp_eq_exp_pos_generator {R : Register}
    {H : HilbertOperator R} (hH : H.IsHermitian) (τ : ℝ) :
    star (timeEvolutionOp H τ) =
      NormedSpace.exp (((τ : ℂ) * Complex.I) • H) := by
  rw [timeEvolutionOp, NormedSpace.star_exp]
  congr 1
  ext i j
  have hentry : (starRingEnd ℂ) (H j i) = H i j := by
    have h := congrArg (fun M : HilbertOperator R => M i j) hH.eq
    simpa [Matrix.conjTranspose_apply] using h
  simp [hentry]
  ring_nf
  tauto

open scoped Matrix.Norms.L2Operator in
/-- Concrete second-order bound for the adjoint time-evolution generator
`U† - 1 - i τ H`. -/
lemma star_timeEvolutionOp_generator_remainder_norm_le {R : Register}
    {H : HilbertOperator R} (hH : H.IsHermitian) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖star (timeEvolutionOp H τ) - 1 - (((τ : ℂ) * Complex.I) • H)‖
      ≤ (1 / 2) * τ ^ 2 * ‖H‖ ^ 2 * Real.exp (τ * ‖H‖) := by
  let B : HilbertOperator R := ((τ : ℂ) * Complex.I) • H
  have hB := norm_exp_sub_one_sub_id_le_rclike ℂ B
  have hnormB : ‖B‖ = τ * ‖H‖ := by
    dsimp [B]
    rw [norm_smul]
    have hscalar : ‖(τ : ℂ) * Complex.I‖ = τ := by
      have hI : ‖Complex.I‖ = 1 := by
        have hsq : ‖Complex.I‖ ^ 2 = 1 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_I]
        nlinarith [norm_nonneg Complex.I]
      rw [norm_mul, hI, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ]
      ring
    rw [hscalar]
  calc
    ‖star (timeEvolutionOp H τ) - 1 - (((τ : ℂ) * Complex.I) • H)‖
        = ‖NormedSpace.exp B - 1 - B‖ := by
          rw [star_timeEvolutionOp_eq_exp_pos_generator hH τ]
    _ ≤ (1 / 2) * ‖B‖ ^ 2 * Real.exp ‖B‖ := hB
    _ = (1 / 2) * τ ^ 2 * ‖H‖ ^ 2 * Real.exp (τ * ‖H‖) := by
      rw [hnormB]
      ring

open scoped Matrix.Norms.L2Operator in
/-- Uniform budget version of the adjoint time-evolution generator remainder. -/
lemma star_timeEvolutionOp_generator_remainder_norm_le_budget {R : Register}
    {H : HilbertOperator R} (hH : H.IsHermitian) {τ Λ : ℝ}
    (hτ : 0 ≤ τ) (hHnorm : ‖H‖ ≤ Λ) :
    ‖star (timeEvolutionOp H τ) - 1 - (((τ : ℂ) * Complex.I) • H)‖
      ≤ (1 / 2) * τ ^ 2 * Λ ^ 2 * Real.exp (τ * Λ) := by
  have hΛ : 0 ≤ Λ := le_trans (norm_nonneg H) hHnorm
  calc
    ‖star (timeEvolutionOp H τ) - 1 - (((τ : ℂ) * Complex.I) • H)‖
        ≤ (1 / 2) * τ ^ 2 * ‖H‖ ^ 2 * Real.exp (τ * ‖H‖) :=
      star_timeEvolutionOp_generator_remainder_norm_le hH hτ
    _ ≤ (1 / 2) * τ ^ 2 * Λ ^ 2 * Real.exp (τ * Λ) := by
      have hcoef : 0 ≤ (1 / 2 : ℝ) * τ ^ 2 := by positivity
      have hsq : ‖H‖ ^ 2 ≤ Λ ^ 2 := by
        nlinarith [sq_nonneg (Λ - ‖H‖), norm_nonneg H]
      have hexp : Real.exp (τ * ‖H‖) ≤ Real.exp (τ * Λ) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hHnorm hτ)
      have htail :
          ‖H‖ ^ 2 * Real.exp (τ * ‖H‖)
            ≤ Λ ^ 2 * Real.exp (τ * Λ) := by
        exact mul_le_mul hsq hexp (le_of_lt (Real.exp_pos _)) (sq_nonneg Λ)
      nlinarith [mul_le_mul_of_nonneg_left htail hcoef]

open scoped Matrix.Norms.L2Operator in
/-- Uniform adjoint-generator remainder bound with qDRIFT step size and the
global exponential factor. -/
lemma star_timeEvolutionOp_generator_remainder_norm_le_global_exp {R : Register}
    {H : HilbertOperator R} (hH : H.IsHermitian) {t Λ : ℝ} {r : ℕ}
    (ht : 0 ≤ t) (hr : 0 < r) (hHnorm : ‖H‖ ≤ Λ) :
    let τ : ℝ := t / (r : ℝ)
    ‖star (timeEvolutionOp H τ) - 1 - (((τ : ℂ) * Complex.I) • H)‖
      ≤ (1 / 2) * τ ^ 2 * Λ ^ 2 * Real.exp (t * Λ) := by
  dsimp
  have hΛ : 0 ≤ Λ := le_trans (norm_nonneg H) hHnorm
  have hrℝ : 0 < (r : ℝ) := by exact_mod_cast hr
  have hr_one : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hτ_le_t : t / (r : ℝ) ≤ t := by
    rw [div_le_iff₀ hrℝ]
    nlinarith [mul_le_mul_of_nonneg_left hr_one ht]
  have hτ_nonneg : 0 ≤ t / (r : ℝ) := div_nonneg ht (le_of_lt hrℝ)
  have hexp : Real.exp ((t / (r : ℝ)) * Λ) ≤ Real.exp (t * Λ) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hτ_le_t hΛ)
  calc
    ‖star (timeEvolutionOp H (t / (r : ℝ))) - 1 -
        (((t / (r : ℝ) : ℝ) : ℂ) * Complex.I) • H‖
        ≤ (1 / 2) * (t / (r : ℝ)) ^ 2 * Λ ^ 2 *
            Real.exp ((t / (r : ℝ)) * Λ) :=
      star_timeEvolutionOp_generator_remainder_norm_le_budget hH hτ_nonneg hHnorm
    _ ≤ (1 / 2) * (t / (r : ℝ)) ^ 2 * Λ ^ 2 * Real.exp (t * Λ) := by
      have hcoef : 0 ≤ (1 / 2 : ℝ) * (t / (r : ℝ)) ^ 2 * Λ ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hexp hcoef]

open scoped Matrix.Norms.L2Operator in
/-- The same generator-level exponential remainder bound, specialized to the
qDRIFT step size `τ = t / r`. -/
lemma timeEvolutionOp_generator_remainder_norm_le_div_steps {R : Register}
    (H : HilbertOperator R) {t : ℝ} {r : ℕ} (ht : 0 ≤ t) (hr : 0 < r) :
    let τ : ℝ := t / (r : ℝ)
    ‖NormedSpace.exp ((-(Complex.I * (τ : ℂ))) • H) - 1 -
        ((-(Complex.I * (τ : ℂ))) • H)‖
      ≤ (1 / 2) * τ ^ 2 * ‖H‖ ^ 2 * Real.exp (τ * ‖H‖) := by
  dsimp
  have hrℝ : 0 < (r : ℝ) := by exact_mod_cast hr
  exact timeEvolutionOp_generator_remainder_norm_le H
    (div_nonneg ht (le_of_lt hrℝ))

open scoped Matrix.Norms.L2Operator in
/-- Generator-level exponential remainder bound with a uniform Hamiltonian
norm budget. -/
lemma timeEvolutionOp_generator_remainder_norm_le_budget {R : Register}
    (H : HilbertOperator R) {τ Λ : ℝ} (hτ : 0 ≤ τ) (hH : ‖H‖ ≤ Λ) :
    ‖NormedSpace.exp ((-(Complex.I * (τ : ℂ))) • H) - 1 -
        ((-(Complex.I * (τ : ℂ))) • H)‖
      ≤ (1 / 2) * τ ^ 2 * Λ ^ 2 * Real.exp (τ * Λ) := by
  have hΛ : 0 ≤ Λ := le_trans (norm_nonneg H) hH
  calc
    ‖NormedSpace.exp ((-(Complex.I * (τ : ℂ))) • H) - 1 -
        ((-(Complex.I * (τ : ℂ))) • H)‖
        ≤ (1 / 2) * τ ^ 2 * ‖H‖ ^ 2 * Real.exp (τ * ‖H‖) :=
      timeEvolutionOp_generator_remainder_norm_le H hτ
    _ ≤ (1 / 2) * τ ^ 2 * Λ ^ 2 * Real.exp (τ * Λ) := by
      have hcoef : 0 ≤ (1 / 2 : ℝ) * τ ^ 2 := by positivity
      have hsq : ‖H‖ ^ 2 ≤ Λ ^ 2 := by
        nlinarith [sq_nonneg (Λ - ‖H‖), norm_nonneg H]
      have hexp : Real.exp (τ * ‖H‖) ≤ Real.exp (τ * Λ) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hH hτ)
      have htail :
          ‖H‖ ^ 2 * Real.exp (τ * ‖H‖)
            ≤ Λ ^ 2 * Real.exp (τ * Λ) := by
        exact mul_le_mul hsq hexp (le_of_lt (Real.exp_pos _)) (sq_nonneg Λ)
      nlinarith [mul_le_mul_of_nonneg_left htail hcoef]

open scoped Matrix.Norms.L2Operator in
/-- Uniform generator-level remainder bound at qDRIFT step size `τ = t / r`. -/
lemma timeEvolutionOp_generator_remainder_norm_le_div_steps_budget {R : Register}
    (H : HilbertOperator R) {t Λ : ℝ} {r : ℕ}
    (ht : 0 ≤ t) (hr : 0 < r) (hH : ‖H‖ ≤ Λ) :
    let τ : ℝ := t / (r : ℝ)
    ‖NormedSpace.exp ((-(Complex.I * (τ : ℂ))) • H) - 1 -
        ((-(Complex.I * (τ : ℂ))) • H)‖
      ≤ (1 / 2) * τ ^ 2 * Λ ^ 2 * Real.exp (τ * Λ) := by
  dsimp
  have hrℝ : 0 < (r : ℝ) := by exact_mod_cast hr
  exact timeEvolutionOp_generator_remainder_norm_le_budget H
    (div_nonneg ht (le_of_lt hrℝ)) hH

open scoped Matrix.Norms.L2Operator in
/-- Uniform generator-level remainder bound with the global exponential factor
`exp (t * Λ)`. -/
lemma timeEvolutionOp_generator_remainder_norm_le_global_exp {R : Register}
    (H : HilbertOperator R) {t Λ : ℝ} {r : ℕ}
    (ht : 0 ≤ t) (hr : 0 < r) (hH : ‖H‖ ≤ Λ) :
    let τ : ℝ := t / (r : ℝ)
    ‖NormedSpace.exp ((-(Complex.I * (τ : ℂ))) • H) - 1 -
        ((-(Complex.I * (τ : ℂ))) • H)‖
      ≤ (1 / 2) * τ ^ 2 * Λ ^ 2 * Real.exp (t * Λ) := by
  dsimp
  have hΛ : 0 ≤ Λ := le_trans (norm_nonneg H) hH
  have hrℝ : 0 < (r : ℝ) := by exact_mod_cast hr
  have hr_one : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hτ_le_t : t / (r : ℝ) ≤ t := by
    rw [div_le_iff₀ hrℝ]
    nlinarith [mul_le_mul_of_nonneg_left hr_one ht]
  have hexp : Real.exp ((t / (r : ℝ)) * Λ) ≤ Real.exp (t * Λ) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hτ_le_t hΛ)
  calc
    ‖NormedSpace.exp ((-(Complex.I * ((t / (r : ℝ) : ℝ) : ℂ))) • H) - 1 -
        ((-(Complex.I * ((t / (r : ℝ) : ℝ) : ℂ))) • H)‖
        ≤ (1 / 2) * (t / (r : ℝ)) ^ 2 * Λ ^ 2 *
            Real.exp ((t / (r : ℝ)) * Λ) :=
      timeEvolutionOp_generator_remainder_norm_le_div_steps_budget H ht hr hH
    _ ≤ (1 / 2) * (t / (r : ℝ)) ^ 2 * Λ ^ 2 * Real.exp (t * Λ) := by
      have hcoef : 0 ≤ (1 / 2 : ℝ) * (t / (r : ℝ)) ^ 2 * Λ ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hexp hcoef]

open scoped Matrix.Norms.L2Operator in
/-- Left exponential remainder in the notation used by the conjugation
decomposition, with `A = -i τ H` and `τ = t / r`. -/
lemma timeEvolutionOp_left_remainder_norm_le_global_exp {R : Register}
    (H : HilbertOperator R) {t Λ : ℝ} {r : ℕ}
    (ht : 0 ≤ t) (hr : 0 < r) (hHnorm : ‖H‖ ≤ Λ) :
    let τ : ℝ := t / (r : ℝ)
    let A : HilbertOperator R := (-((τ : ℂ) * Complex.I)) • H
    ‖timeEvolutionOp H τ - 1 - A‖
      ≤ (1 / 2) * τ ^ 2 * Λ ^ 2 * Real.exp (t * Λ) := by
  dsimp
  simpa [timeEvolutionOp, mul_comm] using
    timeEvolutionOp_generator_remainder_norm_le_global_exp H ht hr hHnorm

open scoped Matrix.Norms.L2Operator in
/-- Right exponential remainder in the notation used by the conjugation
decomposition, with `A = -i τ H` and `τ = t / r`. -/
lemma star_timeEvolutionOp_right_remainder_norm_le_global_exp {R : Register}
    {H : HilbertOperator R} (hH : H.IsHermitian) {t Λ : ℝ} {r : ℕ}
    (ht : 0 ≤ t) (hr : 0 < r) (hHnorm : ‖H‖ ≤ Λ) :
    let τ : ℝ := t / (r : ℝ)
    let A : HilbertOperator R := (-((τ : ℂ) * Complex.I)) • H
    ‖star (timeEvolutionOp H τ) - 1 + A‖
      ≤ (1 / 2) * τ ^ 2 * Λ ^ 2 * Real.exp (t * Λ) := by
  dsimp
  simpa [sub_eq_add_neg] using
    star_timeEvolutionOp_generator_remainder_norm_le_global_exp hH ht hr hHnorm

open scoped Matrix.Norms.L2Operator in
/-- Concrete operator-norm budget for the first-order remainder of one
time-evolution conjugation step.  The superoperator norm itself remains an
abstract interface; this supplies the matrix-side analytic inputs to it. -/
def unitaryStepRemainderNormBudgetOperatorNorm {R : Register} [Nonempty R.Index]
    {H : HilbertOperator R} (hH : H.IsHermitian) {τ Λ : ℝ}
    (hτ : 0 ≤ τ) (hHnorm : ‖H‖ ≤ Λ) :
    let tail := (1 / 2) * τ ^ 2 * Λ ^ 2 * Real.exp (τ * Λ)
    UnitaryStepRemainderNormBudget opNorm H τ
      (tail * 1 + (1 + τ * Λ) * tail + (τ * Λ) * (τ * Λ)) := by
  dsimp
  have hΛ : 0 ≤ Λ := le_trans (norm_nonneg H) hHnorm
  have hHnorm' : opNorm H ≤ Λ := hHnorm
  have hscalar : ‖-((τ : ℂ) * Complex.I)‖ = τ := by
    rw [norm_neg, norm_mul]
    have hI : ‖Complex.I‖ = 1 := by
      have hsq : ‖Complex.I‖ ^ 2 = 1 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_I]
      nlinarith [norm_nonneg Complex.I]
    rw [hI, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ]
    ring
  have hA :
      opNorm (-((τ : ℂ) * Complex.I) • H) = τ * opNorm H := by
    rw [opNorm_smul, hscalar]
  refine
    { leftBudget := (1 / 2) * τ ^ 2 * Λ ^ 2 * Real.exp (τ * Λ)
      rightBudget := (1 / 2) * τ ^ 2 * Λ ^ 2 * Real.exp (τ * Λ)
      unitaryBudget := 1
      oneABudget := 1 + τ * Λ
      aBudget := τ * Λ
      left_bound := ?_
      right_bound := ?_
      unitary_bound := ?_
      one_add_generator_bound := ?_
      generator_bound := ?_
      leftBudget_nonneg := ?_
      oneABudget_nonneg := ?_
      aBudget_nonneg := ?_
      total_bound := by rfl }
  · simpa [opNorm, timeEvolutionOp, mul_comm] using
      timeEvolutionOp_generator_remainder_norm_le_budget H hτ hHnorm
  · simpa [opNorm, sub_eq_add_neg] using
      star_timeEvolutionOp_generator_remainder_norm_le_budget hH hτ hHnorm
  · exact (calc
      opNorm (star (timeEvolutionOp H τ)) = opNorm (timeEvolutionOp H τ) :=
        opNorm_star _
      _ = 1 := opNorm_timeEvolutionOp hH τ).le
  · calc
      opNorm (1 + (-((τ : ℂ) * Complex.I) • H))
          ≤ opNorm 1 + opNorm (-((τ : ℂ) * Complex.I) • H) :=
        opNorm_add_le _ _
      _ = 1 + τ * opNorm H := by rw [opNorm_one, hA]
      _ ≤ 1 + τ * Λ := by gcongr
  · dsimp
    rw [hA]
    exact mul_le_mul_of_nonneg_left hHnorm' hτ
  · positivity
  · positivity
  · positivity

/-- Uniform concrete operator-norm budgets for every sampled qDRIFT term and
for the probability-weighted ideal Hamiltonian. -/
def qdriftUnitaryStepRemainderBudgetsOperatorNorm {R : Register} [Nonempty R.Index]
    {ι : Type} [Fintype ι] (H : ι → HilbertOperator R) (p : ι → ℝ)
    (τ Λ : ℝ) (hprob : QDriftProbabilityWeights p)
    (hH : ∀ j, (H j).IsHermitian) (hτ : 0 ≤ τ)
    (hHnorm : ∀ j, opNorm (H j) ≤ Λ) :
    let tail := (1 / 2) * τ ^ 2 * Λ ^ 2 * Real.exp (τ * Λ)
    let budget := tail * 1 + (1 + τ * Λ) * tail + (τ * Λ) * (τ * Λ)
    (∀ j, UnitaryStepRemainderNormBudget opNorm (H j) τ budget) ×
      UnitaryStepRemainderNormBudget opNorm (weightedHamiltonianOp H p) τ budget := by
  dsimp
  constructor
  · intro j
    exact unitaryStepRemainderNormBudgetOperatorNorm (hH j) hτ (hHnorm j)
  · exact unitaryStepRemainderNormBudgetOperatorNorm
      (weightedHamiltonianOp_isHermitian H p hH) hτ
      (opNorm_weightedHamiltonianOp_le H p Λ hprob hHnorm)

/-- The concrete unitary-step budget is uniformly quadratic when the step size
is bounded by `T`; its exponential tail is controlled by `exp (T * Λ)`. -/
lemma unitaryStepRemainderBudget_operatorNorm_le_quadratic
    {τ T Λ : ℝ} (hτ : 0 ≤ τ) (hT : 0 ≤ T) (hτT : τ ≤ T) (hΛ : 0 ≤ Λ) :
    let tail := (1 / 2) * τ ^ 2 * Λ ^ 2 * Real.exp (τ * Λ)
    let budget := tail * 1 + (1 + τ * Λ) * tail + (τ * Λ) * (τ * Λ)
    budget ≤
      ((1 / 2) * Λ ^ 2 * Real.exp (T * Λ) * (2 + T * Λ) + Λ ^ 2) * τ ^ 2 := by
  dsimp
  have hτΛ : 0 ≤ τ * Λ := mul_nonneg hτ hΛ
  have hTΛ : 0 ≤ T * Λ := mul_nonneg hT hΛ
  have hτΛ_le : τ * Λ ≤ T * Λ :=
    mul_le_mul_of_nonneg_right hτT hΛ
  have hexp : Real.exp (τ * Λ) ≤ Real.exp (T * Λ) :=
    Real.exp_le_exp.mpr hτΛ_le
  have hlinear : 2 + τ * Λ ≤ 2 + T * Λ := by linarith
  have htail :
      Real.exp (τ * Λ) * (2 + τ * Λ)
        ≤ Real.exp (T * Λ) * (2 + T * Λ) :=
    mul_le_mul hexp hlinear (by linarith) (le_of_lt (Real.exp_pos _))
  have hscaled :
      (1 / 2) * Λ ^ 2 * (Real.exp (τ * Λ) * (2 + τ * Λ))
        ≤ (1 / 2) * Λ ^ 2 * (Real.exp (T * Λ) * (2 + T * Λ)) := by
    exact mul_le_mul_of_nonneg_left htail (by positivity)
  have hinner :
      (1 / 2) * Λ ^ 2 * Real.exp (τ * Λ) * (2 + τ * Λ) + Λ ^ 2
        ≤ (1 / 2) * Λ ^ 2 * Real.exp (T * Λ) * (2 + T * Λ) + Λ ^ 2 := by
    simpa [mul_assoc] using add_le_add_right hscaled (Λ ^ 2)
  calc
    (1 / 2) * τ ^ 2 * Λ ^ 2 * Real.exp (τ * Λ) * 1 +
          (1 + τ * Λ) * ((1 / 2) * τ ^ 2 * Λ ^ 2 * Real.exp (τ * Λ)) +
          (τ * Λ) * (τ * Λ)
        = τ ^ 2 *
            ((1 / 2) * Λ ^ 2 * Real.exp (τ * Λ) * (2 + τ * Λ) + Λ ^ 2) := by
          ring
    _ ≤ τ ^ 2 *
          ((1 / 2) * Λ ^ 2 * Real.exp (T * Λ) * (2 + T * Λ) + Λ ^ 2) :=
      mul_le_mul_of_nonneg_left hinner (sq_nonneg τ)
    _ = ((1 / 2) * Λ ^ 2 * Real.exp (T * Λ) * (2 + T * Λ) + Λ ^ 2) * τ ^ 2 := by
      ring

/-- Uniform constant used by the concrete operator-norm qDRIFT one-step and
global induced trace-norm bounds.  The parameter `T` is the total simulated
time appearing in the global exponential factor. -/
def qdriftOperatorNormConstant (T Λ : ℝ) : ℝ :=
  2 * ((1 / 2) * Λ ^ 2 * Real.exp (T * Λ) * (2 + T * Λ) + Λ ^ 2)

/-- A readable closed form for `qdriftOperatorNormConstant`. -/
lemma qdriftOperatorNormConstant_eq (T Λ : ℝ) :
    qdriftOperatorNormConstant T Λ =
      Λ ^ 2 * (Real.exp (T * Λ) * (2 + T * Λ) + 2) := by
  unfold qdriftOperatorNormConstant
  ring

/-- A coarse constant bound for the small-step regime `0 ≤ T * Λ ≤ 1`. -/
lemma qdriftOperatorNormConstant_le_small {T Λ : ℝ}
    (h_nonneg : 0 ≤ T * Λ) (h_small : T * Λ ≤ 1) :
    qdriftOperatorNormConstant T Λ ≤ (3 * Real.exp 1 + 2) * Λ ^ 2 := by
  rw [qdriftOperatorNormConstant_eq]
  have hexp : Real.exp (T * Λ) ≤ Real.exp 1 := Real.exp_le_exp.mpr h_small
  have hlin : 2 + T * Λ ≤ 3 := by linarith
  have hlin_nonneg : 0 ≤ 2 + T * Λ := by linarith
  have hprod :
      Real.exp (T * Λ) * (2 + T * Λ) ≤ Real.exp 1 * 3 := by
    exact mul_le_mul hexp hlin hlin_nonneg (le_of_lt (Real.exp_pos _))
  have hinner :
      Real.exp (T * Λ) * (2 + T * Λ) + 2 ≤ 3 * Real.exp 1 + 2 := by
    nlinarith [hprod]
  calc
    Λ ^ 2 * (Real.exp (T * Λ) * (2 + T * Λ) + 2)
        ≤ Λ ^ 2 * (3 * Real.exp 1 + 2) :=
          mul_le_mul_of_nonneg_left hinner (sq_nonneg Λ)
    _ = (3 * Real.exp 1 + 2) * Λ ^ 2 := by ring

/-- Concrete qDRIFT one-step quadratic bounds assembled from operator-norm
Hamiltonian budgets. -/
lemma qdriftOneStepQuadraticBoundsOperatorNorm {R : Register} [Nonempty R.Index]
    {ι : Type} [Fintype ι] (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (hmul : SuperOpTwoSidedMulNormControl superOpNorm opNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ T Λ : ℝ)
    (hprob : QDriftProbabilityWeights p)
    (hweights : QDriftWeightConditions scalarNorm p)
    (hH : ∀ j, (H j).IsHermitian) (hτ : 0 ≤ τ) (hT : 0 ≤ T)
    (hτT : τ ≤ T) (hΛ : 0 ≤ Λ)
    (hHnorm : ∀ j, opNorm (H j) ≤ Λ) :
    let tail := (1 / 2) * τ ^ 2 * Λ ^ 2 * Real.exp (τ * Λ)
    let budget := tail * 1 + (1 + τ * Λ) * tail + (τ * Λ) * (τ * Λ)
    let constant := qdriftOperatorNormConstant T Λ
    QDriftOneStepQuadraticBounds superOpNorm scalarNorm H p τ budget budget constant := by
  dsimp
  refine qdriftOneStepQuadraticBounds_of_unitaryStepBudgets
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm)
    (matrixNorm := opNorm) (hnorm := hnorm) (hmul := hmul)
    (H := H) (p := p) (τ := τ) ?_ ?_ ?_ ?_ ?_
    hweights.scalar_weights_bound hweights.scalar_nonneg ?_ ?_
  · exact (qdriftUnitaryStepRemainderBudgetsOperatorNorm H p τ Λ hprob hH hτ hHnorm).1
  · exact (qdriftUnitaryStepRemainderBudgetsOperatorNorm H p τ Λ hprob hH hτ hHnorm).2
  · positivity
  · have hbudget :=
      unitaryStepRemainderBudget_operatorNorm_le_quadratic hτ hT hτT hΛ
    dsimp [qdriftOperatorNormConstant] at *
    nlinarith

/-- Abstract analytic budget for a second-order exponential remainder.

For a concrete induced superoperator norm this is the point where one supplies
the Banach-algebra estimate
`‖exp A - 1 - A‖ ≤ ‖A‖^2 * exp ‖A‖`. -/
structure ExpSecondOrderRemainderBudget {R : Register}
    (superOpNorm : SuperOp R → ℝ) (expRemainder : SuperOp R) (Λ : ℝ) : Prop where
  remainder_bound : superOpNorm expRemainder ≤ Λ

/-- Package the usual analytic estimate
`‖remainder‖ ≤ analyticNorm^2 * exp analyticNorm` as an abstract qDRIFT
remainder budget. -/
lemma ExpSecondOrderRemainderBudget.of_exp_tail_bound
    {R : Register}
    (superOpNorm : SuperOp R → ℝ) (expRemainder : SuperOp R)
    (analyticNorm Λ : ℝ)
    (hrem : superOpNorm expRemainder ≤ analyticNorm ^ 2 * Real.exp analyticNorm)
    (hbudget : analyticNorm ^ 2 * Real.exp analyticNorm ≤ Λ) :
    ExpSecondOrderRemainderBudget superOpNorm expRemainder Λ where
  remainder_bound := le_trans hrem hbudget

/-- Pull a continuous-operator norm estimate back to the algebraic
superoperator remainder interface. -/
lemma ExpSecondOrderRemainderBudget.of_continuous_pullback_bound
    {R : Register}
    (continuousNorm : (HilbertOperator R →L[ℂ] HilbertOperator R) → ℝ)
    (expRemainder : SuperOp R) (Λ : ℝ)
    (hrem : continuousNorm (continuousSuperOp expRemainder) ≤ Λ) :
    ExpSecondOrderRemainderBudget (continuousSuperOpNorm continuousNorm)
      expRemainder Λ where
  remainder_bound := hrem

/-- Turn a second-order exponential remainder estimate into the quadratic
budget format used by the global qDRIFT theorem, with step size `τ = 1`. -/
lemma expSecondOrderRemainderBudget.to_quadratic_budget_one
    {R : Register}
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (expRemainder : SuperOp R) (Λ : ℝ)
    (hscalar_one_nonneg : 0 ≤ scalarNorm ((1 : ℂ) ^ 2))
    (hbudget : ExpSecondOrderRemainderBudget superOpNorm expRemainder Λ) :
    QuadraticRemainderNormBudget superOpNorm scalarNorm 1 Λ
      expRemainder where
  quadratic := by
    use expRemainder
    simp
  remainder_bound := by
    intro Ψ hΨ
    have hΨ' : expRemainder = Ψ := by
      simpa using hΨ
    simpa [← hΨ'] using hbudget.remainder_bound
  scalar_quadratic_nonneg := hscalar_one_nonneg

/-- Final abstract qDRIFT global error bound using a scalar-norm square bound
instead of an explicit scale hypothesis. -/
lemma qdrift_global_error_bound_of_hybrid_quadratic_budgets_of_scalar_square
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ)
    (totalError : QDriftTotalError R) (t Λ : ℝ) (steps : ℕ)
    (pre post : Fin steps → SuperOp R)
    (hsteps : steps ≠ 0)
    (hΛ : 0 ≤ Λ)
    (hscalar_sq :
      scalarNorm (((t / (steps : ℝ) : ℝ) : ℂ) ^ 2)
        ≤ (t / (steps : ℝ)) ^ 2)
    (hdecomp :
      totalError = ∑ k,
        qdriftHybridStepErrorFamily pre post H p (t / (steps : ℝ)) k)
    (hbudget : ∀ k,
      QuadraticRemainderNormBudget superOpNorm scalarNorm (t / (steps : ℝ)) Λ
        (qdriftHybridStepErrorFamily pre post H p (t / (steps : ℝ)) k)) :
    superOpNorm totalError ≤ (t ^ 2 / (steps : ℝ)) * Λ :=
  qdrift_global_error_bound_of_hybrid_quadratic_budgets
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
    (H := H) (p := p) (totalError := totalError)
    (t := t) (Λ := Λ) (steps := steps) (pre := pre) (post := post)
    hdecomp hbudget
    (qdrift_global_error_scale_le
      (scalarNorm := scalarNorm) (t := t) (Λ := Λ) (steps := steps)
      hsteps hΛ hscalar_sq)

/-- Global error bound for an explicit composition-power difference.  This is
the telescoping specialization of the hybrid bound. -/
lemma qdrift_global_error_bound_of_power_diff_quadratic_budgets
    {R : Register}
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (U E : SuperOp R) (t Λ : ℝ) (steps : ℕ)
    (hsteps : steps ≠ 0)
    (hΛ : 0 ≤ Λ)
    (hscalar_sq :
      scalarNorm (((t / (steps : ℝ) : ℝ) : ℂ) ^ 2)
        ≤ (t / (steps : ℝ)) ^ 2)
    (hbudget : ∀ k : Fin steps,
      QuadraticRemainderNormBudget superOpNorm scalarNorm (t / (steps : ℝ)) Λ
        (superOpComp (superOpPower U (steps - 1 - (k : ℕ)))
          (superOpComp (U - E) (superOpPower E (k : ℕ))))) :
    superOpNorm (superOpPower U steps - superOpPower E steps)
      ≤ (t ^ 2 / (steps : ℝ)) * Λ := by
  have hdecomp :
      superOpPower U steps - superOpPower E steps =
        ∑ k : Fin steps,
          superOpComp (superOpPower U (steps - 1 - k))
            (superOpComp (U - E) (superOpPower E k)) := by
    rw [superOpPower_diff_eq_sum]
    exact (Fin.sum_univ_eq_sum_range
      (fun k : ℕ =>
        superOpComp (superOpPower U (steps - 1 - k))
          (superOpComp (U - E) (superOpPower E k))) steps).symm
  calc
    superOpNorm (superOpPower U steps - superOpPower E steps)
        ≤ (steps : ℝ) * (scalarNorm (((t / (steps : ℝ) : ℝ) : ℂ) ^ 2) * Λ) :=
      qdriftTotalError_norm_le_of_quadratic_step_budgets
      (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
      (totalError := superOpPower U steps - superOpPower E steps)
      (steps := steps) (τ := t / (steps : ℝ)) (Λ := Λ)
      (stepError := fun k =>
        superOpComp (superOpPower U (steps - 1 - k))
          (superOpComp (U - E) (superOpPower E k)))
      hdecomp hbudget
    _ ≤ (t ^ 2 / (steps : ℝ)) * Λ :=
      qdrift_global_error_scale_le
      (scalarNorm := scalarNorm) (t := t) (Λ := Λ) (steps := steps)
      hsteps hΛ hscalar_sq

namespace QDriftTotalErrorBound

/-- Statement of the abstract qDRIFT total error bound after `steps` steps. -/
def Statement {R : Register}
    (superOpNorm : SuperOp R → ℝ) (totalError : QDriftTotalError R)
    (constant t : ℝ) (steps : ℕ) : Prop :=
  qdriftTotalErrorStatement superOpNorm totalError constant t steps

/-- Packaged assumptions for the abstract qDRIFT total error bound. -/
structure Assumptions {R : Register}
    (superOpNorm : SuperOp R → ℝ) (totalError : QDriftTotalError R)
    (constant t : ℝ) (steps : ℕ) : Prop where
  total_budget : superOpNorm totalError ≤ qdriftTotalQuadraticBudget constant t steps

/-- Packaged assumptions using an explicit sum of identical one-step budgets. -/
structure SummedOneStepAssumptions {R : Register}
    (superOpNorm : SuperOp R → ℝ) (totalError : QDriftTotalError R)
    (constant t : ℝ) (steps : ℕ) : Prop where
  summed_one_step_budget :
    superOpNorm totalError
      ≤ (steps : ℝ) * qdriftOneStepQuadraticBudget constant t steps

/-- Packaged assumptions using a `Fin steps` sum of identical one-step budgets. -/
structure FinSumOneStepAssumptions {R : Register}
    (superOpNorm : SuperOp R → ℝ) (totalError : QDriftTotalError R)
    (constant t : ℝ) (steps : ℕ) : Prop where
  fin_sum_one_step_budget :
    superOpNorm totalError
      ≤ ∑ _k : Fin steps, qdriftOneStepQuadraticBudget constant t steps

/-- Packaged assumptions using possibly different per-step budgets. -/
structure FinSumStepBudgetAssumptions {R : Register}
    (superOpNorm : SuperOp R → ℝ) (totalError : QDriftTotalError R)
    (constant t : ℝ) (steps : ℕ) (stepBudget : Fin steps → ℝ) : Prop where
  total_le_sum_step_budgets : superOpNorm totalError ≤ ∑ k, stepBudget k
  step_budget_le : ∀ k, stepBudget k ≤ qdriftOneStepQuadraticBudget constant t steps

/-- Packaged assumptions using an explicit family of per-step error superoperators. -/
structure StepErrorFamilyAssumptions {R : Register}
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (totalError : QDriftTotalError R) (constant t : ℝ) (steps : ℕ)
    (stepError : Fin steps → SuperOp R) : Prop where
  norm_properties : SuperOpNormProperties superOpNorm scalarNorm
  total_error_decomposition : totalError = ∑ k, stepError k
  step_error_bound : ∀ k, superOpNorm (stepError k)
    ≤ qdriftOneStepQuadraticBudget constant t steps

/-- Packaged hybrid-argument assumptions for qDRIFT total error accumulation. -/
structure HybridArgumentAssumptions {R : Register}
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (totalError : QDriftTotalError R) (constant t : ℝ) (steps : ℕ)
    (propagatedStepError : Fin steps → SuperOp R) : Prop where
  norm_properties : SuperOpNormProperties superOpNorm scalarNorm
  hybrid_decomposition : totalError = ∑ k, propagatedStepError k
  hybrid_step_bound : ∀ k, superOpNorm (propagatedStepError k)
    ≤ qdriftOneStepQuadraticBudget constant t steps

/-- Hybrid-argument assumptions using explicit pre- and post-propagation maps. -/
structure HybridFamilyAssumptions {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (H : ι → HilbertOperator R) (p : ι → ℝ)
    (totalError : QDriftTotalError R) (constant t : ℝ) (steps : ℕ)
    (pre post : Fin steps → SuperOp R) : Prop where
  norm_properties : SuperOpNormProperties superOpNorm scalarNorm
  hybrid_decomposition :
    totalError = ∑ k, qdriftHybridStepErrorFamily pre post H p (t / (steps : ℝ)) k
  hybrid_step_bound : ∀ k,
    superOpNorm (qdriftHybridStepErrorFamily pre post H p (t / (steps : ℝ)) k)
      ≤ qdriftOneStepQuadraticBudget constant t steps

/-- Hybrid-argument assumptions with nonexpansive propagation maps. -/
structure NonexpansiveHybridFamilyAssumptions {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (H : ι → HilbertOperator R) (p : ι → ℝ)
    (totalError : QDriftTotalError R) (constant t : ℝ) (steps : ℕ)
    (pre post : Fin steps → SuperOp R) : Prop where
  norm_properties : SuperOpNormProperties superOpNorm scalarNorm
  hybrid_decomposition :
    totalError = ∑ k, qdriftHybridStepErrorFamily pre post H p (t / (steps : ℝ)) k
  pre_nonexpansive : ∀ k, SuperOpLeftNonexpansive superOpNorm (pre k)
  post_nonexpansive : ∀ k, SuperOpRightNonexpansive superOpNorm (post k)
  one_step_error_bound :
    superOpNorm (qdriftStepErrorSuperOp H p (t / (steps : ℝ)))
      ≤ qdriftOneStepQuadraticBudget constant t steps

/-- Abstract qDRIFT total error bound from a packaged total-budget estimate. -/
lemma bound {R : Register}
    (superOpNorm : SuperOp R → ℝ) (totalError : QDriftTotalError R)
    (constant t : ℝ) (steps : ℕ)
    (hassumptions : Assumptions superOpNorm totalError constant t steps) :
    Statement superOpNorm totalError constant t steps :=
  qdriftTotalError_norm_le_of_budget
    (superOpNorm := superOpNorm) (totalError := totalError)
    (constant := constant) (t := t) (steps := steps)
    hassumptions.total_budget

/-- Abstract qDRIFT total error bound from summed one-step budget assumptions. -/
lemma bound_of_summed_one_step_assumptions {R : Register}
    (superOpNorm : SuperOp R → ℝ) (totalError : QDriftTotalError R)
    (constant t : ℝ) (steps : ℕ)
    (hassumptions :
      SummedOneStepAssumptions superOpNorm totalError constant t steps) :
    Statement superOpNorm totalError constant t steps :=
  qdriftTotalError_norm_le_of_summed_one_step_budget
    (superOpNorm := superOpNorm) (totalError := totalError)
    (constant := constant) (t := t) (steps := steps)
    hassumptions.summed_one_step_budget

/-- Abstract qDRIFT total error bound from a `Fin steps` sum of one-step budgets. -/
lemma bound_of_fin_sum_one_step_assumptions {R : Register}
    (superOpNorm : SuperOp R → ℝ) (totalError : QDriftTotalError R)
    (constant t : ℝ) (steps : ℕ)
    (hassumptions :
      FinSumOneStepAssumptions superOpNorm totalError constant t steps) :
    Statement superOpNorm totalError constant t steps :=
  qdriftTotalError_norm_le_of_fin_sum_one_step_budget
    (superOpNorm := superOpNorm) (totalError := totalError)
    (constant := constant) (t := t) (steps := steps)
    hassumptions.fin_sum_one_step_budget

/-- Abstract qDRIFT total error bound from per-step budget assumptions. -/
lemma bound_of_fin_sum_step_budget_assumptions {R : Register}
    (superOpNorm : SuperOp R → ℝ) (totalError : QDriftTotalError R)
    (constant t : ℝ) (steps : ℕ) (stepBudget : Fin steps → ℝ)
    (hassumptions :
      FinSumStepBudgetAssumptions superOpNorm totalError constant t steps stepBudget) :
    Statement superOpNorm totalError constant t steps :=
  qdriftTotalError_norm_le_of_fin_sum_step_budgets
    (superOpNorm := superOpNorm) (totalError := totalError)
    (constant := constant) (t := t) (steps := steps)
    (stepBudget := stepBudget)
    hassumptions.total_le_sum_step_budgets hassumptions.step_budget_le

/-- Abstract qDRIFT total error bound from a per-step error family. -/
lemma bound_of_step_error_family_assumptions {R : Register}
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (totalError : QDriftTotalError R) (constant t : ℝ) (steps : ℕ)
    (stepError : Fin steps → SuperOp R)
    (hassumptions :
      StepErrorFamilyAssumptions superOpNorm scalarNorm totalError constant t steps
        stepError) :
    Statement superOpNorm totalError constant t steps :=
  qdriftTotalError_norm_le_of_step_error_family
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm)
    (hnorm := hassumptions.norm_properties)
    (totalError := totalError)
    (constant := constant) (t := t) (steps := steps)
    (stepError := stepError)
    hassumptions.total_error_decomposition hassumptions.step_error_bound

/-- Abstract qDRIFT total error bound from a hybrid-argument decomposition. -/
lemma bound_of_hybrid_argument {R : Register}
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (totalError : QDriftTotalError R) (constant t : ℝ) (steps : ℕ)
    (propagatedStepError : Fin steps → SuperOp R)
    (hassumptions :
      HybridArgumentAssumptions superOpNorm scalarNorm totalError constant t steps
        propagatedStepError) :
    Statement superOpNorm totalError constant t steps :=
  qdriftTotalError_norm_le_of_step_error_family
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm)
    (hnorm := hassumptions.norm_properties)
    (totalError := totalError)
    (constant := constant) (t := t) (steps := steps)
    (stepError := propagatedStepError)
    hassumptions.hybrid_decomposition hassumptions.hybrid_step_bound

/-- Abstract qDRIFT total error bound from explicit hybrid propagation maps. -/
lemma bound_of_hybrid_family {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (H : ι → HilbertOperator R) (p : ι → ℝ)
    (totalError : QDriftTotalError R) (constant t : ℝ) (steps : ℕ)
    (pre post : Fin steps → SuperOp R)
    (hassumptions :
      HybridFamilyAssumptions superOpNorm scalarNorm H p totalError constant t steps
        pre post) :
    Statement superOpNorm totalError constant t steps :=
  qdriftTotalError_norm_le_of_hybrid_family
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm)
    (hnorm := hassumptions.norm_properties)
    (H := H) (p := p)
    (totalError := totalError) (constant := constant) (t := t) (steps := steps)
    (pre := pre) (post := post)
    hassumptions.hybrid_decomposition hassumptions.hybrid_step_bound

/-- Abstract qDRIFT total error bound from nonexpansive hybrid propagation maps. -/
lemma bound_of_nonexpansive_hybrid_family {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (H : ι → HilbertOperator R) (p : ι → ℝ)
    (totalError : QDriftTotalError R) (constant t : ℝ) (steps : ℕ)
    (pre post : Fin steps → SuperOp R)
    (hassumptions :
      NonexpansiveHybridFamilyAssumptions superOpNorm scalarNorm H p totalError
        constant t steps pre post) :
    Statement superOpNorm totalError constant t steps :=
  qdriftTotalError_norm_le_of_hybrid_family_nonexpansive
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm)
    (hnorm := hassumptions.norm_properties)
    (H := H) (p := p)
    (totalError := totalError) (constant := constant) (t := t) (steps := steps)
    (pre := pre) (post := post)
    hassumptions.hybrid_decomposition
    hassumptions.pre_nonexpansive
    hassumptions.post_nonexpansive
    hassumptions.one_step_error_bound

/-- Abstract qDRIFT total error bound from nonexpansive hybrid propagation and
two-sided unitary-step remainder budgets. -/
lemma bound_of_nonexpansive_hybrid_family_unitaryStepBudgets
    {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (matrixNorm : HilbertOperator R → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (hmul : SuperOpTwoSidedMulNormControl superOpNorm matrixNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ)
    (totalError : QDriftTotalError R) (constant t : ℝ) (steps : ℕ)
    (pre post : Fin steps → SuperOp R)
    (hweights : QDriftWeightConditions scalarNorm p)
    (termBound idealBudget : ℝ)
    (hterms : ∀ j,
      UnitaryStepRemainderNormBudget matrixNorm (H j) (t / (steps : ℝ))
        termBound)
    (hideal :
      UnitaryStepRemainderNormBudget matrixNorm (weightedHamiltonianOp H p)
        (t / (steps : ℝ)) idealBudget)
    (hterm_nonneg : 0 ≤ termBound)
    (hquadratic : termBound + idealBudget ≤ constant * (t / (steps : ℝ)) ^ 2)
    (hdecomp :
      totalError =
        ∑ k, qdriftHybridStepErrorFamily pre post H p (t / (steps : ℝ)) k)
    (hpre : ∀ k, SuperOpLeftNonexpansive superOpNorm (pre k))
    (hpost : ∀ k, SuperOpRightNonexpansive superOpNorm (post k)) :
    Statement superOpNorm totalError constant t steps := by
  apply qdriftTotalError_norm_le_of_hybrid_family_nonexpansive
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
    (H := H) (p := p)
    (totalError := totalError) (constant := constant) (t := t) (steps := steps)
    (pre := pre) (post := post)
    hdecomp hpre hpost
  exact qdriftStepErrorSuperOp_norm_le_time_sq_div_steps_sq_of_weight_conditions
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
    (H := H) (p := p) (t := t) (steps := steps)
    (hweights := hweights)
    (termBound := termBound) (idealBudget := idealBudget)
    (constant := constant)
    (qdriftOneStepQuadraticBounds_of_unitaryStepBudgets
      (superOpNorm := superOpNorm) (scalarNorm := scalarNorm)
      (matrixNorm := matrixNorm) (hnorm := hnorm) (hmul := hmul)
      (H := H) (p := p) (τ := t / (steps : ℝ))
      (termBound := termBound) (idealBudget := idealBudget)
      (constant := constant)
      hterms hideal hweights.scalar_weights_bound hweights.scalar_nonneg
      hterm_nonneg hquadratic)

end QDriftTotalErrorBound

namespace QDriftOneStepErrorBound

/-- Statement of the abstract qDRIFT one-step error bound at step size `t / steps`. -/
def Statement {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (t : ℝ) (steps : ℕ)
    (constant : ℝ) : Prop :=
  superOpNorm (qdriftStepErrorSuperOp H p (t / (steps : ℝ)))
    ≤ constant * t ^ 2 / (steps : ℝ) ^ 2

/-- Packaged assumptions for the abstract qDRIFT one-step error bound. -/
structure Assumptions {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (t : ℝ) (steps : ℕ)
    (termBound idealBudget constant : ℝ) : Prop where
  norm_properties : SuperOpNormProperties superOpNorm scalarNorm
  weight_conditions : QDriftWeightConditions scalarNorm p
  quadratic_bounds :
    QDriftOneStepQuadraticBounds superOpNorm scalarNorm H p
      (t / (steps : ℝ)) termBound idealBudget constant

/-- Abstract qDRIFT one-step error bound from packaged weight and remainder assumptions. -/
lemma bound {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (t : ℝ) (steps : ℕ)
    (hweights : QDriftWeightConditions scalarNorm p)
    (termBound idealBudget constant : ℝ)
    (hbounds :
      QDriftOneStepQuadraticBounds superOpNorm scalarNorm H p
        (t / (steps : ℝ)) termBound idealBudget constant) :
    Statement superOpNorm H p t steps constant :=
  qdriftStepErrorSuperOp_norm_le_time_sq_div_steps_sq_of_weight_conditions
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
    (H := H) (p := p) (t := t) (steps := steps)
    (hweights := hweights)
    (termBound := termBound) (idealBudget := idealBudget)
    (constant := constant) hbounds

/-- Abstract qDRIFT one-step error bound from one packaged assumptions object. -/
lemma bound_of_assumptions {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (t : ℝ) (steps : ℕ)
    (termBound idealBudget constant : ℝ)
    (hassumptions :
      Assumptions superOpNorm scalarNorm H p t steps termBound idealBudget constant) :
    Statement superOpNorm H p t steps constant :=
  bound
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm)
    (hnorm := hassumptions.norm_properties)
    (H := H) (p := p) (t := t) (steps := steps)
    (hweights := hassumptions.weight_conditions)
    (termBound := termBound) (idealBudget := idealBudget)
    (constant := constant) hassumptions.quadratic_bounds

/-- Abstract qDRIFT one-step error bound from real probability weights. -/
lemma bound_of_probability_weights {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (t : ℝ) (steps : ℕ)
    (hscalar : ∀ j, scalarNorm (p j : ℂ) = p j)
    (hprob : QDriftProbabilityWeights p)
    (termBound idealBudget constant : ℝ)
    (hbounds :
      QDriftOneStepQuadraticBounds superOpNorm scalarNorm H p
        (t / (steps : ℝ)) termBound idealBudget constant) :
    Statement superOpNorm H p t steps constant :=
  qdriftStepErrorSuperOp_norm_le_time_sq_div_steps_sq_of_probability_weights
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
    (H := H) (p := p) (t := t) (steps := steps)
    (hscalar := hscalar) (hprob := hprob)
    (termBound := termBound) (idealBudget := idealBudget)
    (constant := constant) hbounds

/-- One-step qDRIFT error bound from two-sided unitary-step remainder budgets. -/
lemma bound_of_unitaryStepBudgets {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (matrixNorm : HilbertOperator R → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (hmul : SuperOpTwoSidedMulNormControl superOpNorm matrixNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (t : ℝ) (steps : ℕ)
    (hweights : QDriftWeightConditions scalarNorm p)
    (termBound idealBudget constant : ℝ)
    (hterms : ∀ j,
      UnitaryStepRemainderNormBudget matrixNorm (H j) (t / (steps : ℝ))
        termBound)
    (hideal :
      UnitaryStepRemainderNormBudget matrixNorm (weightedHamiltonianOp H p)
        (t / (steps : ℝ)) idealBudget)
    (hterm_nonneg : 0 ≤ termBound)
    (hquadratic : termBound + idealBudget ≤ constant * (t / (steps : ℝ)) ^ 2) :
    Statement superOpNorm H p t steps constant :=
  bound
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
    (H := H) (p := p) (t := t) (steps := steps)
    (hweights := hweights)
    (termBound := termBound) (idealBudget := idealBudget)
    (constant := constant)
    (qdriftOneStepQuadraticBounds_of_unitaryStepBudgets
      (superOpNorm := superOpNorm) (scalarNorm := scalarNorm)
      (matrixNorm := matrixNorm) (hnorm := hnorm) (hmul := hmul)
      (H := H) (p := p) (τ := t / (steps : ℝ))
      (termBound := termBound) (idealBudget := idealBudget)
      (constant := constant)
      hterms hideal hweights.scalar_weights_bound hweights.scalar_nonneg
      hterm_nonneg hquadratic)

/-- One-step qDRIFT error bound with the concrete operator-norm remainder
budget and the uniform global exponential factor `exp (t * Λ)`. -/
lemma bound_of_operatorNorm {R : Register} [Nonempty R.Index]
    {ι : Type} [Fintype ι] (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (hmul : SuperOpTwoSidedMulNormControl superOpNorm opNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ) (t Λ : ℝ) (steps : ℕ)
    (hprob : QDriftProbabilityWeights p)
    (hweights : QDriftWeightConditions scalarNorm p)
    (hH : ∀ j, (H j).IsHermitian) (ht : 0 ≤ t) (hsteps : steps ≠ 0)
    (hΛ : 0 ≤ Λ) (hHnorm : ∀ j, opNorm (H j) ≤ Λ) :
    Statement superOpNorm H p t steps (qdriftOperatorNormConstant t Λ) := by
  have hsteps_nat : 0 < steps := Nat.pos_of_ne_zero hsteps
  have hsteps_pos : 0 < (steps : ℝ) := by exact_mod_cast hsteps_nat
  have hstep_nonneg : 0 ≤ t / (steps : ℝ) := div_nonneg ht hsteps_pos.le
  have hsteps_one : (1 : ℝ) ≤ (steps : ℝ) := by exact_mod_cast hsteps_nat
  have hstep_le : t / (steps : ℝ) ≤ t := by
    rw [div_le_iff₀ hsteps_pos]
    simpa using mul_le_mul_of_nonneg_left hsteps_one ht
  let tail := (1 / 2) * (t / (steps : ℝ)) ^ 2 * Λ ^ 2 *
    Real.exp ((t / (steps : ℝ)) * Λ)
  let budget := tail * 1 + (1 + (t / (steps : ℝ)) * Λ) * tail +
    ((t / (steps : ℝ)) * Λ) * ((t / (steps : ℝ)) * Λ)
  let constant := qdriftOperatorNormConstant t Λ
  change Statement superOpNorm H p t steps constant
  exact bound
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
    (H := H) (p := p) (t := t) (steps := steps)
    (hweights := hweights)
    (termBound := budget) (idealBudget := budget) (constant := constant)
    (qdriftOneStepQuadraticBoundsOperatorNorm
      (superOpNorm := superOpNorm) (scalarNorm := scalarNorm)
      (hnorm := hnorm) (hmul := hmul)
      (H := H) (p := p) (τ := t / (steps : ℝ)) (T := t) (Λ := Λ)
      hprob hweights hH hstep_nonneg ht hstep_le hΛ hHnorm)

/-- One-step qDRIFT error bound specialized to the induced trace norm. -/
lemma bound_of_inducedTraceNorm_operatorNorm {R : Register} [Nonempty R.Index]
    {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (t Λ : ℝ) (steps : ℕ)
    (hprob : QDriftProbabilityWeights p)
    (hH : ∀ j, (H j).IsHermitian) (ht : 0 ≤ t) (hsteps : steps ≠ 0)
    (hΛ : 0 ≤ Λ) (hHnorm : ∀ j, opNorm (H j) ≤ Λ) :
    Statement inducedTraceNorm H p t steps (qdriftOperatorNormConstant t Λ) :=
  bound_of_operatorNorm
    (superOpNorm := inducedTraceNorm) (scalarNorm := fun c : ℂ => ‖c‖)
    (hnorm := inducedTraceNorm_properties)
    (hmul := inducedTraceNorm_twoSidedMul_control_operatorNorm)
    (H := H) (p := p) (t := t) (Λ := Λ) (steps := steps)
    hprob (QDriftWeightConditions.of_probability_weights_norm p hprob)
    hH ht hsteps hΛ hHnorm

end QDriftOneStepErrorBound

namespace QDriftTotalErrorBound

/-- Global qDRIFT error bound using the concrete operator-norm one-step
estimate.  Only the hybrid decomposition and propagation nonexpansivity remain
as superoperator-level assumptions. -/
lemma bound_of_operatorNorm {R : Register} [Nonempty R.Index]
    {ι : Type} [Fintype ι] (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (hmul : SuperOpTwoSidedMulNormControl superOpNorm opNorm)
    (H : ι → HilbertOperator R) (p : ι → ℝ)
    (totalError : QDriftTotalError R) (t Λ : ℝ) (steps : ℕ)
    (pre post : Fin steps → SuperOp R)
    (hprob : QDriftProbabilityWeights p)
    (hweights : QDriftWeightConditions scalarNorm p)
    (hH : ∀ j, (H j).IsHermitian) (ht : 0 ≤ t) (hsteps : steps ≠ 0)
    (hΛ : 0 ≤ Λ) (hHnorm : ∀ j, opNorm (H j) ≤ Λ)
    (hdecomp :
      totalError =
        ∑ k, qdriftHybridStepErrorFamily pre post H p (t / (steps : ℝ)) k)
    (hpre : ∀ k, SuperOpLeftNonexpansive superOpNorm (pre k))
    (hpost : ∀ k, SuperOpRightNonexpansive superOpNorm (post k)) :
    Statement superOpNorm totalError (qdriftOperatorNormConstant t Λ) t steps := by
  apply qdriftTotalError_norm_le_of_hybrid_family_nonexpansive
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm) (hnorm := hnorm)
    (H := H) (p := p) (totalError := totalError)
    (constant := qdriftOperatorNormConstant t Λ)
    (t := t) (steps := steps) (pre := pre) (post := post)
    hdecomp hpre hpost
  exact QDriftOneStepErrorBound.bound_of_operatorNorm
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm)
    (hnorm := hnorm) (hmul := hmul)
    (H := H) (p := p) (t := t) (Λ := Λ) (steps := steps)
    hprob hweights hH ht hsteps hΛ hHnorm

/-- Global hybrid qDRIFT error bound specialized to the induced trace norm.
The hybrid propagators are supplied as pointwise trace-norm nonexpansive maps. -/
lemma bound_of_inducedTraceNorm_operatorNorm {R : Register} [Nonempty R.Index]
    {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ)
    (totalError : QDriftTotalError R) (t Λ : ℝ) (steps : ℕ)
    (pre post : Fin steps → SuperOp R)
    (hprob : QDriftProbabilityWeights p)
    (hH : ∀ j, (H j).IsHermitian) (ht : 0 ≤ t) (hsteps : steps ≠ 0)
    (hΛ : 0 ≤ Λ) (hHnorm : ∀ j, opNorm (H j) ≤ Λ)
    (hdecomp :
      totalError =
        ∑ k, qdriftHybridStepErrorFamily pre post H p (t / (steps : ℝ)) k)
    (hpre : ∀ k, TraceNormNonexpansive (pre k))
    (hpost : ∀ k, TraceNormNonexpansive (post k)) :
    Statement inducedTraceNorm totalError (qdriftOperatorNormConstant t Λ) t steps := by
  exact bound_of_operatorNorm
    (superOpNorm := inducedTraceNorm) (scalarNorm := fun c : ℂ => ‖c‖)
    (hnorm := inducedTraceNorm_properties)
    (hmul := inducedTraceNorm_twoSidedMul_control_operatorNorm)
    (H := H) (p := p) (totalError := totalError) (t := t) (Λ := Λ)
    (steps := steps) (pre := pre) (post := post)
    hprob (QDriftWeightConditions.of_probability_weights_norm p hprob)
    hH ht hsteps hΛ hHnorm hdecomp
    (fun k => traceNormNonexpansive_left_inducedTraceNorm_nonexpansive (hpre k))
    (fun k => traceNormNonexpansive_right_inducedTraceNorm_nonexpansive (hpost k))

end QDriftTotalErrorBound

namespace QDriftOneStepQuadraticRemainder

/-- Algebraic statement that the qDRIFT one-step error has no constant or
first-order part in the step size. -/
def Statement {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ) : Prop :=
  IsQuadraticRemainder τ (qdriftStepErrorSuperOp H p τ)

/-- Packaged assumptions for the algebraic qDRIFT one-step quadratic remainder. -/
structure Assumptions {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ) : Prop where
  weight_sum : ∑ j, (p j : ℂ) = 1
  sampled_unitary_remainders :
    ∀ j, IsQuadraticRemainder τ (unitaryStepRemainderSuperOp (H j) τ)
  ideal_remainder :
    IsQuadraticRemainder τ
      (unitaryStepRemainderSuperOp (weightedHamiltonianOp H p) τ)

/-- Algebraic qDRIFT one-step quadratic remainder from explicit Taylor-style
unitary remainder assumptions. -/
lemma bound {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hp : ∑ j, (p j : ℂ) = 1)
    (hunit : ∀ j, IsQuadraticRemainder τ (unitaryStepRemainderSuperOp (H j) τ))
    (hideal :
      IsQuadraticRemainder τ
        (unitaryStepRemainderSuperOp (weightedHamiltonianOp H p) τ)) :
    Statement H p τ :=
  qdriftStepErrorSuperOp_isQuadraticRemainder H p τ hp hunit hideal

/-- Algebraic qDRIFT one-step quadratic remainder from one packaged assumptions
object. -/
lemma bound_of_assumptions {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ) (τ : ℝ)
    (hassumptions : Assumptions H p τ) :
    Statement H p τ :=
  bound H p τ
    hassumptions.weight_sum
    hassumptions.sampled_unitary_remainders
    hassumptions.ideal_remainder

end QDriftOneStepQuadraticRemainder

namespace QDriftHybridQuadraticRemainder

/-- Algebraic statement that a hybrid qDRIFT total error is quadratic in the
single step size used by each hybrid summand. -/
def Statement {R : Register}
    (totalError : QDriftTotalError R) (τ : ℝ) : Prop :=
  IsQuadraticRemainder τ totalError

/-- Packaged assumptions for the algebraic hybrid qDRIFT quadratic remainder. -/
structure Assumptions {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ)
    (totalError : QDriftTotalError R) (τ : ℝ) (steps : ℕ)
    (pre post : Fin steps → SuperOp R) : Prop where
  hybrid_decomposition :
    totalError = ∑ k, qdriftHybridStepErrorFamily pre post H p τ k
  one_step_quadratic :
    IsQuadraticRemainder τ (qdriftStepErrorSuperOp H p τ)

/-- The hybrid argument preserves the algebraic quadratic-remainder shape. -/
lemma bound {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ)
    (totalError : QDriftTotalError R) (τ : ℝ) (steps : ℕ)
    (pre post : Fin steps → SuperOp R)
    (hdecomp :
      totalError = ∑ k, qdriftHybridStepErrorFamily pre post H p τ k)
    (hstep : IsQuadraticRemainder τ (qdriftStepErrorSuperOp H p τ)) :
    Statement totalError τ :=
  qdriftTotalError_isQuadraticRemainder_of_hybrid_propagation
    (H := H) (p := p) (totalError := totalError) (τ := τ)
    (steps := steps) (pre := pre) (post := post) hdecomp hstep

/-- Hybrid quadratic remainder from one packaged assumptions object. -/
lemma bound_of_assumptions {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ)
    (totalError : QDriftTotalError R) (τ : ℝ) (steps : ℕ)
    (pre post : Fin steps → SuperOp R)
    (hassumptions : Assumptions H p totalError τ steps pre post) :
    Statement totalError τ :=
  bound H p totalError τ steps pre post
    hassumptions.hybrid_decomposition
    hassumptions.one_step_quadratic

/-- Hybrid quadratic remainder directly from the one-step Taylor-style
remainder assumptions. -/
lemma bound_of_one_step_assumptions {R : Register} {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (p : ι → ℝ)
    (totalError : QDriftTotalError R) (τ : ℝ) (steps : ℕ)
    (pre post : Fin steps → SuperOp R)
    (hdecomp :
      totalError = ∑ k, qdriftHybridStepErrorFamily pre post H p τ k)
    (honeStep : QDriftOneStepQuadraticRemainder.Assumptions H p τ) :
    Statement totalError τ :=
  bound H p totalError τ steps pre post hdecomp
    (QDriftOneStepQuadraticRemainder.bound_of_assumptions H p τ honeStep)

end QDriftHybridQuadraticRemainder

namespace QDriftGlobalErrorBound

/-- Statement of the abstract qDRIFT global error bound after `steps` hybrid
steps. -/
def Statement {R : Register}
    (superOpNorm : SuperOp R → ℝ) (totalError : QDriftTotalError R)
    (t Λ : ℝ) (steps : ℕ) : Prop :=
  superOpNorm totalError ≤ (t ^ 2 / (steps : ℝ)) * Λ

/-- Packaged assumptions for the abstract qDRIFT global error bound. -/
structure Assumptions {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (H : ι → HilbertOperator R) (p : ι → ℝ)
    (totalError : QDriftTotalError R) (t Λ : ℝ) (steps : ℕ)
    (pre post : Fin steps → SuperOp R) : Prop where
  norm_properties : SuperOpNormProperties superOpNorm scalarNorm
  steps_ne_zero : steps ≠ 0
  lambda_nonneg : 0 ≤ Λ
  scalar_square_bound :
    scalarNorm (((t / (steps : ℝ) : ℝ) : ℂ) ^ 2)
      ≤ (t / (steps : ℝ)) ^ 2
  hybrid_decomposition :
    totalError = ∑ k,
      qdriftHybridStepErrorFamily pre post H p (t / (steps : ℝ)) k
  hybrid_step_budget : ∀ k,
    QuadraticRemainderNormBudget superOpNorm scalarNorm (t / (steps : ℝ)) Λ
      (qdriftHybridStepErrorFamily pre post H p (t / (steps : ℝ)) k)

/-- Packaged assumptions for a global error written directly as a composition
power difference. -/
structure PowerDiffAssumptions {R : Register}
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (U E : SuperOp R) (t Λ : ℝ) (steps : ℕ) : Prop where
  norm_properties : SuperOpNormProperties superOpNorm scalarNorm
  steps_ne_zero : steps ≠ 0
  lambda_nonneg : 0 ≤ Λ
  scalar_square_bound :
    scalarNorm (((t / (steps : ℝ) : ℝ) : ℂ) ^ 2)
      ≤ (t / (steps : ℝ)) ^ 2
  telescoping_step_budget : ∀ k : Fin steps,
    QuadraticRemainderNormBudget superOpNorm scalarNorm (t / (steps : ℝ)) Λ
      (superOpComp (superOpPower U (steps - 1 - (k : ℕ)))
        (superOpComp (U - E) (superOpPower E (k : ℕ))))

/-- Abstract qDRIFT global error bound from packaged hybrid quadratic budgets. -/
lemma bound {R : Register} {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (H : ι → HilbertOperator R) (p : ι → ℝ)
    (totalError : QDriftTotalError R) (t Λ : ℝ) (steps : ℕ)
    (pre post : Fin steps → SuperOp R)
    (hassumptions :
      Assumptions superOpNorm scalarNorm H p totalError t Λ steps pre post) :
    Statement superOpNorm totalError t Λ steps :=
  qdrift_global_error_bound_of_hybrid_quadratic_budgets_of_scalar_square
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm)
    (hnorm := hassumptions.norm_properties)
    (H := H) (p := p) (totalError := totalError)
    (t := t) (Λ := Λ) (steps := steps) (pre := pre) (post := post)
    (hsteps := hassumptions.steps_ne_zero)
    (hΛ := hassumptions.lambda_nonneg)
    (hscalar_sq := hassumptions.scalar_square_bound)
    hassumptions.hybrid_decomposition
    hassumptions.hybrid_step_budget

/-- Abstract qDRIFT global error bound from a direct power-difference
telescoping expansion. -/
lemma bound_of_power_diff {R : Register}
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (U E : SuperOp R) (t Λ : ℝ) (steps : ℕ)
    (hassumptions : PowerDiffAssumptions superOpNorm scalarNorm U E t Λ steps) :
    Statement superOpNorm (superOpPower U steps - superOpPower E steps) t Λ steps :=
  qdrift_global_error_bound_of_power_diff_quadratic_budgets
    (superOpNorm := superOpNorm) (scalarNorm := scalarNorm)
    (hnorm := hassumptions.norm_properties)
    (U := U) (E := E) (t := t) (Λ := Λ) (steps := steps)
    (hsteps := hassumptions.steps_ne_zero)
    (hΛ := hassumptions.lambda_nonneg)
    (hscalar_sq := hassumptions.scalar_square_bound)
    hassumptions.telescoping_step_budget

/-- Power-difference global error bound specialized to the concrete complex
scalar norm. -/
lemma bound_of_power_diff_complex_norm {R : Register}
    (superOpNorm : SuperOp R → ℝ)
    (U E : SuperOp R) (t Λ : ℝ) (steps : ℕ)
    (hnorm : SuperOpNormProperties superOpNorm fun z : ℂ => ‖z‖)
    (hsteps : steps ≠ 0)
    (hΛ : 0 ≤ Λ)
    (hbudget : ∀ k : Fin steps,
      QuadraticRemainderNormBudget superOpNorm (fun z : ℂ => ‖z‖)
        (t / (steps : ℝ)) Λ
        (superOpComp (superOpPower U (steps - 1 - (k : ℕ)))
          (superOpComp (U - E) (superOpPower E (k : ℕ))))) :
    Statement superOpNorm (superOpPower U steps - superOpPower E steps) t Λ steps :=
  qdrift_global_error_bound_of_power_diff_quadratic_budgets
    (superOpNorm := superOpNorm) (scalarNorm := fun z : ℂ => ‖z‖)
    (hnorm := hnorm)
    (U := U) (E := E) (t := t) (Λ := Λ) (steps := steps)
    (hsteps := hsteps) (hΛ := hΛ)
    (hscalar_sq := complex_norm_scalar_square_bound t steps)
    hbudget

end QDriftGlobalErrorBound

/-- Campbell-style global qDRIFT bound for the repeated averaged channel.

The analytic one-step estimate and norm laws stay abstract in
`PowerDiffAssumptions`; this theorem fixes their channel arguments and the
physical total time `t λ`. -/
lemma qdriftAverageChannel_global_error_bound {R : Register}
    {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (H : ι → HilbertOperator R) (h : ι → ℝ) (t κ : ℝ) (steps : ℕ)
    (hassumptions :
      QDriftGlobalErrorBound.PowerDiffAssumptions superOpNorm scalarNorm
        (qdriftTargetSegmentChannel H h t steps)
        (qdriftAverageChannel H h t steps)
        (qdriftAverageTotalTime h t) κ steps) :
    superOpNorm (qdriftAveragePowerError H h t steps)
      ≤ (qdriftAverageTotalTime h t) ^ 2 / (steps : ℝ) * κ := by
  simpa [qdriftAveragePowerError, QDriftGlobalErrorBound.Statement] using
    (QDriftGlobalErrorBound.bound_of_power_diff superOpNorm scalarNorm
      (qdriftTargetSegmentChannel H h t steps)
      (qdriftAverageChannel H h t steps)
      (qdriftAverageTotalTime h t) κ steps hassumptions)

/-- One-step qDRIFT error bound expressed in Campbell's coefficient parameters. -/
lemma qdriftAverageChannel_oneStep_error_bound {R : Register}
    {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (matrixNorm : HilbertOperator R → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (hmul : SuperOpTwoSidedMulNormControl superOpNorm matrixNorm)
    (H : ι → HilbertOperator R) (h : ι → ℝ) (t : ℝ) (steps : ℕ)
    (hweights : QDriftWeightConditions scalarNorm (qdriftProbabilities h))
    (termBound idealBudget κ : ℝ)
    (hterms : ∀ j,
      UnitaryStepRemainderNormBudget matrixNorm (H j)
        (qdriftStepTime h t steps) termBound)
    (hideal : UnitaryStepRemainderNormBudget matrixNorm
      (weightedHamiltonianOp H (qdriftProbabilities h))
      (qdriftStepTime h t steps) idealBudget)
    (hterm_nonneg : 0 ≤ termBound)
    (hquadratic : termBound + idealBudget
      ≤ κ * (qdriftStepTime h t steps) ^ 2) :
    superOpNorm
        (qdriftAverageChannel H h t steps - qdriftTargetSegmentChannel H h t steps)
      ≤ κ * (qdriftAverageTotalTime h t) ^ 2 / (steps : ℝ) ^ 2 := by
  simpa [qdriftAverageChannel, qdriftTargetSegmentChannel,
    qdriftAverageTotalTime, qdriftStepTime, QDriftOneStepErrorBound.Statement,
    qdriftStepErrorSuperOp] using
    (QDriftOneStepErrorBound.bound_of_unitaryStepBudgets
      superOpNorm scalarNorm matrixNorm hnorm hmul H (qdriftProbabilities h)
      (qdriftAverageTotalTime h t) steps hweights termBound idealBudget κ
      (by simpa [qdriftAverageTotalTime, qdriftStepTime] using hterms)
      (by simpa [qdriftAverageTotalTime, qdriftStepTime] using hideal)
      hterm_nonneg
      (by simpa [qdriftAverageTotalTime, qdriftStepTime] using hquadratic))

/-- One-step qDRIFT error bound in Campbell's coefficient parameters, using
the concrete operator-norm unitary-step remainder estimate. -/
lemma qdriftAverageChannel_oneStep_error_bound_operatorNorm {R : Register}
    [Nonempty R.Index] {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (hmul : SuperOpTwoSidedMulNormControl superOpNorm opNorm)
    (H : ι → HilbertOperator R) (h : ι → ℝ) (t Λ : ℝ) (steps : ℕ)
    (hscalar :
      ∀ j, scalarNorm ((qdriftProbabilities h j : ℝ) : ℂ) =
        qdriftProbabilities h j)
    (h_nonneg : ∀ j, 0 ≤ h j) (h_lambda_ne_zero : qdriftLambda h ≠ 0)
    (hH : ∀ j, (H j).IsHermitian) (ht : 0 ≤ t) (hsteps : steps ≠ 0)
    (hΛ : 0 ≤ Λ) (hHnorm : ∀ j, opNorm (H j) ≤ Λ) :
    superOpNorm
        (qdriftAverageChannel H h t steps - qdriftTargetSegmentChannel H h t steps)
      ≤ qdriftOperatorNormConstant (qdriftAverageTotalTime h t) Λ *
          (qdriftAverageTotalTime h t) ^ 2 / (steps : ℝ) ^ 2 := by
  have hprob : QDriftProbabilityWeights (qdriftProbabilities h) :=
    qdriftProbabilityWeights h h_nonneg h_lambda_ne_zero
  have hweights :
      QDriftWeightConditions scalarNorm (qdriftProbabilities h) :=
    QDriftWeightConditions.of_probability_weights scalarNorm
      (qdriftProbabilities h) hscalar hprob
  have hlambda_nonneg : 0 ≤ qdriftLambda h :=
    Finset.sum_nonneg fun j _ => h_nonneg j
  have htotal_nonneg : 0 ≤ qdriftAverageTotalTime h t := by
    exact mul_nonneg ht hlambda_nonneg
  simpa [qdriftOperatorNormConstant, qdriftAverageChannel, qdriftTargetSegmentChannel,
    qdriftAverageTotalTime, qdriftStepTime, QDriftOneStepErrorBound.Statement,
    qdriftStepErrorSuperOp] using
    (QDriftOneStepErrorBound.bound_of_operatorNorm
      (superOpNorm := superOpNorm) (scalarNorm := scalarNorm)
      (hnorm := hnorm) (hmul := hmul)
      (H := H) (p := qdriftProbabilities h)
      (t := qdriftAverageTotalTime h t) (Λ := Λ) (steps := steps)
      hprob hweights hH htotal_nonneg hsteps hΛ hHnorm)

/-- One-step qDRIFT error bound for the induced trace norm, using the concrete
operator-norm two-sided multiplication control proved above. -/
lemma qdriftAverageChannel_oneStep_error_bound_inducedTraceNorm_operatorNorm {R : Register}
    [Nonempty R.Index] {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (h : ι → ℝ) (t Λ : ℝ) (steps : ℕ)
    (h_nonneg : ∀ j, 0 ≤ h j) (h_lambda_ne_zero : qdriftLambda h ≠ 0)
    (hH : ∀ j, (H j).IsHermitian) (ht : 0 ≤ t) (hsteps : steps ≠ 0)
    (hΛ : 0 ≤ Λ) (hHnorm : ∀ j, opNorm (H j) ≤ Λ) :
    inducedTraceNorm
        (qdriftAverageChannel H h t steps - qdriftTargetSegmentChannel H h t steps)
      ≤ qdriftOperatorNormConstant (qdriftAverageTotalTime h t) Λ *
          (qdriftAverageTotalTime h t) ^ 2 / (steps : ℝ) ^ 2 := by
  have hprob : QDriftProbabilityWeights (qdriftProbabilities h) :=
    qdriftProbabilityWeights h h_nonneg h_lambda_ne_zero
  exact qdriftAverageChannel_oneStep_error_bound_operatorNorm
    (superOpNorm := inducedTraceNorm) (scalarNorm := fun c : ℂ => ‖c‖)
    (hnorm := inducedTraceNorm_properties)
    (hmul := inducedTraceNorm_twoSidedMul_control_operatorNorm)
    (H := H) (h := h) (t := t) (Λ := Λ) (steps := steps)
    (hscalar := by
      intro j
      simp [Complex.norm_real, abs_of_nonneg (hprob.nonneg j)])
    h_nonneg h_lambda_ne_zero hH ht hsteps hΛ hHnorm

/-- Hybrid global qDRIFT error bound in Campbell's coefficient parameters,
using the concrete operator-norm one-step estimate.  The hybrid decomposition
and propagation nonexpansivity remain explicit superoperator assumptions. -/
lemma qdriftAverageChannel_hybrid_global_error_bound_operatorNorm {R : Register}
    [Nonempty R.Index] {ι : Type} [Fintype ι]
    (superOpNorm : SuperOp R → ℝ) (scalarNorm : ℂ → ℝ)
    (hnorm : SuperOpNormProperties superOpNorm scalarNorm)
    (hmul : SuperOpTwoSidedMulNormControl superOpNorm opNorm)
    (H : ι → HilbertOperator R) (h : ι → ℝ)
    (totalError : QDriftTotalError R) (t Λ : ℝ) (steps : ℕ)
    (pre post : Fin steps → SuperOp R)
    (hscalar :
      ∀ j, scalarNorm ((qdriftProbabilities h j : ℝ) : ℂ) =
        qdriftProbabilities h j)
    (h_nonneg : ∀ j, 0 ≤ h j) (h_lambda_ne_zero : qdriftLambda h ≠ 0)
    (hH : ∀ j, (H j).IsHermitian) (ht : 0 ≤ t) (hsteps : steps ≠ 0)
    (hΛ : 0 ≤ Λ) (hHnorm : ∀ j, opNorm (H j) ≤ Λ)
    (hdecomp :
      totalError =
        ∑ k,
          qdriftHybridStepErrorFamily pre post H (qdriftProbabilities h)
            (qdriftStepTime h t steps) k)
    (hpre : ∀ k, SuperOpLeftNonexpansive superOpNorm (pre k))
    (hpost : ∀ k, SuperOpRightNonexpansive superOpNorm (post k)) :
    superOpNorm totalError
      ≤ qdriftOperatorNormConstant (qdriftAverageTotalTime h t) Λ *
          (qdriftAverageTotalTime h t) ^ 2 / (steps : ℝ) := by
  have hprob : QDriftProbabilityWeights (qdriftProbabilities h) :=
    qdriftProbabilityWeights h h_nonneg h_lambda_ne_zero
  have hweights :
      QDriftWeightConditions scalarNorm (qdriftProbabilities h) :=
    QDriftWeightConditions.of_probability_weights scalarNorm
      (qdriftProbabilities h) hscalar hprob
  have hlambda_nonneg : 0 ≤ qdriftLambda h :=
    Finset.sum_nonneg fun j _ => h_nonneg j
  have htotal_nonneg : 0 ≤ qdriftAverageTotalTime h t := by
    exact mul_nonneg ht hlambda_nonneg
  simpa [qdriftOperatorNormConstant, qdriftAverageTotalTime, qdriftStepTime,
    QDriftTotalErrorBound.Statement, qdriftTotalErrorStatement] using
    (QDriftTotalErrorBound.bound_of_operatorNorm
      (superOpNorm := superOpNorm) (scalarNorm := scalarNorm)
      (hnorm := hnorm) (hmul := hmul)
      (H := H) (p := qdriftProbabilities h) (totalError := totalError)
      (t := qdriftAverageTotalTime h t) (Λ := Λ) (steps := steps)
      (pre := pre) (post := post)
      hprob hweights hH htotal_nonneg hsteps hΛ hHnorm
      (by simpa [qdriftAverageTotalTime, qdriftStepTime] using hdecomp)
      hpre hpost)

/-- Hybrid global qDRIFT error bound for the induced trace norm.  Hybrid
propagators are supplied as pointwise trace-norm nonexpansive maps and are
converted to induced-norm nonexpansive maps internally. -/
lemma qdriftAverageChannel_hybrid_global_error_bound_inducedTraceNorm_operatorNorm
    {R : Register} [Nonempty R.Index] {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (h : ι → ℝ)
    (totalError : QDriftTotalError R) (t Λ : ℝ) (steps : ℕ)
    (pre post : Fin steps → SuperOp R)
    (h_nonneg : ∀ j, 0 ≤ h j) (h_lambda_ne_zero : qdriftLambda h ≠ 0)
    (hH : ∀ j, (H j).IsHermitian) (ht : 0 ≤ t) (hsteps : steps ≠ 0)
    (hΛ : 0 ≤ Λ) (hHnorm : ∀ j, opNorm (H j) ≤ Λ)
    (hdecomp :
      totalError =
        ∑ k,
          qdriftHybridStepErrorFamily pre post H (qdriftProbabilities h)
            (qdriftStepTime h t steps) k)
    (hpre : ∀ k, TraceNormNonexpansive (pre k))
    (hpost : ∀ k, TraceNormNonexpansive (post k)) :
    inducedTraceNorm totalError
      ≤ qdriftOperatorNormConstant (qdriftAverageTotalTime h t) Λ *
          (qdriftAverageTotalTime h t) ^ 2 / (steps : ℝ) := by
  have hprob : QDriftProbabilityWeights (qdriftProbabilities h) :=
    qdriftProbabilityWeights h h_nonneg h_lambda_ne_zero
  exact qdriftAverageChannel_hybrid_global_error_bound_operatorNorm
    (superOpNorm := inducedTraceNorm) (scalarNorm := fun c : ℂ => ‖c‖)
    (hnorm := inducedTraceNorm_properties)
    (hmul := inducedTraceNorm_twoSidedMul_control_operatorNorm)
    (H := H) (h := h) (totalError := totalError) (t := t) (Λ := Λ)
    (steps := steps) (pre := pre) (post := post)
    (hscalar := by
      intro j
      simp [Complex.norm_real, abs_of_nonneg (hprob.nonneg j)])
    h_nonneg h_lambda_ne_zero hH ht hsteps hΛ hHnorm hdecomp
    (fun k => traceNormNonexpansive_left_inducedTraceNorm_nonexpansive (hpre k))
    (fun k => traceNormNonexpansive_right_inducedTraceNorm_nonexpansive (hpost k))

/-- Global repeated-channel qDRIFT error bound for the induced trace norm.

This closes the standard telescoping/hybrid argument for the concrete averaged
qDRIFT channel and its target segment channel. -/
public theorem qdriftAveragePowerError_bound_inducedTraceNorm_operatorNorm {R : Register}
    [Nonempty R.Index] {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (h : ι → ℝ) (t Λ : ℝ) (steps : ℕ)
    (h_nonneg : ∀ j, 0 ≤ h j) (h_lambda_ne_zero : qdriftLambda h ≠ 0)
    (hH : ∀ j, (H j).IsHermitian) (ht : 0 ≤ t) (hsteps : steps ≠ 0)
    (hΛ : 0 ≤ Λ) (hHnorm : ∀ j, opNorm (H j) ≤ Λ) :
    inducedTraceNorm (qdriftAveragePowerError H h t steps)
      ≤ qdriftOperatorNormConstant (qdriftAverageTotalTime h t) Λ *
          (qdriftAverageTotalTime h t) ^ 2 / (steps : ℝ) := by
  let avg : SuperOp R := qdriftAverageChannel H h t steps
  let target : SuperOp R := qdriftTargetSegmentChannel H h t steps
  let pre : Fin steps → SuperOp R := fun k =>
    superOpPower avg (steps - 1 - (k : ℕ))
  let post : Fin steps → SuperOp R := fun k =>
    superOpPower target (k : ℕ)
  have htarget_nonexp : TraceNormNonexpansive target := by
    simpa [target] using
      qdriftTargetSegmentChannel_traceNorm_nonexpansive H h t steps hH
  have havg_nonexp : TraceNormNonexpansive avg := by
    simpa [avg] using
      qdriftAverageChannel_traceNorm_nonexpansive
        H h t steps h_nonneg h_lambda_ne_zero hH
  have hdecomp :
      superOpPower avg steps - superOpPower target steps =
        ∑ k,
          qdriftHybridStepErrorFamily pre post H (qdriftProbabilities h)
            (qdriftStepTime h t steps) k := by
    rw [superOpPower_diff_eq_sum]
    trans ∑ k : Fin steps,
        superOpComp (superOpPower avg (steps - 1 - (k : ℕ)))
          (superOpComp (avg - target) (superOpPower target (k : ℕ)))
    · exact (Fin.sum_univ_eq_sum_range
        (fun k : ℕ =>
          superOpComp (superOpPower avg (steps - 1 - k))
            (superOpComp (avg - target) (superOpPower target k))) steps).symm
    · apply Finset.sum_congr rfl
      intro k _
      simp [pre, post, avg, target, qdriftAverageChannel,
        qdriftTargetSegmentChannel, qdriftHybridStepErrorFamily,
        qdriftPropagatedStepError, qdriftStepErrorSuperOp]
  have hbound :
      inducedTraceNorm (superOpPower avg steps - superOpPower target steps)
        ≤ qdriftOperatorNormConstant (qdriftAverageTotalTime h t) Λ *
            (qdriftAverageTotalTime h t) ^ 2 / (steps : ℝ) := by
    exact qdriftAverageChannel_hybrid_global_error_bound_inducedTraceNorm_operatorNorm
      (H := H) (h := h)
      (totalError := superOpPower avg steps - superOpPower target steps)
      (t := t) (Λ := Λ) (steps := steps) (pre := pre) (post := post)
      h_nonneg h_lambda_ne_zero hH ht hsteps hΛ hHnorm
      hdecomp
      (fun k => TraceNormNonexpansive.power havg_nonexp _)
      (fun k => TraceNormNonexpansive.power htarget_nonexp _)
  have hneg :
      qdriftAveragePowerError H h t steps =
        -(superOpPower avg steps - superOpPower target steps) := by
    simp [qdriftAveragePowerError, avg, target, sub_eq_add_neg]
  rw [hneg, inducedTraceNorm_neg]
  exact hbound

/-- A coarse small-step corollary for the repeated-channel qDRIFT bound.

When the total simulated time-energy product satisfies `T * Λ ≤ 1`, the
operator-norm constant can be replaced by the simpler
`(3 * exp 1 + 2) * Λ^2`. -/
lemma qdriftAveragePowerError_bound_inducedTraceNorm_operatorNorm_small
    {R : Register} [Nonempty R.Index] {ι : Type} [Fintype ι]
    (H : ι → HilbertOperator R) (h : ι → ℝ) (t Λ : ℝ) (steps : ℕ)
    (h_nonneg : ∀ j, 0 ≤ h j) (h_lambda_ne_zero : qdriftLambda h ≠ 0)
    (hH : ∀ j, (H j).IsHermitian) (ht : 0 ≤ t) (hsteps : steps ≠ 0)
    (hΛ : 0 ≤ Λ) (hHnorm : ∀ j, opNorm (H j) ≤ Λ)
    (hsmall : qdriftAverageTotalTime h t * Λ ≤ 1) :
    inducedTraceNorm (qdriftAveragePowerError H h t steps)
      ≤ ((3 * Real.exp 1 + 2) * Λ ^ 2) *
          (qdriftAverageTotalTime h t) ^ 2 / (steps : ℝ) := by
  have hbase :=
    qdriftAveragePowerError_bound_inducedTraceNorm_operatorNorm
      (H := H) (h := h) (t := t) (Λ := Λ) (steps := steps)
      h_nonneg h_lambda_ne_zero hH ht hsteps hΛ hHnorm
  have hlambda_nonneg : 0 ≤ qdriftLambda h :=
    Finset.sum_nonneg fun j _ => h_nonneg j
  have htotal_nonneg : 0 ≤ qdriftAverageTotalTime h t := by
    exact mul_nonneg ht hlambda_nonneg
  have hmul_nonneg : 0 ≤ qdriftAverageTotalTime h t * Λ := by
    exact mul_nonneg htotal_nonneg hΛ
  have hconstant :
      qdriftOperatorNormConstant (qdriftAverageTotalTime h t) Λ
        ≤ (3 * Real.exp 1 + 2) * Λ ^ 2 :=
    qdriftOperatorNormConstant_le_small hmul_nonneg hsmall
  have hsteps_pos : 0 < (steps : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hsteps
  have hscaled :
      qdriftOperatorNormConstant (qdriftAverageTotalTime h t) Λ *
          (qdriftAverageTotalTime h t) ^ 2 / (steps : ℝ)
        ≤ ((3 * Real.exp 1 + 2) * Λ ^ 2) *
          (qdriftAverageTotalTime h t) ^ 2 / (steps : ℝ) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hconstant
        (sq_nonneg (qdriftAverageTotalTime h t)))
      hsteps_pos.le
  exact le_trans hbase hscaled

end

end QuantumAlg
