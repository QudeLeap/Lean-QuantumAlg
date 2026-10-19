/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Invariant
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Operator
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Invariant
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Operator
import all QuantumAlg.Primitives.QSP.SingleQubit.Chebyshev.Basic
import all QuantumAlg.Primitives.QSP.SingleQubit.PhaseSynthesis
import all QuantumAlg.Components.Gates.Rotation.Operator
import all QuantumAlg.Components.Gates.Signal.Operator
import all QuantumAlg.Components.Oracle.SignalProcessing
import all QuantumAlg.Components.Oracle.Reflection
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Util.Complex

/-!
# Alternating source products on singular invariant sectors

The source's phase conversion from W-signal QSP and its actions on singular
sectors use certified operators, independently of executable gate accounting
[GSLW19, BlockHam.tex:514-528,655-849].
-/

section
namespace QuantumAlg.QSP.MultiQubit.QSVT
open scoped Matrix.Norms.L2Operator ComplexOrder

@[simp]
lemma sourceAlternatingPhaseModulation_nil {N : Nat} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N) :
    (Native.sourceWord U left right [] : HilbertOperator (Qubits N)) = 1 := rfl

/-- The independent source product composes phase, parity-selected signal and tail. -/
lemma sourceAlternatingPhaseModulation_cons {N : Nat} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N) (φ : ℝ) (phases : List ℝ) :
    (Native.sourceWord U left right (φ :: phases) : HilbertOperator (Qubits N)) =
      (projectorPhaseOp φ (sourcePhaseProjector left right (phases.length + 1)) :
        HilbertOperator (Qubits N)) *
      (sourcePhaseSignal U (phases.length + 1) : HilbertOperator (Qubits N)) *
      (Native.sourceWord U left right phases : HilbertOperator (Qubits N)) := by
  by_cases even : (phases.length + 1) % 2 = 0 <;>
    simp [Native.sourceWord, sourcePhaseProjector, projectedOutputProjector, sourcePhaseSignal,
      UnitaryOperator.dagger, Matrix.mul_assoc, even]

@[simp]
lemma sourceAlternatingPhaseModulation_cons_applyVec {N : Nat}
    (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N)
    (φ : ℝ) (phases : List ℝ) (ψ : HilbertVector (Qubits N)) :
    (Native.sourceWord U left right (φ :: phases)).applyVec ψ =
      (projectorPhaseOp φ (sourcePhaseProjector left right (phases.length + 1))).applyVec
        ((sourcePhaseSignal U (phases.length + 1)).applyVec
          ((Native.sourceWord U left right phases).applyVec ψ)) := by
  change HilbertOperator.applyVec (Native.sourceWord U left right (φ :: phases)) ψ = _
  rw [sourceAlternatingPhaseModulation_cons,
    HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec]
  rfl

/-- Scalar phase product accumulated by a one-dimensional singular block of
the source alternating phase sequence. -/
noncomputable def phaseProduct (phases : List ℝ) : ℂ :=
  (phases.map fun φ => Complex.exp (φ * Complex.I)).prod

@[simp]
lemma phaseProduct_nil : phaseProduct [] = 1 := rfl

@[simp]
lemma phaseProduct_cons (φ : ℝ) (phases : List ℝ) :
    phaseProduct (φ :: phases) =
      Complex.exp (φ * Complex.I) * phaseProduct phases := by
  simp [phaseProduct]

/-- The `(0,0)` scalar entry of the `W`-convention one-qubit QSP product at
`x=1` is the product of all scalar phase factors. -/
lemma qspW_one_zero_zero_eq_phaseProduct (φ₀ : ℝ) (φs : List ℝ) :
    qspW φ₀ φs 1 0 0 =
      Complex.exp (φ₀ * Complex.I) *
        (φs.map fun φ => Complex.exp (φ * Complex.I)).prod := by
  induction φs using List.reverseRecOn with
  | nil =>
      simp [qspW, rotZOp]
  | append_singleton φs φ ih =>
      rw [qspW_concat]
      simp [Matrix.mul_apply, signalW, rotZOp, ih]
      ring

/-- The real `R(x)` signal block used in the source proof of singular-value
transformation.  It is the local two-dimensional block induced by `U` and
`U†` on a nontrivial singular sector [GSLW19, BlockHam.tex:520-528,768-849]. -/
noncomputable def singularSignalR (x : ℝ) : HilbertOperator (Qubits 1) :=
  !![(x : ℂ), (Real.sqrt (1 - x ^ 2) : ℂ);
     (Real.sqrt (1 - x ^ 2) : ℂ), (-(x : ℂ))]

/-- The source `R(x)` signal block is unitary on its physical singular-value
domain. -/
lemma singularSignalR_mem_unitaryGroup {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    singularSignalR x ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  have hs := sq_sqrt_one_sub_sq hx
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [singularSignalR, Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
    linear_combination hs
  · simp [singularSignalR, Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
    ring
  · simp [singularSignalR, Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
    ring
  · simp [singularSignalR, Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
    linear_combination hs

/-- The source `R(x)` signal block certified on its physical singular-value
domain. -/
noncomputable def singularSignalROperator (x : ℝ)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix (singularSignalR x)
    (singularSignalR_mem_unitaryGroup hx)

@[simp]
lemma singularSignalROperator_coe (x : ℝ)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (singularSignalROperator x hx : HilbertOperator (Qubits 1)) =
      singularSignalR x := rfl

-- Mathlib linter exception: this source-aligned 2x2 matrix expansion is
-- kept in its existing proof shape; `simp only` rewrites were brittle here.
set_option linter.flexible false in
/-- In the repository's `rotZOp` convention, the source identity
`W(x)=i e^{-iπσ_z/4} R(x)e^{-iπσ_z/4}` is the matrix bridge from the
`W`-convention QSP certificate to the projected-QSVT `R` product
[GSLW19, BlockHam.tex:514-517]. -/
lemma signalW_eq_I_smul_rotZ_mul_singularSignalR_mul_rotZ (x : ℝ) :
    signalW x =
      (Complex.I : ℂ) •
        ((rotZOp (-(Real.pi / 4)) : HilbertOperator (Qubits 1)) *
          singularSignalR x * (rotZOp (-(Real.pi / 4)) : HilbertOperator (Qubits 1))) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [signalW, singularSignalR, rotZOp]
    have hprod :
        Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
            ↑x * Complex.exp (-(↑Real.pi / 4 * Complex.I)) =
          ↑x * Complex.exp (-(↑Real.pi / 2 * Complex.I)) := by
      rw [show Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
            ↑x * Complex.exp (-(↑Real.pi / 4 * Complex.I)) =
          ↑x * (Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
            Complex.exp (-(↑Real.pi / 4 * Complex.I))) by ring]
      rw [← Complex.exp_add]
      congr 1
      ring_nf
    rw [hprod, exp_neg_pi_div_two_mul_I]
    rw [mul_comm (x : ℂ) (-Complex.I), ← mul_assoc]
    rw [show Complex.I * -Complex.I = (1 : ℂ) by
      rw [mul_neg, Complex.I_mul_I]
      ring]
    ring
  · simp [signalW, singularSignalR, rotZOp]
    have hprod :
        Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
            ↑√(1 - x ^ 2) * Complex.exp (↑Real.pi / 4 * Complex.I) =
          ↑√(1 - x ^ 2) := by
      rw [show Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
            ↑√(1 - x ^ 2) * Complex.exp (↑Real.pi / 4 * Complex.I) =
          ↑√(1 - x ^ 2) * (Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
            Complex.exp (↑Real.pi / 4 * Complex.I)) by ring]
      rw [← Complex.exp_add]
      simp
    rw [hprod]
  · simp [signalW, singularSignalR, rotZOp]
    have hprod :
        Complex.exp (↑Real.pi / 4 * Complex.I) *
            ↑√(1 - x ^ 2) * Complex.exp (-(↑Real.pi / 4 * Complex.I)) =
          ↑√(1 - x ^ 2) := by
      rw [show Complex.exp (↑Real.pi / 4 * Complex.I) *
            ↑√(1 - x ^ 2) * Complex.exp (-(↑Real.pi / 4 * Complex.I)) =
          ↑√(1 - x ^ 2) * (Complex.exp (↑Real.pi / 4 * Complex.I) *
            Complex.exp (-(↑Real.pi / 4 * Complex.I))) by ring]
      rw [← Complex.exp_add]
      simp
    rw [hprod]
  · simp [signalW, singularSignalR, rotZOp]
    have hprod :
        Complex.exp (↑Real.pi / 4 * Complex.I) *
            ↑x * Complex.exp (↑Real.pi / 4 * Complex.I) =
          ↑x * Complex.exp (↑Real.pi / 2 * Complex.I) := by
      rw [show Complex.exp (↑Real.pi / 4 * Complex.I) *
            ↑x * Complex.exp (↑Real.pi / 4 * Complex.I) =
          ↑x * (Complex.exp (↑Real.pi / 4 * Complex.I) *
            Complex.exp (↑Real.pi / 4 * Complex.I)) by ring]
      rw [← Complex.exp_add]
      congr 1
      ring_nf
    rw [hprod, exp_pi_div_two_mul_I]
    rw [mul_comm (x : ℂ) Complex.I, ← mul_assoc, Complex.I_mul_I]
    ring

/-- The source's `R`-convention product
`∏_j (e^{iφ_jσ_z} R(x))`, written in the same left-to-right order as the
projected-unitary phase sequence [GSLW19, BlockHam.tex:520-528,768-849]. -/
noncomputable def singularSignalRProduct : List ℝ -> ℝ -> HilbertOperator (Qubits 1)
  | [], _ => 1
  | φ :: phases, x =>
      (rotZOp φ : HilbertOperator (Qubits 1)) *
        singularSignalR x * singularSignalRProduct phases x

/-- The source `R`-convention product certified on the physical singular-value
domain. -/
noncomputable def singularSignalRProductOperator :
    (phases : List ℝ) -> (x : ℝ) ->
      x ∈ Set.Icc (-1 : ℝ) 1 -> UnitaryOperator (Qubits 1)
  | [], _, _ => 1
  | φ :: phases, x, hx =>
      (rotZOp φ) * singularSignalROperator x hx *
        singularSignalRProductOperator phases x hx

@[simp]
lemma singularSignalRProductOperator_coe (phases : List ℝ) (x : ℝ)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (singularSignalRProductOperator phases x hx :
      HilbertOperator (Qubits 1)) = singularSignalRProduct phases x := by
  induction phases with
  | nil => rfl
  | cons φ phases ih =>
      simp [singularSignalRProductOperator, singularSignalRProduct, ih]

@[simp]
lemma singularSignalRProduct_nil (x : ℝ) :
    singularSignalRProduct [] x = 1 := rfl

@[simp]
lemma singularSignalRProduct_cons (φ : ℝ) (phases : List ℝ) (x : ℝ) :
    singularSignalRProduct (φ :: phases) x =
      (rotZOp φ : HilbertOperator (Qubits 1)) *
        singularSignalR x * singularSignalRProduct phases x := rfl

/-- Appending one source `R`-signal block on the right multiplies the existing
source product by that block [GSLW19, BlockHam.tex:501-528]. -/
lemma singularSignalRProduct_append_singleton (phases : List ℝ) (φ x : ℝ) :
    singularSignalRProduct (phases ++ [φ]) x =
      singularSignalRProduct phases x *
        ((rotZOp φ : HilbertOperator (Qubits 1)) * singularSignalR x) := by
  induction phases with
  | nil =>
      simp [singularSignalRProduct]
  | cons θ phases ih =>
      simp [singularSignalRProduct, ih, mul_assoc]

private lemma rotZ_neg_eq_map_star (φ : ℝ) :
    (rotZOp (-φ) : HilbertOperator (Qubits 1)) =
      ((rotZOp φ : HilbertOperator (Qubits 1)).map (starRingEnd ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZOp, conj_exp_I, conj_exp_neg_I]

private lemma singularSignalR_eq_map_star (x : ℝ) :
    singularSignalR x = (singularSignalR x).map (starRingEnd ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [singularSignalR]

lemma singularSignalRProduct_map_neg_eq_map_star (phases : List ℝ) (x : ℝ) :
    singularSignalRProduct (phases.map fun φ => -φ) x =
      (singularSignalRProduct phases x).map (starRingEnd ℂ) := by
  induction phases with
  | nil =>
      simp [singularSignalRProduct]
  | cons φ phases ih =>
      simp only [List.map_cons, singularSignalRProduct_cons]
      rw [ih, rotZ_neg_eq_map_star]
      rw [Matrix.map_mul, Matrix.map_mul]
      rw [← singularSignalR_eq_map_star]

lemma singularSignalRProduct_map_neg_zero_zero (phases : List ℝ) (x : ℝ) :
    singularSignalRProduct (phases.map fun φ => -φ) x 0 0 =
      star (singularSignalRProduct phases x 0 0) := by
  rw [singularSignalRProduct_map_neg_eq_map_star]
  rfl

/-- The `rotZOp` multiplication rule at the `HilbertOperator` coercion layer. -/
lemma rotZ_op_mul (a b : ℝ) :
    (rotZOp a : HilbertOperator (Qubits 1)) *
        (rotZOp b : HilbertOperator (Qubits 1)) =
      (rotZOp (a + b) : HilbertOperator (Qubits 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZOp, Matrix.mul_apply, add_mul, Complex.exp_add]
  ring

private lemma matrix_smul_mul_smul_mul (A B C : HilbertOperator (Qubits 1)) (c d : ℂ) :
    (c • A) * ((d • B) * C) = (c * d) • (A * B * C) := by
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp [mul_assoc]

/-- Reassociate the source's `R`-signal bridge phases around one signal block.
This is the local matrix identity used in converting `W`-convention QSP
products into `R`-convention projected-QSVT products
[GSLW19, BlockHam.tex:514-528]. -/
private lemma rotZ_singularSignalR_rotZ_reassociate (a b c d x : ℝ) :
    (rotZOp a : HilbertOperator (Qubits 1)) *
        ((rotZOp b : HilbertOperator (Qubits 1)) * singularSignalR x *
          (rotZOp c : HilbertOperator (Qubits 1))) *
        (rotZOp d : HilbertOperator (Qubits 1)) =
      (rotZOp (a + b) : HilbertOperator (Qubits 1)) *
        singularSignalR x * (rotZOp (c + d) : HilbertOperator (Qubits 1)) := by
  calc
    (rotZOp a : HilbertOperator (Qubits 1)) *
        ((rotZOp b : HilbertOperator (Qubits 1)) * singularSignalR x *
          (rotZOp c : HilbertOperator (Qubits 1))) *
        (rotZOp d : HilbertOperator (Qubits 1))
        = ((rotZOp a : HilbertOperator (Qubits 1)) *
            (rotZOp b : HilbertOperator (Qubits 1))) *
          singularSignalR x *
            ((rotZOp c : HilbertOperator (Qubits 1)) *
              (rotZOp d : HilbertOperator (Qubits 1))) := by
          noncomm_ring
    _ = (rotZOp (a + b) : HilbertOperator (Qubits 1)) *
        singularSignalR x * (rotZOp (c + d) : HilbertOperator (Qubits 1)) := by
          rw [rotZ_op_mul, rotZ_op_mul]

/-- The raw `R`-product appearing before the source absorbs the terminal scalar
phase into the first projected-QSVT phase [GSLW19, BlockHam.tex:514-528]. -/
noncomputable def singularSignalRRawProduct (φ₀ : ℝ) (init : List ℝ) (x : ℝ) :
    HilbertOperator (Qubits 1) :=
  singularSignalRProduct ((φ₀ - Real.pi / 4) :: init.map (fun φ => φ - Real.pi / 2)) x

/-- The raw source `R`-product certified on the physical singular-value
domain. -/
noncomputable def singularSignalRRawProductOperator (φ₀ : ℝ)
    (init : List ℝ) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    UnitaryOperator (Qubits 1) :=
  singularSignalRProductOperator
    ((φ₀ - Real.pi / 4) :: init.map (fun φ => φ - Real.pi / 2)) x hx

@[simp]
lemma singularSignalRRawProductOperator_coe (φ₀ : ℝ)
    (init : List ℝ) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (singularSignalRRawProductOperator φ₀ init x hx :
      HilbertOperator (Qubits 1)) = singularSignalRRawProduct φ₀ init x := by
  simp [singularSignalRRawProductOperator, singularSignalRRawProduct]

-- Mathlib linter exception: this induction depends on the existing broad
-- simplification shape of the imported single-qubit `qspW` product.
set_option linter.flexible false in
/-- Source `W`-convention QSP products equal the raw `R`-convention projected
QSVT product, up to the scalar `i^{L}` and the terminal source phase.  This is
the product form of the phase conversion in [GSLW19, BlockHam.tex:514-528]. -/
lemma qspW_eq_I_pow_smul_rawProduct_mul_terminal (φ₀ : ℝ)
    (init : List ℝ) (last x : ℝ) :
    qspW φ₀ (init ++ [last]) x =
      (Complex.I ^ (init.length + 1)) •
        (singularSignalRRawProduct φ₀ init x *
          (rotZOp (last - Real.pi / 4) : HilbertOperator (Qubits 1))) := by
  revert last
  induction init using List.reverseRecOn with
  | nil =>
      intro last
      simp [qspW, singularSignalRRawProduct, singularSignalRProduct,
        signalW_eq_I_smul_rotZ_mul_singularSignalR_mul_rotZ]
      rw [show (rotZOp φ₀ : HilbertOperator (Qubits 1)) *
          ((rotZOp (-(Real.pi / 4)) : HilbertOperator (Qubits 1)) * singularSignalR x *
            (rotZOp (-(Real.pi / 4)) : HilbertOperator (Qubits 1)) *
              (rotZOp last : HilbertOperator (Qubits 1))) =
        (rotZOp φ₀ : HilbertOperator (Qubits 1)) *
          ((rotZOp (-(Real.pi / 4)) : HilbertOperator (Qubits 1)) * singularSignalR x *
            (rotZOp (-(Real.pi / 4)) : HilbertOperator (Qubits 1))) *
          (rotZOp last : HilbertOperator (Qubits 1)) by noncomm_ring]
      calc
        (rotZOp φ₀) *
            ((rotZOp (-(Real.pi / 4))) * singularSignalR x *
              (rotZOp (-(Real.pi / 4)))) *
            (rotZOp last) =
          (rotZOp (φ₀ + -(Real.pi / 4))) *
            singularSignalR x * (rotZOp (-(Real.pi / 4) + last)) := by
            simpa using
              rotZ_singularSignalR_rotZ_reassociate φ₀ (-(Real.pi / 4))
                (-(Real.pi / 4)) last x
        _ =
          (rotZOp (φ₀ - Real.pi / 4)) * singularSignalR x *
            (rotZOp (last - Real.pi / 4)) := by
            congr 2
            all_goals ring_nf
  | append_singleton init φ ih =>
      intro last
      rw [show init ++ [φ] ++ [last] = (init ++ [φ]) ++ [last] by simp]
      rw [qspW_concat, ih φ]
      rw [signalW_eq_I_smul_rotZ_mul_singularSignalR_mul_rotZ]
      rw [matrix_smul_mul_smul_mul]
      unfold singularSignalRRawProduct
      rw [List.map_append]
      change (Complex.I ^ (init.length + 1) * Complex.I) •
          (singularSignalRProduct ((φ₀ - Real.pi / 4) ::
                List.map (fun φ => φ - Real.pi / 2) init) x *
              (rotZOp (φ - Real.pi / 4)) *
            ((rotZOp (-(Real.pi / 4))) * singularSignalR x *
                (rotZOp (-(Real.pi / 4)))) *
              (rotZOp last)) =
        Complex.I ^ ((init ++ [φ]).length + 1) •
          (singularSignalRProduct
              (((φ₀ - Real.pi / 4) ::
                List.map (fun φ => φ - Real.pi / 2) init) ++ [φ - Real.pi / 2]) x *
            (rotZOp (last - Real.pi / 4)))
      rw [singularSignalRProduct_append_singleton]
      rw [show (Complex.I ^ (init.length + 1) * Complex.I) =
          Complex.I ^ ((init ++ [φ]).length + 1) by
        simp [pow_succ]]
      have hmatrix :
          singularSignalRProduct ((φ₀ - Real.pi / 4) ::
                List.map (fun φ => φ - Real.pi / 2) init) x *
              (rotZOp (φ - Real.pi / 4)) *
            ((rotZOp (-(Real.pi / 4))) * singularSignalR x *
                (rotZOp (-(Real.pi / 4)))) *
              (rotZOp last) =
          singularSignalRProduct ((φ₀ - Real.pi / 4) ::
                List.map (fun φ => φ - Real.pi / 2) init) x *
            ((rotZOp (φ - Real.pi / 2)) * singularSignalR x) *
              (rotZOp (last - Real.pi / 4)) := by
        have hblock :
            (rotZOp (φ - Real.pi / 4)) *
                ((rotZOp (-(Real.pi / 4))) * singularSignalR x *
                  (rotZOp (-(Real.pi / 4)))) *
                (rotZOp last) =
              (rotZOp (φ - Real.pi / 2)) * singularSignalR x *
                (rotZOp (last - Real.pi / 4)) := by
          calc
            (rotZOp (φ - Real.pi / 4)) *
                ((rotZOp (-(Real.pi / 4))) * singularSignalR x *
                  (rotZOp (-(Real.pi / 4)))) *
                (rotZOp last) =
              (rotZOp ((φ - Real.pi / 4) + -(Real.pi / 4))) *
                singularSignalR x * (rotZOp (-(Real.pi / 4) + last)) := by
                simpa using
                  rotZ_singularSignalR_rotZ_reassociate (φ - Real.pi / 4)
                    (-(Real.pi / 4)) (-(Real.pi / 4)) last x
            _ =
              (rotZOp (φ - Real.pi / 2)) * singularSignalR x *
                (rotZOp (last - Real.pi / 4)) := by
                congr 2
                all_goals ring_nf
        calc
          singularSignalRProduct ((φ₀ - Real.pi / 4) ::
                List.map (fun φ => φ - Real.pi / 2) init) x *
              (rotZOp (φ - Real.pi / 4)) *
            ((rotZOp (-(Real.pi / 4))) * singularSignalR x *
                (rotZOp (-(Real.pi / 4)))) *
              (rotZOp last)
              =
            singularSignalRProduct ((φ₀ - Real.pi / 4) ::
                List.map (fun φ => φ - Real.pi / 2) init) x *
              ((rotZOp (φ - Real.pi / 4)) *
                ((rotZOp (-(Real.pi / 4))) * singularSignalR x *
                  (rotZOp (-(Real.pi / 4)))) *
                (rotZOp last)) := by
                noncomm_ring
          _ =
            singularSignalRProduct ((φ₀ - Real.pi / 4) ::
                List.map (fun φ => φ - Real.pi / 2) init) x *
              ((rotZOp (φ - Real.pi / 2)) * singularSignalR x *
                (rotZOp (last - Real.pi / 4))) := by
                rw [hblock]
          _ =
            singularSignalRProduct ((φ₀ - Real.pi / 4) ::
                List.map (fun φ => φ - Real.pi / 2) init) x *
              ((rotZOp (φ - Real.pi / 2)) * singularSignalR x) *
                (rotZOp (last - Real.pi / 4)) := by
                noncomm_ring
      rw [hmatrix]

/-- Right multiplication by `rotZOp` multiplies the `(0,0)` entry by the positive
phase. -/
private lemma mul_rotZ_zero_zero (A : HilbertOperator (Qubits 1)) (θ : ℝ) :
    (A * (rotZOp θ : HilbertOperator (Qubits 1))) 0 0 =
      A 0 0 * Complex.exp ((θ : ℂ) * Complex.I) := by
  simp [rotZOp, Matrix.mul_apply]

/-- The scalar part of the source phase conversion
[GSLW19, BlockHam.tex:523-528]. -/
lemma I_pow_mul_terminal_phase (n : Nat) (last : ℝ) :
    Complex.I ^ (n + 1) * Complex.exp (((last - Real.pi / 4 : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((last + n * (Real.pi / 2) + Real.pi / 4 : ℝ) : ℂ) *
        Complex.I) := by
  have hstep (θ : ℝ) :
      Complex.exp ((θ : ℂ) * Complex.I) * Complex.I =
        Complex.exp (((θ + Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    calc
      Complex.exp ((θ : ℂ) * Complex.I) * Complex.I =
          Complex.exp ((θ : ℂ) * Complex.I) *
            Complex.exp ((Real.pi : ℂ) / 2 * Complex.I) := by
            rw [exp_pi_div_two_mul_I]
      _ = Complex.exp (((θ : ℂ) * Complex.I) +
            ((Real.pi : ℂ) / 2 * Complex.I)) := by
            rw [Complex.exp_add]
      _ = Complex.exp (((θ + Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
            congr 1
            norm_num
            ring_nf
  induction n with
  | zero =>
      rw [pow_one]
      rw [show Complex.I * Complex.exp (((last - Real.pi / 4 : ℝ) : ℂ) * Complex.I) =
          Complex.exp (((last - Real.pi / 4 : ℝ) : ℂ) * Complex.I) * Complex.I by ring]
      rw [hstep]
      congr 1
      norm_num
      ring_nf
  | succ n ih =>
      rw [show Complex.I ^ (n + 1 + 1) *
          Complex.exp (((last - Real.pi / 4 : ℝ) : ℂ) * Complex.I) =
          (Complex.I ^ (n + 1) *
            Complex.exp (((last - Real.pi / 4 : ℝ) : ℂ) * Complex.I)) * Complex.I by
          rw [pow_succ]
          ring]
      rw [ih]
      rw [hstep]
      congr 1
      norm_num
      ring_nf

-- Mathlib linter exception: the terminal phase proof relies on the current
-- matrix-entry expansion of `rotZOp` and the raw QSP product.
set_option linter.flexible false in
/-- The `(0,0)` entry of the `W`-convention QSP product equals the raw
`R`-product entry with the source scalar phase absorbed
[GSLW19, BlockHam.tex:514-528]. -/
lemma qspW_zero_zero_eq_rawProduct (φ₀ : ℝ) (init : List ℝ) (last x : ℝ) :
    qspW φ₀ (init ++ [last]) x 0 0 =
      Complex.exp (((last + init.length * (Real.pi / 2) + Real.pi / 4 : ℝ) : ℂ) *
          Complex.I) * singularSignalRRawProduct φ₀ init x 0 0 := by
  rw [qspW_eq_I_pow_smul_rawProduct_mul_terminal]
  simp [Matrix.mul_apply, rotZOp]
  change Complex.I ^ (init.length + 1) *
      (singularSignalRRawProduct φ₀ init x 0 0 *
        Complex.exp (((last : ℂ) - (Real.pi : ℂ) / 4) * Complex.I)) =
    Complex.exp (((last : ℂ) + (init.length : ℂ) * ((Real.pi : ℂ) / 2) +
        (Real.pi : ℂ) / 4) * Complex.I) *
      singularSignalRRawProduct φ₀ init x 0 0
  have hphase :
      Complex.I ^ (init.length + 1) *
          Complex.exp (((last : ℂ) - (Real.pi : ℂ) / 4) * Complex.I) =
        Complex.exp (((last : ℂ) + (init.length : ℂ) * ((Real.pi : ℂ) / 2) +
            (Real.pi : ℂ) / 4) * Complex.I) := by
    simpa using I_pow_mul_terminal_phase init.length last
  calc
    Complex.I ^ (init.length + 1) *
        (singularSignalRRawProduct φ₀ init x 0 0 *
          Complex.exp (((last : ℂ) - (Real.pi : ℂ) / 4) * Complex.I))
        =
      (Complex.I ^ (init.length + 1) *
          Complex.exp (((last : ℂ) - (Real.pi : ℂ) / 4) * Complex.I)) *
        singularSignalRRawProduct φ₀ init x 0 0 := by
        ring
    _ =
      Complex.exp (((last : ℂ) + (init.length : ℂ) * ((Real.pi : ℂ) / 2) +
          (Real.pi : ℂ) / 4) * Complex.I) *
        singularSignalRRawProduct φ₀ init x 0 0 := by
        rw [hphase]

-- Mathlib linter exception: this entrywise product proof is intentionally
-- kept close to the source phase algebra.
set_option linter.flexible false in
/-- Changing only the first source `R`-product phase multiplies the `(0,0)`
entry by the corresponding scalar phase [GSLW19, BlockHam.tex:523-528]. -/
lemma singularSignalRProduct_first_phase_zero_zero
    (a b : ℝ) (tail : List ℝ) (x : ℝ) :
    singularSignalRProduct (a :: tail) x 0 0 =
      Complex.exp (((a : ℂ) - (b : ℂ)) * Complex.I) *
        singularSignalRProduct (b :: tail) x 0 0 := by
  rw [singularSignalRProduct_cons, singularSignalRProduct_cons]
  simp [rotZOp, Matrix.mul_apply, Matrix.vecMul, dotProduct]
  have h_exp :
      Complex.exp (((a : ℂ) - (b : ℂ)) * Complex.I) *
          Complex.exp ((b : ℂ) * Complex.I) =
        Complex.exp ((a : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [mul_add]
  repeat rw [← mul_assoc]
  rw [h_exp]

lemma phaseProduct_eq_exp_sum (phases : List ℝ) :
    phaseProduct phases = Complex.exp (((phases.sum : ℝ) : ℂ) * Complex.I) := by
  induction phases with
  | nil =>
      simp [phaseProduct]
  | cons φ phases ih =>
      rw [phaseProduct_cons, ih, ← Complex.exp_add]
      congr 1
      norm_num
      ring

private lemma list_sum_map_const_add (c : ℝ) (xs : List ℝ) :
    (xs.map fun x => c + x).sum = xs.length * c + xs.sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih]
      ring_nf

private lemma list_sum_map_sub_const (c : ℝ) (xs : List ℝ) :
    (xs.map fun x => x - c).sum = xs.sum - xs.length * c := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih]
      ring_nf

namespace SourceUnitSingularBlock

/-- On a one-dimensional singular-value-one block, the source alternating
phase sequence alternates between the right and left singular vectors and
accumulates the product of the scalar projector phases [GSLW19,
BlockHam.tex:655-671,738-849]. -/
lemma sourceAlternating_applyVec_rightVec {N : Nat}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right) :
    ∀ phases : List ℝ,
      (phases.length % 2 = 0 →
        (Native.sourceWord U left right phases).applyVec block.rightVec =
          phaseProduct phases • block.rightVec) ∧
      (phases.length % 2 = 1 →
        (Native.sourceWord U left right phases).applyVec block.rightVec =
          phaseProduct phases • block.leftVec) := by
  intro phases
  induction phases with
  | nil =>
      constructor
      · intro _
        simp [Native.sourceWord]
      · intro h
        norm_num at h
  | cons φ phases ih =>
      constructor
      · intro hlen
        have hrem : (phases.length + 1) % 2 = 0 := by
          exact hlen
        have htail : phases.length % 2 = 1 := by omega
        rw [sourceAlternatingPhaseModulation_cons_applyVec]
        have htail_action :
            (Native.sourceWord U left right phases).applyVec block.rightVec =
              phaseProduct phases • block.leftVec :=
          ih.2 htail
        rw [htail_action, UnitaryOperator.applyVec_smul]
        rw [SourceUnitSingularBlock.even_signal_on_leftVec block
          (remaining := phases.length + 1) hrem]
        change (projectorPhaseOp φ (sourcePhaseProjector left right (phases.length + 1))).applyVec
            (phaseProduct phases • block.rightVec) =
          phaseProduct (φ :: phases) • block.rightVec
        rw [UnitaryOperator.applyVec_smul]
        have hphase :
            (projectorPhaseOp φ (sourcePhaseProjector left right (phases.length + 1))).applyVec
              block.rightVec =
                Complex.exp (φ * Complex.I) • block.rightVec := by
          have hp : sourcePhaseProjector left right (phases.length + 1) = right := by
            simpa [sourcePhaseProjector] using
              (projectedOutputProjector_of_even left right (L := phases.length + 1) hrem)
          rw [hp]
          change HilbertOperator.applyVec (projectorPhaseOp φ right) block.rightVec =
            Complex.exp (φ * Complex.I) • block.rightVec
          exact SourceUnitSingularBlock.right_phase_on_rightVec block φ
        rw [hphase]
        rw [phaseProduct_cons, smul_smul]
        have hmul :
            phaseProduct phases * Complex.exp (φ * Complex.I) =
              Complex.exp (φ * Complex.I) * phaseProduct phases := by ring
        rw [hmul]
      · intro hlen
        have hrem : (phases.length + 1) % 2 = 1 := by
          exact hlen
        have htail : phases.length % 2 = 0 := by omega
        have hrem_ne : (phases.length + 1) % 2 ≠ 0 := by omega
        rw [sourceAlternatingPhaseModulation_cons_applyVec]
        have htail_action :
            (Native.sourceWord U left right phases).applyVec block.rightVec =
              phaseProduct phases • block.rightVec :=
          ih.1 htail
        rw [htail_action, UnitaryOperator.applyVec_smul]
        rw [SourceUnitSingularBlock.odd_signal_on_rightVec block
          (remaining := phases.length + 1) hrem_ne]
        change (projectorPhaseOp φ (sourcePhaseProjector left right (phases.length + 1))).applyVec
            (phaseProduct phases • block.leftVec) =
          phaseProduct (φ :: phases) • block.leftVec
        rw [UnitaryOperator.applyVec_smul]
        have hphase :
            (projectorPhaseOp φ (sourcePhaseProjector left right (phases.length + 1))).applyVec
              block.leftVec =
                Complex.exp (φ * Complex.I) • block.leftVec := by
          have hp : sourcePhaseProjector left right (phases.length + 1) = left := by
            simpa [sourcePhaseProjector] using
              (projectedOutputProjector_of_odd left right (L := phases.length + 1) hrem_ne)
          rw [hp]
          change HilbertOperator.applyVec (projectorPhaseOp φ left) block.leftVec =
            Complex.exp (φ * Complex.I) • block.leftVec
          exact SourceUnitSingularBlock.left_phase_on_leftVec block φ
        rw [hphase]
        rw [phaseProduct_cons, smul_smul]
        have hmul :
            phaseProduct phases * Complex.exp (φ * Complex.I) =
              Complex.exp (φ * Complex.I) * phaseProduct phases := by ring
        rw [hmul]

end SourceUnitSingularBlock

namespace SourceTwoDimensionalSingularBlock

/-- On a nontrivial two-dimensional singular block, the source alternating
phase sequence has exactly the coordinates of the source `R`-convention QSP
product.  This is the local block computation used in
`thm:singValTransformation` before projecting onto the singular-vector
component [GSLW19, BlockHam.tex:655-735,768-849]. -/
lemma sourceAlternating_applyVec_rightVec_singularSignalRProduct {N : Nat}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) :
    ∀ phases : List ℝ,
      (phases.length % 2 = 0 →
        (Native.sourceWord U left right phases).applyVec block.rightVec =
          singularSignalRProduct phases block.σ 0 0 • block.rightVec +
            singularSignalRProduct phases block.σ 1 0 • block.rightPerp) ∧
      (phases.length % 2 = 1 →
        (Native.sourceWord U left right phases).applyVec block.rightVec =
          singularSignalRProduct phases block.σ 0 0 • block.leftVec +
            singularSignalRProduct phases block.σ 1 0 • block.leftPerp) := by
  intro phases
  induction phases with
  | nil =>
      constructor
      · intro _
        simp [Native.sourceWord]
      · intro h
        norm_num at h
  | cons φ phases ih =>
      constructor
      · intro hlen
        have hrem : (phases.length + 1) % 2 = 0 := by
          exact hlen
        have htail : phases.length % 2 = 1 := by omega
        rw [sourceAlternatingPhaseModulation_cons_applyVec]
        have htail_action :
            (Native.sourceWord U left right phases).applyVec block.rightVec =
              singularSignalRProduct phases block.σ 0 0 • block.leftVec +
                singularSignalRProduct phases block.σ 1 0 • block.leftPerp :=
          ih.2 htail
        rw [htail_action, UnitaryOperator.applyVec_add,
          UnitaryOperator.applyVec_smul, UnitaryOperator.applyVec_smul]
        rw [SourceTwoDimensionalSingularBlock.even_signal_on_leftVec block
          (remaining := phases.length + 1) hrem]
        rw [SourceTwoDimensionalSingularBlock.even_signal_on_leftPerp block
          (remaining := phases.length + 1) hrem]
        rw [UnitaryOperator.applyVec_add,
          UnitaryOperator.applyVec_smul,
          UnitaryOperator.applyVec_smul,
          UnitaryOperator.applyVec_add,
          UnitaryOperator.applyVec_smul,
          UnitaryOperator.applyVec_smul,
          UnitaryOperator.applyVec_add,
          UnitaryOperator.applyVec_smul,
          UnitaryOperator.applyVec_smul]
        have hphase_right :
            (projectorPhaseOp φ (sourcePhaseProjector left right (phases.length + 1))).applyVec
              block.rightVec =
                Complex.exp (φ * Complex.I) • block.rightVec := by
          have hp : sourcePhaseProjector left right (phases.length + 1) = right := by
            simpa [sourcePhaseProjector] using
              (projectedOutputProjector_of_even left right (L := phases.length + 1) hrem)
          rw [hp]
          change HilbertOperator.applyVec (projectorPhaseOp φ right) block.rightVec =
            Complex.exp (φ * Complex.I) • block.rightVec
          exact SourceTwoDimensionalSingularBlock.right_phase_on_rightVec block φ
        have hphase_right_perp :
            (projectorPhaseOp φ (sourcePhaseProjector left right (phases.length + 1))).applyVec
              block.rightPerp =
                Complex.exp (-(φ * Complex.I)) • block.rightPerp := by
          have hp : sourcePhaseProjector left right (phases.length + 1) = right := by
            simpa [sourcePhaseProjector] using
              (projectedOutputProjector_of_even left right (L := phases.length + 1) hrem)
          rw [hp]
          change HilbertOperator.applyVec (projectorPhaseOp φ right) block.rightPerp =
            Complex.exp (-(φ * Complex.I)) • block.rightPerp
          exact SourceTwoDimensionalSingularBlock.right_phase_on_rightPerp block φ
        rw [hphase_right, hphase_right_perp]
        simp [singularSignalRProduct, singularSignalR, rotZOp, Matrix.mul_apply]
        module
      · intro hlen
        have hrem : (phases.length + 1) % 2 = 1 := by
          exact hlen
        have htail : phases.length % 2 = 0 := by omega
        have hrem_ne : (phases.length + 1) % 2 ≠ 0 := by omega
        rw [sourceAlternatingPhaseModulation_cons_applyVec]
        have htail_action :
            (Native.sourceWord U left right phases).applyVec block.rightVec =
              singularSignalRProduct phases block.σ 0 0 • block.rightVec +
                singularSignalRProduct phases block.σ 1 0 • block.rightPerp :=
          ih.1 htail
        rw [htail_action, UnitaryOperator.applyVec_add,
          UnitaryOperator.applyVec_smul, UnitaryOperator.applyVec_smul]
        rw [SourceTwoDimensionalSingularBlock.odd_signal_on_rightVec block
          (remaining := phases.length + 1) hrem_ne]
        rw [SourceTwoDimensionalSingularBlock.odd_signal_on_rightPerp block
          (remaining := phases.length + 1) hrem_ne]
        rw [UnitaryOperator.applyVec_add,
          UnitaryOperator.applyVec_smul,
          UnitaryOperator.applyVec_smul,
          UnitaryOperator.applyVec_add,
          UnitaryOperator.applyVec_smul,
          UnitaryOperator.applyVec_smul,
          UnitaryOperator.applyVec_add,
          UnitaryOperator.applyVec_smul,
          UnitaryOperator.applyVec_smul]
        have hphase_left :
            (projectorPhaseOp φ (sourcePhaseProjector left right (phases.length + 1))).applyVec
              block.leftVec =
                Complex.exp (φ * Complex.I) • block.leftVec := by
          have hp : sourcePhaseProjector left right (phases.length + 1) = left := by
            simpa [sourcePhaseProjector] using
              (projectedOutputProjector_of_odd left right (L := phases.length + 1) hrem_ne)
          rw [hp]
          change HilbertOperator.applyVec (projectorPhaseOp φ left) block.leftVec =
            Complex.exp (φ * Complex.I) • block.leftVec
          exact SourceTwoDimensionalSingularBlock.left_phase_on_leftVec block φ
        have hphase_left_perp :
            (projectorPhaseOp φ (sourcePhaseProjector left right (phases.length + 1))).applyVec
              block.leftPerp =
                Complex.exp (-(φ * Complex.I)) • block.leftPerp := by
          have hp : sourcePhaseProjector left right (phases.length + 1) = left := by
            simpa [sourcePhaseProjector] using
              (projectedOutputProjector_of_odd left right (L := phases.length + 1) hrem_ne)
          rw [hp]
          change HilbertOperator.applyVec (projectorPhaseOp φ left) block.leftPerp =
            Complex.exp (-(φ * Complex.I)) • block.leftPerp
          exact SourceTwoDimensionalSingularBlock.left_phase_on_leftPerp block φ
        rw [hphase_left, hphase_left_perp]
        simp [singularSignalRProduct, singularSignalR, rotZOp, Matrix.mul_apply]
        module

end SourceTwoDimensionalSingularBlock

namespace SourceRightKernelSingularBlock

/-- On a right-kernel singular block (`σ = 0`), the source alternating phase
sequence follows the `R(0)` local product: even lengths return to the right
singular vector, and odd lengths land in the left-complement vector.  This is
the zero-singular-value right-sector part of `thm:singValTransformation`
[GSLW19, BlockHam.tex:599-611,655-716,768-849]. -/
lemma sourceAlternating_applyVec_rightVec_singularSignalRProduct_zero {N : Nat}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right) :
    ∀ phases : List ℝ,
      (phases.length % 2 = 0 →
        (Native.sourceWord U left right phases).applyVec block.rightVec =
          singularSignalRProduct phases 0 0 0 • block.rightVec) ∧
      (phases.length % 2 = 1 →
        (Native.sourceWord U left right phases).applyVec block.rightVec =
          singularSignalRProduct phases 0 1 0 • block.leftPerp) := by
  intro phases
  induction phases with
  | nil =>
      constructor
      · intro _
        simp [Native.sourceWord]
      · intro h
        norm_num at h
  | cons φ phases ih =>
      constructor
      · intro hlen
        have hrem : (phases.length + 1) % 2 = 0 := by
          exact hlen
        have htail : phases.length % 2 = 1 := by omega
        rw [sourceAlternatingPhaseModulation_cons_applyVec]
        have htail_action :
            (Native.sourceWord U left right phases).applyVec block.rightVec =
              singularSignalRProduct phases 0 1 0 • block.leftPerp :=
          ih.2 htail
        rw [htail_action, UnitaryOperator.applyVec_smul]
        rw [SourceRightKernelSingularBlock.even_signal_on_leftPerp block
          (remaining := phases.length + 1) hrem]
        rw [UnitaryOperator.applyVec_smul]
        have hphase_right :
            (projectorPhaseOp φ (sourcePhaseProjector left right (phases.length + 1))).applyVec
              block.rightVec =
                Complex.exp (φ * Complex.I) • block.rightVec := by
          have hp : sourcePhaseProjector left right (phases.length + 1) = right := by
            simpa [sourcePhaseProjector] using
              (projectedOutputProjector_of_even left right (L := phases.length + 1) hrem)
          rw [hp]
          change HilbertOperator.applyVec (projectorPhaseOp φ right) block.rightVec =
            Complex.exp (φ * Complex.I) • block.rightVec
          exact SourceRightKernelSingularBlock.right_phase_on_rightVec block φ
        rw [hphase_right]
        simp [singularSignalRProduct, singularSignalR, rotZOp, Matrix.mul_apply,
          smul_smul, mul_comm]
      · intro hlen
        have hrem : (phases.length + 1) % 2 = 1 := by
          exact hlen
        have htail : phases.length % 2 = 0 := by omega
        have hrem_ne : (phases.length + 1) % 2 ≠ 0 := by omega
        rw [sourceAlternatingPhaseModulation_cons_applyVec]
        have htail_action :
            (Native.sourceWord U left right phases).applyVec block.rightVec =
              singularSignalRProduct phases 0 0 0 • block.rightVec :=
          ih.1 htail
        rw [htail_action, UnitaryOperator.applyVec_smul]
        rw [SourceRightKernelSingularBlock.odd_signal_on_rightVec block
          (remaining := phases.length + 1) hrem_ne]
        rw [UnitaryOperator.applyVec_smul]
        have hphase_left_perp :
            (projectorPhaseOp φ (sourcePhaseProjector left right (phases.length + 1))).applyVec
              block.leftPerp =
                Complex.exp (-(φ * Complex.I)) • block.leftPerp := by
          have hp : sourcePhaseProjector left right (phases.length + 1) = left := by
            simpa [sourcePhaseProjector] using
              (projectedOutputProjector_of_odd left right (L := phases.length + 1) hrem_ne)
          rw [hp]
          change HilbertOperator.applyVec (projectorPhaseOp φ left) block.leftPerp =
            Complex.exp (-(φ * Complex.I)) • block.leftPerp
          exact SourceRightKernelSingularBlock.left_phase_on_leftPerp block φ
        rw [hphase_left_perp]
        simp [singularSignalRProduct, singularSignalR, rotZOp, Matrix.mul_apply,
          smul_smul, mul_comm]

end SourceRightKernelSingularBlock

end QuantumAlg.QSP.MultiQubit.QSVT
end
