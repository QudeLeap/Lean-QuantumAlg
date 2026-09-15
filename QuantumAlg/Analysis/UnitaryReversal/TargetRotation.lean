/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.State.Normalized

public import QuantumAlg.Analysis.UnitaryReversal.Orthonormality

/-!
# Target-dependent span rotation

A mathematical rotation built from the target adjoint subspace and its
orthogonal companion. Its formula depends on the target U†. This module
proves the resulting matrix identity; it supplies no construction using
only calls to U and makes no oracle-query bound.
-/

@[expose] public section

namespace QuantumAlg.UnitaryReversal

noncomputable section

open MatrixWeyl

-- Preserve symbolic basis coefficients until a proof requests their entry formula.
attribute [-simp] NormalizedVector.ket_apply

variable {d : ℕ}




/-- The nonnegative round count `max(0, floor(π / (2θ)) - 1)` for the target-dependent rotation. -/
def quraRounds (hd : 1 ≤ d) : ℕ :=
  let θ := quraAngle hd
  let k := Int.floor (Real.pi / (2 * θ))
  max 0 ((k - 1).toNat)

/-! ## Rotation defined using the target subspace -/

/-- Projector onto the image of `Ψ₀ = |00⟩⊗U†`. -/
def quraPsi0Proj (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × (Fin d × Fin d)) (Fin d × (Fin d × Fin d)) ℂ :=
  quraPsi0 d U * (quraPsi0 d U).conjTranspose

/-- Projector onto the image of `Ψ⊥`. -/
def quraPsiPerpProj (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × (Fin d × Fin d)) (Fin d × (Fin d × Fin d)) ℂ :=
  quraPsiPerp d U * (quraPsiPerp d U).conjTranspose

/-- The final rotation block: rotates `Span(Ψ₀, Ψ⊥)` by `β` and fixes the complement. -/
def targetDependentRotationBlock (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) (β : ℂ) :
    Matrix (Fin d × (Fin d × Fin d)) (Fin d × (Fin d × Fin d)) ℂ :=
  1 - quraPsi0Proj d U - quraPsiPerpProj d U +
    Complex.cos β • quraPsi0Proj d U + Complex.cos β • quraPsiPerpProj d U +
    Complex.sin β • (quraPsiPerp d U * (quraPsi0 d U).conjTranspose) -
    Complex.sin β • (quraPsi0 d U * (quraPsiPerp d U).conjTranspose)

lemma quraPsi0Proj_mul_psi0 (d : ℕ) [NeZero d] (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quraPsi0Proj d U * quraPsi0 d U = quraPsi0 d U := by
  calc
    quraPsi0Proj d U * quraPsi0 d U
        = quraPsi0 d U * ((quraPsi0 d U).conjTranspose * quraPsi0 d U) := by
          rw [quraPsi0Proj, Matrix.mul_assoc]
    _ = quraPsi0 d U * (1 : Matrix (Fin d) (Fin d) ℂ) := by
          rw [quraPsi0_adjoint_self d U hU]
    _ = quraPsi0 d U := by simp

lemma quraPsi0Proj_mul_psiPerp (d : ℕ) [NeZero d] (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quraPsi0Proj d U * quraPsiPerp d U = 0 := by
  calc
    quraPsi0Proj d U * quraPsiPerp d U
        = quraPsi0 d U * ((quraPsi0 d U).conjTranspose * quraPsiPerp d U) := by
          rw [quraPsi0Proj, Matrix.mul_assoc]
    _ = quraPsi0 d U * (0 : Matrix (Fin d) (Fin d) ℂ) := by
          rw [quraPsi0_adjoint_psiPerp d U hU]
    _ = 0 := by simp

lemma quraPsiPerpProj_mul_psi0 (d : ℕ) [NeZero d] (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quraPsiPerpProj d U * quraPsi0 d U = 0 := by
  calc
    quraPsiPerpProj d U * quraPsi0 d U
        = quraPsiPerp d U * ((quraPsiPerp d U).conjTranspose * quraPsi0 d U) := by
          rw [quraPsiPerpProj, Matrix.mul_assoc]
    _ = quraPsiPerp d U * (0 : Matrix (Fin d) (Fin d) ℂ) := by
          rw [quraPsiPerp_adjoint_psi0 d U hU]
    _ = 0 := by simp

lemma quraPsiPerpProj_mul_psiPerp (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quraPsiPerpProj d U * quraPsiPerp d U = quraPsiPerp d U := by
  calc
    quraPsiPerpProj d U * quraPsiPerp d U
        = quraPsiPerp d U * ((quraPsiPerp d U).conjTranspose * quraPsiPerp d U) := by
          rw [quraPsiPerpProj, Matrix.mul_assoc]
    _ = quraPsiPerp d U * (1 : Matrix (Fin d) (Fin d) ℂ) := by
          rw [quraPsiPerp_adjoint_self d hd U hU]
    _ = quraPsiPerp d U := by simp

lemma quraPsiPerp_mul_psi0Adj_mul_psi0 (d : ℕ) [NeZero d] (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quraPsiPerp d U * (quraPsi0 d U).conjTranspose * quraPsi0 d U = quraPsiPerp d U := by
  calc
    quraPsiPerp d U * (quraPsi0 d U).conjTranspose * quraPsi0 d U
        = quraPsiPerp d U * ((quraPsi0 d U).conjTranspose * quraPsi0 d U) := by
          rw [Matrix.mul_assoc]
    _ = quraPsiPerp d U * (1 : Matrix (Fin d) (Fin d) ℂ) := by
          rw [quraPsi0_adjoint_self d U hU]
    _ = quraPsiPerp d U := by simp

lemma quraPsiPerp_mul_psi0Adj_mul_psiPerp (d : ℕ) [NeZero d] (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quraPsiPerp d U * (quraPsi0 d U).conjTranspose * quraPsiPerp d U = 0 := by
  calc
    quraPsiPerp d U * (quraPsi0 d U).conjTranspose * quraPsiPerp d U
        = quraPsiPerp d U * ((quraPsi0 d U).conjTranspose * quraPsiPerp d U) := by
          rw [Matrix.mul_assoc]
    _ = quraPsiPerp d U * (0 : Matrix (Fin d) (Fin d) ℂ) := by
          rw [quraPsi0_adjoint_psiPerp d U hU]
    _ = 0 := by simp

lemma quraPsi0_mul_psiPerpAdj_mul_psi0 (d : ℕ) [NeZero d] (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quraPsi0 d U * (quraPsiPerp d U).conjTranspose * quraPsi0 d U = 0 := by
  calc
    quraPsi0 d U * (quraPsiPerp d U).conjTranspose * quraPsi0 d U
        = quraPsi0 d U * ((quraPsiPerp d U).conjTranspose * quraPsi0 d U) := by
          rw [Matrix.mul_assoc]
    _ = quraPsi0 d U * (0 : Matrix (Fin d) (Fin d) ℂ) := by
          rw [quraPsiPerp_adjoint_psi0 d U hU]
    _ = 0 := by simp

lemma quraPsi0_mul_psiPerpAdj_mul_psiPerp (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    quraPsi0 d U * (quraPsiPerp d U).conjTranspose * quraPsiPerp d U = quraPsi0 d U := by
  calc
    quraPsi0 d U * (quraPsiPerp d U).conjTranspose * quraPsiPerp d U
        = quraPsi0 d U * ((quraPsiPerp d U).conjTranspose * quraPsiPerp d U) := by
          rw [Matrix.mul_assoc]
    _ = quraPsi0 d U * (1 : Matrix (Fin d) (Fin d) ℂ) := by
          rw [quraPsiPerp_adjoint_self d hd U hU]
    _ = quraPsi0 d U := by simp

/-- The final rotation block rotates the span: on `(Ψ₀, Ψ⊥)` it is the rotation by `−β`. -/
lemma targetDependentRotationBlock_mul_span (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (θ β : ℂ) :
    targetDependentRotationBlock d U β *
        (Complex.sin θ • quraPsi0 d U + Complex.cos θ • quraPsiPerp d U) =
      Complex.sin (θ - β) • quraPsi0 d U + Complex.cos (θ - β) • quraPsiPerp d U := by
  unfold targetDependentRotationBlock
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_mul, Matrix.sub_mul,
    quraPsi0Proj_mul_psi0 d U hU, quraPsi0Proj_mul_psiPerp d U hU,
    quraPsiPerpProj_mul_psi0 d U hU, quraPsiPerpProj_mul_psiPerp d hd U hU,
    quraPsiPerp_mul_psi0Adj_mul_psi0 d U hU, quraPsiPerp_mul_psi0Adj_mul_psiPerp d U hU,
    quraPsi0_mul_psiPerpAdj_mul_psi0 d U hU, quraPsi0_mul_psiPerpAdj_mul_psiPerp d hd U hU]
  ext a s
  simp [smul_eq_mul, mul_sub, add_mul, sub_mul, mul_assoc, mul_comm, mul_left_comm,
    Complex.sin_sub, Complex.cos_sub]
  ring

/-- A block matrix that acts as `F` on the ancilla-`|0⟩` block and as the
identity on the `|1⟩` block, applied to the `|0⟩⊗M` state. -/
lemma block_diag_ket0_mul (d : ℕ)
    (F : Matrix (Fin d × (Fin d × Fin d)) (Fin d × (Fin d × Fin d)) ℂ)
    (M : Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ) :
    (Matrix.of fun (x y : Fin 2 × (Fin d × (Fin d × Fin d))) =>
        if x.1 = 0 ∧ y.1 = 0 then F (x.2) (y.2) else if x = y then 1 else 0) *
      quraKet0Mat d M = quraKet0Mat d (F * M) := by
  ext a s
  rw [Matrix.mul_apply]
  simp only [quraKet0Mat]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (0 : Fin 2)]
  · by_cases ha : a.1 = 0
    · simp [ha, Matrix.mul_apply, NormalizedVector.ket_apply]
    · have hne : ∀ c : Fin d × (Fin d × Fin d), a ≠ (0, c) := by
        intro c h
        exact ha (by simpa using congrArg (fun z : Fin 2 × (Fin d × (Fin d × Fin d)) => z.1) h)
      simp [ha, hne, NormalizedVector.ket_apply]
  · intro i hi hi0
    have hi' : i ≠ (0 : Fin 2) := fun h => hi0 h
    apply Finset.sum_eq_zero
    intro c hc
    simp [hi', NormalizedVector.ket_apply]
  · intro h
    exact False.elim (h (Finset.mem_univ (0 : Fin 2)))

/-- The final rotation on the ancilla-`|0⟩` block, identity on the `|1⟩` block. -/
def targetDependentRotation (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) (β : ℂ) :
    Matrix (Fin 2 × (Fin d × (Fin d × Fin d))) (Fin 2 × (Fin d × (Fin d × Fin d))) ℂ :=
  Matrix.of fun (a b : Fin 2 × (Fin d × (Fin d × Fin d))) =>
    if a.1 = 0 ∧ b.1 = 0 then targetDependentRotationBlock d U β (a.2) (b.2)
    else if a = b then 1 else 0

/-- The final amplifier rotates the span: on `|0⟩⊗Span(Ψ₀, Ψ⊥)` it is the
rotation by `−β`. The formula depends on the target subspace. -/
lemma targetDependentRotation_mul_ket0_span (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (θ β : ℂ) :
    targetDependentRotation d U β * (Complex.sin θ • quraKet0Mat d (quraPsi0 d U) +
        Complex.cos θ • quraKet0Mat d (quraPsiPerp d U)) =
      Complex.sin (θ - β) • quraKet0Mat d (quraPsi0 d U) +
        Complex.cos (θ - β) • quraKet0Mat d (quraPsiPerp d U) := by
  rw [quraKet0Mat_smul_add]
  rw [quraKet0Mat_smul_add]
  rw [targetDependentRotation]
  rw [block_diag_ket0_mul d (targetDependentRotationBlock d U β)
    (Complex.sin θ • quraPsi0 d U + Complex.cos θ • quraPsiPerp d U)]
  congr 1
  exact targetDependentRotationBlock_mul_span d hd U hU θ β

/-- The final rotation angle `β = m·θ_d − π/2`. -/
def quraFinalAngle (hd : 1 ≤ d) (m : ℕ) : ℂ :=
  (((m : ℝ) * quraAngle hd - Real.pi / 2 : ℝ) : ℂ)

/-- `m·θ_d − β = π/2`: the final rotation completes the arc to the target. -/
lemma quraFinalAngle_sub (hd : 1 ≤ d) (m : ℕ) :
    ((m : ℕ) : ℂ) * quraTheta hd - quraFinalAngle hd m = ((Real.pi / 2 : ℝ) : ℂ) := by
  unfold quraFinalAngle
  have hmul : ((m : ℕ) : ℂ) * quraTheta hd = (((m : ℝ) * quraAngle hd : ℝ) : ℂ) := by
    simp [quraTheta, quraAngle, Complex.ofReal_natCast, Complex.ofReal_mul]
  rw [hmul]
  rw [Complex.ofReal_sub]
  ring

/-- For `m ≥ 1`, the target-dependent matrix product maps
`|0⟩⊗Λ₀` to `|0⟩⊗Ψ₀ = |0⟩⊗|00⟩⊗U†`. -/
theorem targetRotation_rounds_eq_adjointBlock (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (m : ℕ) (hm : 1 ≤ m) :
    targetDependentRotation d U (quraFinalAngle (by omega : 1 ≤ d) m) *
        (quraAmplifier d U) ^ (m - 1) * quraI2E d U * quraKet0Mat d (quraLambda0 d) =
      quraKet0Mat d (quraPsi0 d U) := by
  calc
    targetDependentRotation d U (quraFinalAngle (by omega : 1 ≤ d) m) *
        (quraAmplifier d U) ^ (m - 1) * quraI2E d U * quraKet0Mat d (quraLambda0 d)
        = targetDependentRotation d U (quraFinalAngle (by omega : 1 ≤ d) m) *
            ((quraAmplifier d U) ^ (m - 1) *
              (quraI2E d U * quraKet0Mat d (quraLambda0 d))) := by
          simp only [Matrix.mul_assoc]
    _ = targetDependentRotation d U (quraFinalAngle (by omega : 1 ≤ d) m) *
            ((quraAmplifier d U) ^ (m - 1) * quraEncodedState d U) := by
          rw [quraI2E_mul_ket0_lambda0 d hd U]
    _ = targetDependentRotation d U (quraFinalAngle (by omega : 1 ≤ d) m) *
            quraSpanState (by omega : 1 ≤ d) m U := by
          rw [quraAmplifier_pow_mul_encoded d hd U hU (m - 1)]
          rw [show (m - 1) + 1 = m by omega]
    _ = Complex.sin ((Real.pi / 2 : ℝ) : ℂ) • quraKet0Mat d (quraPsi0 d U) +
          Complex.cos ((Real.pi / 2 : ℝ) : ℂ) • quraKet0Mat d (quraPsiPerp d U) := by
          simp only [quraSpanState]
          rw [targetDependentRotation_mul_ket0_span d hd U hU
            (((m : ℕ) : ℂ) * quraTheta (by omega : 1 ≤ d)) (quraFinalAngle (by omega : 1 ≤ d) m)]
          rw [← quraFinalAngle_sub (by omega : 1 ≤ d) m]
    _ = quraKet0Mat d (quraPsi0 d U) := by
          simp

/-- For `d ≥ 2`, the number of amplifier rounds satisfies `1 ≤ m`. -/
lemma quraRounds_pos (hd : 2 ≤ d) : 1 ≤ quraRounds (by omega : 1 ≤ d) := by
  have hd1 : 1 ≤ d := by omega
  let θ : ℝ := quraAngle hd1
  have hθ_pos : 0 < θ := by
    dsimp [θ, quraAngle]
    rw [Real.arcsin_pos]
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    positivity
  have hθ_le : θ ≤ Real.pi / 6 := by
    dsimp [θ, quraAngle]
    have hle : (1 / (d : ℝ)) ≤ (1 / 2 : ℝ) := by
      exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hd : (2 : ℝ) ≤ d)
    have hm := Real.arcsin_le_arcsin hle
    have harcsin_half : Real.arcsin (2 : ℝ)⁻¹ = Real.pi / 6 := by
      rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
      rw [← Real.sin_pi_div_six]
      exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    simpa [harcsin_half] using hm
  have hx : 3 ≤ Real.pi / (2 * θ) := by
    have h2θ : 2 * θ ≤ Real.pi / 3 := by nlinarith [hθ_le]
    have h2θ_pos : 0 < 2 * θ := by nlinarith [hθ_pos]
    calc
      3 = Real.pi / (Real.pi / 3) := by field_simp [Real.pi_pos.ne']
      _ ≤ Real.pi / (2 * θ) := by
        exact div_le_div_of_nonneg_left Real.pi_pos.le h2θ_pos h2θ
  have hfloor : (3 : ℤ) ≤ Int.floor (Real.pi / (2 * θ)) := by
    exact Int.le_floor.mpr hx
  have hm' : 2 ≤ ((Int.floor (Real.pi / (2 * θ)) - 1).toNat : ℤ) := by
    have hnonneg : 0 ≤ Int.floor (Real.pi / (2 * θ)) - 1 := by omega
    rw [Int.toNat_of_nonneg hnonneg]
    omega
  have hm'' : 2 ≤ ((Int.floor (Real.pi / (2 * θ)) - 1).toNat : ℕ) := by
    exact_mod_cast hm'
  change 1 ≤ max 0 ((Int.floor (Real.pi / (2 * θ)) - 1).toNat)
  rw [max_eq_right (by omega : 0 ≤ ((Int.floor (Real.pi / (2 * θ)) - 1).toNat : ℕ))]
  omega

/-! ## Matrix identity with a target-dependent rotation -/

/-- Exact matrix identity after the selected rounds and a target-dependent rotation.
The determinant-one assumption is unnecessary for this mathematical statement. -/
theorem targetRotation_eq_adjointBlock [NeZero d] (hd : 2 ≤ d) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    targetDependentRotation d U
        (quraFinalAngle (by omega : 1 ≤ d) (quraRounds (by omega : 1 ≤ d))) *
        (quraAmplifier d U) ^ (quraRounds (by omega : 1 ≤ d) - 1) *
        quraI2E d U * quraKet0Mat d (quraLambda0 d) =
      quraKet0Mat d (quraPsi0 d U) := by
  exact targetRotation_rounds_eq_adjointBlock d hd U hU
    (quraRounds (by omega : 1 ≤ d)) (quraRounds_pos hd)

end

end QuantumAlg.UnitaryReversal
