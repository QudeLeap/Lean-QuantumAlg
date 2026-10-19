/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Analysis.UnitaryReversal.ModifiedAmplification.Action
public import QuantumAlg.Analysis.UnitaryReversal.ModifiedAmplification.Parameters

/-!
# Exact modified-amplifier matrix identity

A floor-parameter variant of the final matrix identity from
[CML+24, main.tex:680]. It combines encoder and amplifier formulas
that directly use conjugate input matrices. The floor schedule differs from
the source's ceiling-minus-one schedule at integer boundaries.
No U-only circuit, success observation, or query ledger is constructed here.
-/

@[expose] public section

namespace QuantumAlg.UnitaryReversal

noncomputable section

open MatrixWeyl

variable {d : ℕ}

/-- Floor-parameter matrix identity, motivated by [CML+24, main.tex:680]: with
`m = ⌊π/(2Δ_d)⌋`, `α = cos Δ_d / sin(m·Δ_d)` and `θ = m·Δ_d`, the modified
amplifier `A_α,θ(U)` completes `m−1` base amplifier rounds, so
`A_α,θ(U)·A(U)^(m−1)·(1₂⊗E(U))·(|0⟩⊗Λ₀) = |0⟩⊗Ψ₀ = |0⟩⊗|00⟩⊗U†`. -/
lemma modifiedAmplification_eq_adjointBlock (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    let m := quraFloorRounds (by omega : 1 ≤ d)
    let α : ℝ := Real.cos (quraAngle (by omega : 1 ≤ d)) /
      Real.sin ((m : ℝ) * quraAngle (by omega : 1 ≤ d))
    quraModifiedAmplifier d U α ((m : ℝ) * quraAngle (by omega : 1 ≤ d)) *
        (quraAmplifier d U) ^ (m - 1) * quraI2E d U * quraKet0Mat d (quraLambda0 d) =
      quraKet0Mat d (quraPsi0 d U) := by
  have hU : (U : Matrix (Fin d) (Fin d) ℂ) ∈ Matrix.unitaryGroup (Fin d) ℂ := U.property
  dsimp
  let θ : ℝ := quraAngle (by omega : 1 ≤ d)
  let m : ℕ := quraFloorRounds (by omega : 1 ≤ d)
  let α : ℝ := Real.cos θ / Real.sin ((m : ℝ) * θ)
  have hα0 : 0 ≤ α := by
    dsimp [α, θ, m]
    exact quraFloorAlpha_nonneg hd
  have hα1 : α < 1 := by
    dsimp [α, θ, m]
    exact quraFloorAlpha_lt_one hd
  have hθ : 0 < Real.sin ((m : ℝ) * θ) := by
    dsimp [θ, m]
    exact quraFloorRounds_sin_pos hd
  calc
    quraModifiedAmplifier d U α ((m : ℝ) * θ) * (quraAmplifier d U) ^ (m - 1) *
          quraI2E d U * quraKet0Mat d (quraLambda0 d)
        = quraModifiedAmplifier d U α ((m : ℝ) * θ) *
            ((quraAmplifier d U) ^ (m - 1) * (quraI2E d U * quraKet0Mat d (quraLambda0 d))) := by
          simp only [Matrix.mul_assoc]
    _ = quraModifiedAmplifier d U α ((m : ℝ) * θ) *
            ((quraAmplifier d U) ^ (m - 1) * quraEncodedState d U) := by
          rw [quraI2E_mul_ket0_lambda0 d hd U]
    _ = quraModifiedAmplifier d U α ((m : ℝ) * θ) *
            quraSpanState (by omega : 1 ≤ d) m U := by
          rw [quraAmplifier_pow_mul_encoded d hd U hU (m - 1)]
          have hm_pos : 1 ≤ m := by
            dsimp [m]
            have h3 : 3 ≤ quraFloorRounds (by omega : 1 ≤ d) := quraFloorRounds_ge_three hd
            omega
          rw [show (m - 1) + 1 = m by omega]
    _ = quraModifiedAmplifier d U α ((m : ℝ) * θ) *
            ((Real.sin ((m : ℝ) * θ) : ℂ) • quraKet0Mat d (quraPsi0 d U) +
              (Real.cos ((m : ℝ) * θ) : ℂ) • quraKet0Mat d (quraPsiPerp d U)) := by
          simp only [quraSpanState]
          rw [show (((m : ℕ) : ℂ) * quraTheta (by omega : 1 ≤ d)) = (((m : ℝ) * θ : ℝ) : ℂ) by
            simp [θ, quraTheta, quraAngle, Complex.ofReal_natCast, Complex.ofReal_mul]]
          rw [← Complex.ofReal_sin, ← Complex.ofReal_cos]
    _ = Complex.sin ((Real.arcsin (α * Real.sin ((m : ℝ) * θ)) : ℂ) +
            quraTheta (by omega : 1 ≤ d)) •
          quraKet0Mat d (quraPsi0 d U) +
        Complex.cos ((Real.arcsin (α * Real.sin ((m : ℝ) * θ)) : ℂ) +
            quraTheta (by omega : 1 ≤ d)) •
          quraKet0Mat d (quraPsiPerp d U) := by
          rw [quraModifiedAmplifier_mul_ket0_span d hd U hU α ((m : ℝ) * θ) hα0 hα1 hθ]
    _ = quraKet0Mat d (quraPsi0 d U) := by
          have hp : Real.arcsin (α * Real.sin ((m : ℝ) * θ)) + θ = Real.pi / 2 := by
            have hsin_ne : Real.sin ((m : ℝ) * θ) ≠ 0 := (quraFloorRounds_sin_pos hd).ne'
            have hαsin : α * Real.sin ((m : ℝ) * θ) = Real.cos θ := by
              dsimp [α]
              field_simp [hsin_ne]
            rw [hαsin]
            have harc : Real.arcsin (Real.cos θ) = Real.pi / 2 - θ := by
              rw [← Real.sin_pi_div_two_sub]
              exact Real.arcsin_sin
                (by linarith [quraAngle_pos_of_two_le hd, quraAngle_le_pi_div_six hd])
                (by linarith [quraAngle_pos_of_two_le hd])
            linarith
          have hcq : (Real.arcsin (α * Real.sin ((m : ℝ) * θ)) : ℂ) +
              quraTheta (by omega : 1 ≤ d) = ((Real.pi / 2 : ℝ) : ℂ) := by
            change (Real.arcsin (α * Real.sin ((m : ℝ) * θ)) : ℂ) +
                (quraAngle (by omega : 1 ≤ d) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ)
            rw [← Complex.ofReal_add]
            exact congrArg (fun x : ℝ => (x : ℂ)) hp
          rw [hcq]
          rw [← Complex.ofReal_sin, ← Complex.ofReal_cos]
          simp [Real.sin_pi_div_two, Real.cos_pi_div_two]

end

end QuantumAlg.UnitaryReversal
