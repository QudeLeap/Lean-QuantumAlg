/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Source.Projected
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Source.Projected
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Source
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Invariant
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Operator
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Complement
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Pair
import all QuantumAlg.Primitives.QSP.SingleQubit.PhaseSynthesis
import all QuantumAlg.Components.Oracle.SignalProcessing
import all QuantumAlg.Components.Oracle.Reflection

/-!
# Projected source phase certificates

Conversion of a reflection-QSP certificate to the source's projected phases,
including the conjugate branch [GSLW19, BlockHam.tex:514-528,768-887].
-/

section
namespace QuantumAlg.QSP.MultiQubit.QSVT
open scoped Matrix.Norms.L2Operator ComplexOrder

/-- Convert the reflection-QSP phase list into the projected-QSVT phase list
used by the source's singular-value transformation sequence.  For a source
certificate `(φ'_0, ..., φ'_d)`, the projected list is
`φ_1 := φ'_0 + φ'_d + (d-1)π/2` and
`φ_j := φ'_{j-1} - π/2` for `j ≥ 2` [GSLW19, BlockHam.tex:520-528]. -/
noncomputable def projectedPhasesFromQSPCertificate (φ₀ : ℝ) (φs : List ℝ) :
    List ℝ :=
  match φs.reverse with
  | [] => []
  | last :: reversedInit =>
      (φ₀ + last + (((φs.length - 1 : ℕ) : ℝ) * (Real.pi / 2))) ::
        (reversedInit.reverse.map fun φ => φ - Real.pi / 2)

theorem projectedPhasesFromQSPCertificate_length (φ₀ : ℝ) (φs : List ℝ) :
    (projectedPhasesFromQSPCertificate φ₀ φs).length = φs.length := by
  unfold projectedPhasesFromQSPCertificate
  cases hrev : φs.reverse with
  | nil =>
      have hlen := congrArg List.length hrev
      simp [List.length_reverse] at hlen
      simp [hlen]
  | cons last reversedInit =>
      have hlen := congrArg List.length hrev
      simp [List.length_reverse] at hlen ⊢
      omega

/-- The source phase conversion of [GSLW19, BlockHam.tex:523-528], restricted
to the `(0,0)` entry needed by the singular-value transformation proof: the
projected-QSVT `R` product is the raw `R` product with the terminal scalar phase
absorbed into its first phase. -/
theorem singularSignalRProduct_projectedPhases_zero_zero_eq_rawProduct
    (φ₀ : ℝ) (init : List ℝ) (last x : ℝ) :
    singularSignalRProduct (projectedPhasesFromQSPCertificate φ₀ (init ++ [last])) x 0 0 =
      Complex.exp (((last + init.length * (Real.pi / 2) + Real.pi / 4 : ℝ) : ℂ) *
          Complex.I) * singularSignalRRawProduct φ₀ init x 0 0 := by
  rw [show projectedPhasesFromQSPCertificate φ₀ (init ++ [last]) =
      (φ₀ + last + (init.length : ℝ) * (Real.pi / 2)) ::
        init.map (fun φ => φ - Real.pi / 2) by
        induction init with
        | nil => simp [projectedPhasesFromQSPCertificate]
        | cons φ init ih =>
            simp [projectedPhasesFromQSPCertificate, List.reverse_append]]
  rw [singularSignalRProduct_first_phase_zero_zero
    (φ₀ + last + (init.length : ℝ) * (Real.pi / 2)) (φ₀ - Real.pi / 4)
    (init.map (fun φ => φ - Real.pi / 2)) x]
  have harg :
      ((((φ₀ + last + (init.length : ℝ) * (Real.pi / 2) : ℝ) : ℂ) -
          ((φ₀ - Real.pi / 4 : ℝ) : ℂ)) * Complex.I) =
        (((last + init.length * (Real.pi / 2) + Real.pi / 4 : ℝ) : ℂ) *
          Complex.I) := by
    have hreal :
        (((φ₀ + last + (init.length : ℝ) * (Real.pi / 2) : ℝ) : ℂ) -
          ((φ₀ - Real.pi / 4 : ℝ) : ℂ)) =
        ((last + init.length * (Real.pi / 2) + Real.pi / 4 : ℝ) : ℂ) := by
      norm_num
      ring
    exact congrArg (fun z : ℂ => z * Complex.I) hreal
  rw [harg]
  simp [singularSignalRRawProduct]

/-- The projected-QSVT phase conversion preserves the `(0,0)` scalar entry of
the source `W`-convention QSP certificate [GSLW19, BlockHam.tex:514-528]. -/
theorem singularSignalRProduct_projectedPhases_zero_zero_eq_qspW
    (φ₀ : ℝ) (init : List ℝ) (last x : ℝ) :
    singularSignalRProduct (projectedPhasesFromQSPCertificate φ₀ (init ++ [last])) x 0 0 =
      qspW φ₀ (init ++ [last]) x 0 0 := by
  rw [singularSignalRProduct_projectedPhases_zero_zero_eq_rawProduct]
  rw [qspW_zero_zero_eq_rawProduct]

/-- Negating the source projected-QSVT phase list implements the coefficient
conjugate scalar polynomial on the local `R`-signal block.  This is the scalar
half of the real-polynomial averaging step in `cor:matchingParity`
[GSLW19, BlockHam.tex:851-887]. -/
theorem singularSignalRProduct_negProjectedPhases_zero_zero_eq_conjP
    {d : Nat} {P Q : Polynomial Complex}
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last x : ℝ)
    (hφs : certificate.φs = init ++ [last])
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    singularSignalRProduct
        (negPhases
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)) x 0 0 =
      (conjP P).eval (x : Complex) := by
  rw [singularSignalRProduct_negPhases_zero_zero]
  rw [hφs]
  rw [singularSignalRProduct_projectedPhases_zero_zero_eq_qspW]
  have hq : qspW certificate.φ₀ (init ++ [last]) x 0 0 = P.eval (x : Complex) := by
    simpa [hφs] using certificate.qspW_zero_zero hx
  rw [hq]
  rw [conjP_eval_ofReal]
  rfl

-- Mathlib linter exception: this list-sum proof uses the existing
-- projected-phase definition shape; the `simp only` variant was brittle.
set_option linter.flexible false in
/-- Phase conversion for the nonempty reflection-QSP phase list.  The source's
projected-QSVT phases have the same scalar product as the `(0,0)` entry of the
corresponding `W`-convention QSP sequence at `x=1` [GSLW19,
BlockHam.tex:520-528,738-849]. -/
theorem phaseProduct_projectedPhases_append_singleton (φ₀ : ℝ)
    (init : List ℝ) (last : ℝ) :
    phaseProduct (projectedPhasesFromQSPCertificate φ₀ (init ++ [last])) =
      Complex.exp (φ₀ * Complex.I) * phaseProduct (init ++ [last]) := by
  have hsum :
      (projectedPhasesFromQSPCertificate φ₀ (init ++ [last])).sum =
        φ₀ + (init ++ [last]).sum := by
    induction init with
    | nil =>
        simp [projectedPhasesFromQSPCertificate]
    | cons φ init ih =>
        simp [projectedPhasesFromQSPCertificate, List.reverse_append]
        rw [list_sum_map_sub_const]
        ring_nf
  rw [phaseProduct_eq_exp_sum, phaseProduct_eq_exp_sum, hsum]
  rw [← Complex.exp_add]
  congr 1
  norm_num
  ring

/-- Nonempty phase-list specialization of the phase conversion: after
projecting a reflection-QSP phase certificate into the source projected-QSVT
phase list, the scalar phase product on a unit singular block is exactly the
certificate's target value at `x=1` [GSLW19, BlockHam.tex:520-528,768-849]. -/
theorem phaseProduct_projectedPhases_eq_certificate_eval_one {d : Nat}
    {P Q : Polynomial Complex}
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) :
    phaseProduct (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) =
      P.eval (1 : Complex) := by
  rw [hφs, phaseProduct_projectedPhases_append_singleton]
  rw [phaseProduct]
  rw [← qspW_one_zero_zero_eq_phaseProduct]
  simpa [hφs] using certificate.qspW_zero_zero (x := 1) (by norm_num)

theorem phaseProduct_negProjectedPhases_eq_conjP_eval_one {d : Nat}
    {P Q : Polynomial Complex}
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) :
    phaseProduct
        (negPhases
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)) =
      (conjP P).eval (1 : Complex) := by
  rw [phaseProduct_negPhases]
  rw [phaseProduct_projectedPhases_eq_certificate_eval_one certificate init last hφs]
  simpa using (conjP_eval_ofReal P 1).symm


end QuantumAlg.QSP.MultiQubit.QSVT
end
