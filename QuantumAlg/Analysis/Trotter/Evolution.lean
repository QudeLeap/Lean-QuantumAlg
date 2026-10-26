/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Base.Gate.OperatorNorm
public import QuantumAlg.Components.Oracle.TimeEvolution
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Time-evolution identities for product-formula analysis

Time-independent evolution is the matrix exponential `exp (-i t H)`
[Lin22, trotter.tex:3]. Its time derivatives, unitary norm identities and
repeated-time identity support the product-formula estimates.
-/

@[expose] public section

namespace QuantumAlg

open HilbertOperator

noncomputable section

lemma hasDerivAt_timeEvolutionOp {R : Register} (H : HilbertOperator R) (t : ℝ) :
    HasDerivAt (fun u : ℝ => timeEvolutionOp H u)
      (timeEvolutionOp H t * ((-Complex.I) • H)) t := by
  let A : HilbertOperator R := (-Complex.I) • H
  have hderiv :
      HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A))
        (NormedSpace.exp (t • A) * A) t := by
    open scoped Matrix.Norms.L2Operator in
    exact hasDerivAt_exp_smul_const A t
  convert hderiv using 1
  · funext u
    have harg : (-(Complex.I * (u : ℂ))) • H = u • A := by
      ext i j
      simp [A]
      ring_nf
    rw [timeEvolutionOp, harg]
  · have harg : (-(Complex.I * (t : ℂ))) • H = t • A := by
      ext i j
      simp [A]
      ring_nf
    rw [timeEvolutionOp, harg]

lemma hasDerivAt_timeEvolutionOp' {R : Register} (H : HilbertOperator R) (t : ℝ) :
    HasDerivAt (fun u : ℝ => timeEvolutionOp H u)
      (((-Complex.I) • H) * timeEvolutionOp H t) t := by
  let A : HilbertOperator R := (-Complex.I) • H
  have hderiv :
      HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A))
        (A * NormedSpace.exp (t • A)) t := by
    open scoped Matrix.Norms.L2Operator in
    exact hasDerivAt_exp_smul_const' A t
  convert hderiv using 1
  · funext u
    have harg : (-(Complex.I * (u : ℂ))) • H = u • A := by
      ext i j
      simp [A]
      ring_nf
    rw [timeEvolutionOp, harg]
  · have harg : (-(Complex.I * (t : ℂ))) • H = t • A := by
      ext i j
      simp [A]
      ring_nf
    rw [timeEvolutionOp, harg]

lemma opNorm_timeEvolutionOp {R : Register} [Nonempty R.Index]
    {H : HilbertOperator R} (hH : H.IsHermitian) (t : ℝ) :
    opNorm (timeEvolutionOp H t) = 1 :=
  opNorm_of_mem_unitaryGroup (timeEvolutionOp_mem_unitaryGroup hH t)

lemma opNorm_timeEvolutionOp_mul {R : Register}
    {H : HilbertOperator R} (hH : H.IsHermitian) (t : ℝ)
    (A : HilbertOperator R) :
    opNorm (timeEvolutionOp H t * A) = opNorm A :=
  opNorm_unitaryGroup_mul A (timeEvolutionOp_mem_unitaryGroup hH t)

lemma opNorm_mul_timeEvolutionOp {R : Register}
    {H : HilbertOperator R} (hH : H.IsHermitian) (t : ℝ)
    (A : HilbertOperator R) :
    opNorm (A * timeEvolutionOp H t) = opNorm A :=
  opNorm_mul_unitaryGroup A (timeEvolutionOp_mem_unitaryGroup hH t)

/-- Repeating exact evolution for `t / r` exactly recovers evolution for `t`.
This is an algebraic matrix-exponential identity and does not require
Hermitianity. -/
lemma timeEvolutionOp_pow_div {R : Register} (H : HilbertOperator R) {r : ℕ}
    (hr : r ≠ 0) (t : ℝ) :
    (timeEvolutionOp H (t / (r : ℝ))) ^ r = timeEvolutionOp H t := by
  rw [timeEvolutionOp, timeEvolutionOp]
  rw [← Matrix.exp_nsmul r
    ((-(Complex.I * ((t / (r : ℝ) : ℝ) : ℂ))) • H)]
  congr 1
  ext i j
  simp [nsmul_eq_mul]
  field_simp [Nat.cast_ne_zero.mpr hr]

end

end QuantumAlg
