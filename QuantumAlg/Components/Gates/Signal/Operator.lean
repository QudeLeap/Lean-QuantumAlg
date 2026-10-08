/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Util.Complex

/-!
# Certified single-qubit signal operators

These mathematical operators grant no native instruction or oracle access.
-/

namespace QuantumAlg

noncomputable section

/-- Certified Chebyshev O-convention signal operator on its physical domain. -/
public def qspSignalOOp (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (!![(x : ℂ), -(Real.sqrt (1 - x ^ 2) : ℂ);
      (Real.sqrt (1 - x ^ 2) : ℂ), (x : ℂ)] :
        HilbertOperator (Qubits 1)) (by
      have hs := sq_sqrt_one_sub_sq hx
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j
      · simp [Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
        linear_combination hs
      · simp [Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
        ring
      · simp [Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
        ring
      · simp [Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
        linear_combination hs)

/-- Certified Chebyshev Wx-convention signal operator on its physical domain. -/
public def qspSignalWOp (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (!![(x : ℂ), Complex.I * (Real.sqrt (1 - x ^ 2) : ℂ);
      Complex.I * (Real.sqrt (1 - x ^ 2) : ℂ), (x : ℂ)] :
        HilbertOperator (Qubits 1)) (by
      have hs := sq_sqrt_one_sub_sq hx
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j
      · simp [Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
        ring_nf
        rw [Complex.I_sq]
        linear_combination hs
      · simp [Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
        ring
      · simp [Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
        ring
      · simp [Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
        ring_nf
        rw [Complex.I_sq]
        linear_combination hs)


end

end QuantumAlg
