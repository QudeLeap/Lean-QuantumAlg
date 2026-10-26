/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Util.CliffordT.Matrix
public import QuantumAlg.Analysis.FTQC.CliffordT.Word
import all QuantumAlg.Analysis.FTQC.CliffordT.Word
import all QuantumAlg.Components.Gates
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Gates.Rotation.Operator
import all QuantumAlg.Components.Kets
import all QuantumAlg.Core.Base.Gate.Unitary

/-!
# Exact arithmetic for Clifford+T words

The first letter acts first, in the same order as `evalOp`. The complex
interpretation of exact matrix evaluation equals the existing unitary semantics,
with no global-phase quotient. The coefficient representation is the ring
`Z[1/sqrt(2), i]` used in Ross and Selinger, *Optimal ancilla-free Clifford+T
approximation of z-rotations*, Some algebra, and in Kliuchnikov, Maslov and
Mosca, *Fast and efficient exact synthesis of single qubit unitaries generated
by Clifford and T gates*, the main characterization theorem.
-/

section

namespace QuantumAlg.CliffordT

open Gate NormalizedVector

lemma toComplexMat_hMat :
    toComplexMat hMat = (HOp : HilbertOperator (Qubits 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toComplexMat, hMat, HOp, DOmega.toComplex_invSqrtTwo, invSqrt2]

lemma toComplexMat_sMat :
    toComplexMat sMat = (SOp : HilbertOperator (Qubits 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toComplexMat, sMat, SOp, DOmega.toComplex_imaginary]

private lemma toComplex_omega_eq_exp :
    DOmega.toComplex DOmega.ω = Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) := by
  rw [DOmega.toComplex_omega, Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four, Real.sqrt_div_self, Complex.ofReal_inv]
  ring

lemma toComplexMat_tMat :
    toComplexMat tMat = (TOp : HilbertOperator (Qubits 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toComplexMat, tMat, TOp, toComplex_omega_eq_exp]

namespace Letter

/-- Exact matrix of a Clifford+T letter. -/
@[expose] public def ringMatrix : Letter → Mat2
  | .h => hMat
  | .s => sMat
  | .t => tMat

lemma toComplexMat_ringMatrix (a : Letter) :
    toComplexMat a.ringMatrix = (a.op : HilbertOperator (Qubits 1)) := by
  cases a
  · exact toComplexMat_hMat
  · exact toComplexMat_sMat
  · exact toComplexMat_tMat

end Letter

/-- Exact matrix evaluation of a word, with the first letter acting first. -/
@[expose] public def evalRing : List Letter → Mat2
  | [] => 1
  | a :: w => evalRing w * a.ringMatrix

@[simp] lemma evalRing_nil : evalRing [] = 1 := rfl

@[simp] lemma evalRing_cons (a : Letter) (w : List Letter) :
    evalRing (a :: w) = evalRing w * a.ringMatrix := rfl

/-- Exact evaluation agrees with the existing unitary semantics, including phase. -/
public lemma evalOp_eq_toComplexMat (w : List Letter) :
    (evalOp w : HilbertOperator (Qubits 1)) = toComplexMat (evalRing w) := by
  induction w with
  | nil => simp [evalRing]
  | cons a w ih =>
      simp only [evalOp_cons, evalRing_cons, map_mul, Letter.toComplexMat_ringMatrix]
      change (evalOp w : HilbertOperator (Qubits 1)) * (a.op : HilbertOperator (Qubits 1)) = _
      rw [ih]

lemma evalRing_append (u v : List Letter) : evalRing (u ++ v) = evalRing v * evalRing u := by
  induction u with
  | nil => simp
  | cons a u ih => simp [ih, mul_assoc]

lemma evalRing_two_t : evalRing [.t, .t] = sMat := by decide +kernel

lemma evalRing_eight_t : evalRing (List.replicate 8 .t) = 1 := by decide +kernel

end QuantumAlg.CliffordT

end
