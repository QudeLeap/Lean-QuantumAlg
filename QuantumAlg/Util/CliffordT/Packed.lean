/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Util.CliffordT.Matrix
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Packed exact two-by-two matrix arithmetic

Four explicit entries avoid repeatedly applying nested matrix-valued functions
when the kernel evaluates long products. Each specialized left multiplication
agrees with the existing exact matrix representation.
-/

@[expose] public section

namespace QuantumAlg.CliffordT

/-- Four exact entries in row-major order. -/
structure PackedMat2 where
  /-- Entry in row zero, column zero. -/
  a : DOmega
  /-- Entry in row zero, column one. -/
  b : DOmega
  /-- Entry in row one, column zero. -/
  c : DOmega
  /-- Entry in row one, column one. -/
  d : DOmega
  deriving DecidableEq

namespace PackedMat2

/-- Interpret the four entries as the ordinary exact matrix. -/
def toMatrix (m : PackedMat2) : Mat2 :=
  fun i j => if i = 0 then if j = 0 then m.a else m.b else if j = 0 then m.c else m.d

/-- Packed identity matrix. -/
def identity : PackedMat2 := ⟨1, 0, 0, 1⟩

/-- Exact left multiplication by the Hadamard matrix. -/
def stepH (m : PackedMat2) : PackedMat2 :=
  ⟨DOmega.invSqrtTwo * (m.a + m.c), DOmega.invSqrtTwo * (m.b + m.d),
    DOmega.invSqrtTwo * (m.a - m.c), DOmega.invSqrtTwo * (m.b - m.d)⟩

/-- Exact left multiplication by the phase matrix. -/
def stepS (m : PackedMat2) : PackedMat2 :=
  ⟨m.a, m.b, DOmega.imaginary * m.c, DOmega.imaginary * m.d⟩

/-- Exact left multiplication by the eighth-root phase matrix. -/
def stepT (m : PackedMat2) : PackedMat2 := ⟨m.a, m.b, DOmega.ω * m.c, DOmega.ω * m.d⟩

lemma toMatrix_identity : toMatrix identity = 1 := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, identity]

lemma toMatrix_stepH (m : PackedMat2) : toMatrix (stepH m) = hMat * toMatrix m := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, stepH, hMat, Matrix.mul_apply, Fin.sum_univ_two, mul_add, sub_eq_add_neg]

lemma toMatrix_stepS (m : PackedMat2) : toMatrix (stepS m) = sMat * toMatrix m := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, stepS, sMat, Matrix.mul_apply, Fin.sum_univ_two]

lemma toMatrix_stepT (m : PackedMat2) : toMatrix (stepT m) = tMat * toMatrix m := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, stepT, tMat, Matrix.mul_apply, Fin.sum_univ_two]

end PackedMat2

end QuantumAlg.CliffordT
