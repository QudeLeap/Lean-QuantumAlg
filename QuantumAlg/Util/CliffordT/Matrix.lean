/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Util.CliffordT.Embedding
public import Mathlib.Data.Matrix.Mul

/-!
# Exact two-by-two matrices over dyadic cyclotomic numbers

The Hadamard, phase, and eighth-root phase matrices are computable values.
Their identities are checked directly by the Lean kernel. Entrywise complex
interpretation is a faithful ring homomorphism.
-/

@[expose] public section

namespace QuantumAlg.CliffordT

/-- Exact single-qubit-sized matrices, independent of the quantum framework. -/
abbrev Mat2 := Matrix (Fin 2) (Fin 2) DOmega

/-- Exact Hadamard matrix. -/
def hMat : Mat2 :=
  fun i j => if i = 1 ∧ j = 1 then -DOmega.invSqrtTwo else DOmega.invSqrtTwo

/-- Exact quarter-turn phase matrix. -/
def sMat : Mat2 := fun i j => if i = j then if i = 0 then 1 else DOmega.imaginary else 0

/-- Exact eighth-turn phase matrix. -/
def tMat : Mat2 := fun i j => if i = j then if i = 0 then 1 else DOmega.ω else 0

/-- Entrywise faithful complex interpretation. -/
noncomputable def toComplexMat : Mat2 →+* Matrix (Fin 2) (Fin 2) ℂ where
  toFun A := A.map DOmega.toComplex
  map_zero' := by simp
  map_one' := by simp
  map_add' A B := by ext i j; exact map_add DOmega.toComplex (A i j) (B i j)
  map_mul' _ _ := Matrix.map_mul

lemma toComplexMat_injective : Function.Injective toComplexMat := by
  intro A B h
  funext i j
  exact DOmega.toComplex_injective (congrFun (congrFun h i) j)

lemma hMat_sq : hMat * hMat = 1 := by decide +kernel

lemma tMat_sq : tMat * tMat = sMat := by decide +kernel

lemma sMat_pow_four : sMat ^ 4 = 1 := by decide +kernel

lemma tMat_pow_eight : tMat ^ 8 = 1 := by decide +kernel

end QuantumAlg.CliffordT
