/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Three-factor matrix tensor

Entrywise form of a right-associated three-factor tensor product.
-/

@[expose] public section

namespace QuantumAlg.MatrixWeyl

noncomputable section


variable {d : ℕ}

/-- Tensor of three `d × d` matrices on the three-qudit register
`(Fin d) × ((Fin d) × (Fin d))`. -/
def qudTensor3 (A B C : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × (Fin d × Fin d)) (Fin d × (Fin d × Fin d)) ℂ :=
  Matrix.of fun a b => A a.1 b.1 * B a.2.1 b.2.1 * C a.2.2 b.2.2

@[simp]
lemma qudTensor3_apply (A B C : Matrix (Fin d) (Fin d) ℂ)
    (a b : Fin d × (Fin d × Fin d)) :
    qudTensor3 A B C a b =
      A a.1 b.1 * B a.2.1 b.2.1 * C a.2.2 b.2.2 := by
  rfl

end

end QuantumAlg.MatrixWeyl
