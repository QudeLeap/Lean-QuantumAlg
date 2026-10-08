/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Unitary
public import QuantumAlg.Components.Kets
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Components.Kets

/-!
# Mathematical XOR query operator

The fixed basis involution sends each target bit to its XOR with the supplied
Boolean function value [dW19, qcnotes.tex:1149-1173]. This module states the
exact operator action independently of any executable access declaration.
-/

namespace QuantumAlg

noncomputable section

variable {n : Nat}

/-- The basis involution underlying the XOR oracle:
`(x, b) ↦ (x, b ⊕ f x)`, with the bit flip written as `Fin.rev`. -/
def xorPerm (f : Fin (2 ^ n) -> Bool) :
    Equiv.Perm (Fin (2 ^ n) × Fin (2 ^ 1)) where
  toFun p := (p.1, if f p.1 then p.2.rev else p.2)
  invFun p := (p.1, if f p.1 then p.2.rev else p.2)
  left_inv p := by by_cases h : f p.1 <;> simp [h]
  right_inv p := by by_cases h : f p.1 <;> simp [h]

@[simp]
theorem xorPerm_apply (f : Fin (2 ^ n) -> Bool) (p : Fin (2 ^ n) × Fin (2 ^ 1)) :
    xorPerm f p = (p.1, if f p.1 then p.2.rev else p.2) :=
  rfl

/-- The XOR oracle is an involution. -/
@[simp]
theorem xorPerm_symm (f : Fin (2 ^ n) -> Bool) : (xorPerm f).symm = xorPerm f :=
  rfl

/-- The metadata-free XOR (bit-flip) oracle of `f`. -/
public def xorOracleOp (f : Fin (2 ^ n) -> Bool) : UnitaryOperator (Qubits (n + 1)) :=
  UnitaryOperator.ofPerm (prodEquiv.permCongr (xorPerm f))

theorem xorOracleOp_apply (f : Fin (2 ^ n) -> Bool)
    (ψ : HilbertVector (Qubits (n + 1))) (i : Fin (2 ^ (n + 1))) :
    (xorOracleOp f).applyVec ψ i =
      ψ (prodEquiv (xorPerm f (prodEquiv.symm i))) := by
  rw [xorOracleOp, UnitaryOperator.ofPerm_applyVec, Equiv.permCongr_apply]

/-- Action on normalized basis kets: `U_f |x⟩|b⟩ = |x⟩|b ⊕ f(x)⟩`. -/
@[simp]
theorem xorOracleOp_apply_ket (f : Fin (2 ^ n) -> Bool) (x : Fin (2 ^ n))
    (b : Fin (2 ^ 1)) :
    (xorOracleOp f).apply
        (NormalizedVector.ket (R := Qubits (n + 1)) (prodEquiv (x, b))) =
      NormalizedVector.ket (R := Qubits (n + 1))
        (prodEquiv (x, if f x then b.rev else b)) := by
  rw [xorOracleOp, UnitaryOperator.ofPerm_apply_ket]
  congr 1
  change prodEquiv ((xorPerm f).symm (prodEquiv.symm (prodEquiv (x, b)))) = _
  rw [Equiv.symm_apply_apply, xorPerm_symm, xorPerm_apply]

/-- On a `|+⟩` target the metadata-free XOR oracle acts trivially. -/
theorem xorOracleOp_apply_tensor_ketPlus (f : Fin (2 ^ n) -> Bool)
    (x : Fin (2 ^ n)) :
    (xorOracleOp f).apply
        ((NormalizedVector.ket x).tensor NormalizedVector.ketPlus) =
      (NormalizedVector.ket x).tensor NormalizedVector.ketPlus := by
  apply NormalizedVector.ext
  intro i
  change (xorOracleOp f).applyVec
      (((NormalizedVector.ket x).tensor NormalizedVector.ketPlus :
        NormalizedVector (Qubits (n + 1))) : HilbertVector (Qubits (n + 1))) i =
    (((NormalizedVector.ket x).tensor NormalizedVector.ketPlus :
      NormalizedVector (Qubits (n + 1))) : HilbertVector (Qubits (n + 1))) i
  rcases (prodEquiv (m := n) (n := 1)).surjective i with ⟨⟨y, b⟩, rfl⟩
  rw [xorOracleOp_apply, NormalizedVector.tensor_apply_prod,
    NormalizedVector.tensor_apply_prod]
  simp only [Equiv.symm_apply_apply, xorPerm_apply]
  by_cases hy : y = x
  · subst y
    by_cases h : f x <;> fin_cases b <;>
      simp [h, NormalizedVector.ketPlus_apply]
  · by_cases h : f y <;> fin_cases b <;>
      simp [h, hy, NormalizedVector.ket_apply]


end

end QuantumAlg
