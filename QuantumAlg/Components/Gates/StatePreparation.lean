/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.State.Pure
import all QuantumAlg.Components.Kets

/-!
# Mathematical unitary preparation targets

A normalized vector extends to an orthonormal basis, defining an exact unitary
that maps zero to that vector. This is a mathematical operator construction;
it supplies no native gate, oracle access or execution-resource claim.
-/

namespace QuantumAlg.Gate

noncomputable section

/-- The requested target gives an orthonormal family on the singleton zero
basis index. -/
theorem finiteCyclicRangePreparation_singleton_orthonormal
    {n : Nat} (target : NormalizedVector (Qubits n)) :
    Orthonormal ℂ
      (({0} : Set (Fin (2 ^ n))).domRestrict
        (fun _ : Fin (2 ^ n) =>
          (target : HilbertVector (Qubits n)))) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hij : i = j := by
    apply Subtype.ext
    simpa using i.property.trans j.property.symm
  subst j
  rw [if_pos rfl]
  exact inner_self_eq_one_of_norm_eq_one target.norm_eq_one

/-- Every normalized target extends from the zero index to an orthonormal
basis. -/
theorem exists_finiteCyclicRangePreparationBasis
    {n : Nat} (target : NormalizedVector (Qubits n)) :
    ∃ b : OrthonormalBasis (Fin (2 ^ n)) ℂ
        (HilbertVector (Qubits n)),
      ∀ i ∈ ({0} : Set (Fin (2 ^ n))),
        b i = (target : HilbertVector (Qubits n)) :=
  Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (s := ({0} : Set (Fin (2 ^ n))))
    (v := fun _ : Fin (2 ^ n) =>
      (target : HilbertVector (Qubits n)))
    (by simp) (finiteCyclicRangePreparation_singleton_orthonormal target)

/-- An orthonormal basis whose zero column is the requested target state. -/
noncomputable def finiteCyclicRangePreparationBasis
    {n : Nat} (target : NormalizedVector (Qubits n)) :
    OrthonormalBasis (Fin (2 ^ n)) ℂ (HilbertVector (Qubits n)) :=
  Classical.choose (exists_finiteCyclicRangePreparationBasis target)

/-- The selected basis has the requested target as its zero column. -/
theorem finiteCyclicRangePreparationBasis_zero
    {n : Nat} (target : NormalizedVector (Qubits n)) :
    finiteCyclicRangePreparationBasis target 0 =
      (target : HilbertVector (Qubits n)) := by
  exact (Classical.choose_spec
    (exists_finiteCyclicRangePreparationBasis target)) 0 (by simp)

/-- Basis-change operator whose zero column is the requested target state. -/
def finiteCyclicRangePreparationOp {n : Nat}
    (target : NormalizedVector (Qubits n)) : UnitaryOperator (Qubits n) :=
  UnitaryOperator.ofMatrix
    ((EuclideanSpace.basisFun (Fin (2 ^ n)) ℂ).toBasis.toMatrix
      (finiteCyclicRangePreparationBasis target))
    ((EuclideanSpace.basisFun (Fin (2 ^ n)) ℂ).toMatrix_orthonormalBasis_mem_unitary
        (finiteCyclicRangePreparationBasis target))

/-- The component basis change prepares its requested target from zero. -/
@[simp] theorem finiteCyclicRangePreparationOp_apply_zero {n : Nat}
    (target : NormalizedVector (Qubits n)) :
    (finiteCyclicRangePreparationOp target).apply
        (NormalizedVector.ket (R := Qubits n) 0) = target := by
  apply NormalizedVector.ext
  intro i
  change
    HilbertOperator.applyVec
        (finiteCyclicRangePreparationOp target : HilbertOperator (Qubits n))
        (NormalizedVector.ket (R := Qubits n) 0) i = _
  rw [HilbertOperator.applyVec_ket]
  change
    (EuclideanSpace.basisFun (Fin (2 ^ n)) ℂ).toBasis.toMatrix
        (finiteCyclicRangePreparationBasis target) i 0 = _
  rw [Module.Basis.toMatrix_apply]
  change
    (EuclideanSpace.basisFun (Fin (2 ^ n)) ℂ).toBasis.repr
        (finiteCyclicRangePreparationBasis target 0) i = _
  rw [finiteCyclicRangePreparationBasis_zero,
    EuclideanSpace.basisFun_toBasis, PiLp.basisFun_repr]

end

end QuantumAlg.Gate
