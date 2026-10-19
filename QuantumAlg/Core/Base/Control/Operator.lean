/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary
public import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Matrix.Block

/-!
# Metadata-free controlled unitary operators

The constructions in this module depend only on certified mathematical operators.
Physical placement and resource annotations are added separately in `Control.Gate`.
-/

section

namespace QuantumAlg.UnitaryOperator

noncomputable section

variable {R S : Register}

/-- Reindexing both axes of a square matrix by one equivalence preserves
unitarity. -/
private lemma reindex_matrix_mem_unitaryGroup {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (M : Matrix ι ι ℂ)
    (hM : M ∈ Matrix.unitaryGroup ι ℂ) :
    Matrix.reindex e e M ∈ Matrix.unitaryGroup κ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hM ⊢
  rw [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    hM, Matrix.submatrix_one_equiv]

private lemma reindex_mem_unitaryGroup (e : R.Index ≃ S.Index)
    (U : UnitaryOperator R) :
    Matrix.reindex e e (U : HilbertOperator R) ∈
      Matrix.unitaryGroup S.Index ℂ := by
  exact reindex_matrix_mem_unitaryGroup e U U.property

/-- Transport a certified unitary operator along a register-index equivalence. -/
public def reindex (e : R.Index ≃ S.Index) (U : UnitaryOperator R) : UnitaryOperator S :=
  ofMatrix (Matrix.reindex e e (U : HilbertOperator R))
    (reindex_mem_unitaryGroup e U)

@[simp]
lemma coe_reindex (e : R.Index ≃ S.Index) (U : UnitaryOperator R) :
    ((reindex e U : UnitaryOperator S) : HilbertOperator S) =
      Matrix.reindex e e (U : HilbertOperator R) := rfl

private def controlledBlock {control : Register} (activationValue : control.Index)
    (U : UnitaryOperator R) (controlValue : control.Index) : HilbertOperator R :=
  if controlValue = activationValue then (U : HilbertOperator R) else 1

private def controlledMatrix (control : Register) (activationValue : control.Index)
    (U : UnitaryOperator R) : HilbertOperator (Register.prod control R) :=
  Matrix.reindex (Equiv.prodComm R.Index control.Index)
    (Equiv.prodComm R.Index control.Index)
    (Matrix.blockDiagonal (controlledBlock activationValue U))

private lemma controlledMatrix_apply (control : Register) (activationValue : control.Index)
    (U : UnitaryOperator R) (i j : (Register.prod control R).Index) :
    controlledMatrix control activationValue U i j =
      if i.1 = j.1 then
        if i.1 = activationValue then U i.2 j.2
        else if i.2 = j.2 then 1 else 0
      else 0 := by
  change
    Matrix.blockDiagonal (controlledBlock activationValue U)
        (i.2, i.1) (j.2, j.1) = _
  rw [Matrix.blockDiagonal_apply]
  by_cases hcontrol : i.1 = j.1
  · by_cases hactive : j.1 = activationValue
    · simp [hcontrol, hactive, controlledBlock]
    · simp [hcontrol, hactive, controlledBlock, Matrix.one_apply]
  · simp [hcontrol]

private lemma controlledMatrix_mem_unitaryGroup (control : Register)
    (activationValue : control.Index) (U : UnitaryOperator R) :
    controlledMatrix control activationValue U ∈
      Matrix.unitaryGroup (Register.prod control R).Index ℂ := by
  apply reindex_matrix_mem_unitaryGroup
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
  have hblocks :
      (fun value => controlledBlock activationValue U value *
        (controlledBlock activationValue U value).conjTranspose) =
      (1 : control.Index → HilbertOperator R) := by
    funext value
    by_cases hvalue : value = activationValue
    · have hU :
          (U : HilbertOperator R) * (U : HilbertOperator R).conjTranspose = 1 := by
        rw [← Matrix.star_eq_conjTranspose]
        exact Matrix.mem_unitaryGroup_iff.mp U.property
      simp [controlledBlock, hvalue, hU]
    · simp [controlledBlock, hvalue]
  rw [hblocks, Matrix.blockDiagonal_one]

/-- Add a finite-dimensional control register at an explicit activation value. -/
public def controlled (control : Register) (activationValue : control.Index)
    (U : UnitaryOperator R) : UnitaryOperator (Register.prod control R) :=
  ofMatrix (controlledMatrix control activationValue U)
    (controlledMatrix_mem_unitaryGroup control activationValue U)

@[simp]
public lemma controlled_apply (control : Register) (activationValue : control.Index)
    (U : UnitaryOperator R) (i j : (Register.prod control R).Index) :
    controlled control activationValue U i j =
      if i.1 = j.1 then
        if i.1 = activationValue then U i.2 j.2
        else if i.2 = j.2 then 1 else 0
      else 0 := by
  change controlledMatrix control activationValue U i j = _
  exact controlledMatrix_apply control activationValue U i j

public lemma controlled_active (control : Register) (activationValue : control.Index)
    (U : UnitaryOperator R) (i j : (Register.prod control R).Index)
    (hcontrol : i.1 = j.1) (hactive : i.1 = activationValue) :
    controlled control activationValue U i j = U i.2 j.2 := by
  have hjactive : j.1 = activationValue := hcontrol.symm.trans hactive
  simp [controlled_apply, hcontrol, hjactive]

public lemma controlled_inactive (control : Register) (activationValue : control.Index)
    (U : UnitaryOperator R) (i j : (Register.prod control R).Index)
    (hcontrol : i.1 = j.1) (hinactive : i.1 ≠ activationValue) :
    controlled control activationValue U i j =
      if i.2 = j.2 then 1 else 0 := by
  have hjinactive : j.1 ≠ activationValue := fun hj => hinactive (hcontrol.trans hj)
  simp [controlled_apply, hcontrol, hjinactive]

end

end QuantumAlg.UnitaryOperator

end
