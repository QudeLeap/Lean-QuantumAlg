/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Control.Operator
import all QuantumAlg.Core.Base.Control.Operator
import all QuantumAlg.Core.Base.Gate.Unitary

/-!
# Exact operator transport between basis conventions

Changing basis labels preserves identity, composition and the original
operator after inverse transport. These are mathematical identities and
introduce no executable gate or access capability.
-/

namespace QuantumAlg.UnitaryOperator

noncomputable section

variable {R S T : Register}

/-- Relabelling the identity gives the identity on the target register. -/
public theorem unitaryOperator_reindex_one (equivalence : R.Index ≃ S.Index) :
    reindex equivalence (1 : UnitaryOperator R) = (1 : UnitaryOperator S) := by
  apply Subtype.ext
  exact Matrix.submatrix_one_equiv equivalence.symm

/-- Exact operator composition commutes with a common change of basis labels. -/
public theorem unitaryOperator_reindex_mul (equivalence : R.Index ≃ S.Index)
    (first second : UnitaryOperator R) :
    reindex equivalence (first * second) =
      reindex equivalence first * reindex equivalence second := by
  apply Subtype.ext
  exact (Matrix.submatrix_mul_equiv (first : HilbertOperator R) (second : HilbertOperator R)
    equivalence.symm equivalence.symm equivalence.symm).symm

/-- Two consecutive basis transports equal their composite transport. -/
public theorem unitaryOperator_reindex_trans (first : R.Index ≃ S.Index)
    (second : S.Index ≃ T.Index) (operator : UnitaryOperator R) :
    reindex second (reindex first operator) = reindex (first.trans second) operator := by
  apply Subtype.ext
  rfl

/-- Transporting back to the original basis restores the complete operator. -/
public theorem unitaryOperator_reindex_cancel (equivalence : R.Index ≃ S.Index)
    (operator : UnitaryOperator R) :
    reindex equivalence.symm (reindex equivalence operator) = operator := by
  apply Subtype.ext
  ext row column
  change operator (equivalence.symm (equivalence row))
    (equivalence.symm (equivalence column)) = operator row column
  rw [equivalence.symm_apply_apply, equivalence.symm_apply_apply]

end

end QuantumAlg.UnitaryOperator

namespace QuantumAlg.HilbertVector

noncomputable section

variable {R S T : Register}

/-- Transport a raw vector along a finite basis equivalence. -/
@[expose] public def reindex (equivalence : R.Index ≃ S.Index)
    (state : HilbertVector R) : HilbertVector S :=
  WithLp.toLp 2 fun index => state (equivalence.symm index)

@[simp] public theorem reindex_apply (equivalence : R.Index ≃ S.Index)
    (state : HilbertVector R) (index : S.Index) :
    reindex equivalence state index = state (equivalence.symm index) := rfl

/-- A finite basis equivalence preserves the Euclidean norm of a vector. -/
public theorem norm_reindex (equivalence : R.Index ≃ S.Index)
    (state : HilbertVector R) :
    ‖reindex equivalence state‖ = ‖state‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  rw [← Equiv.sum_comp equivalence
    (fun index : S.Index => ‖reindex equivalence state index‖ ^ 2)]
  simp only [reindex_apply, Equiv.symm_apply_apply]

/-- Reindexing a computational-basis vector transports its basis label. -/
@[simp] public theorem reindex_ket (equivalence : R.Index ≃ S.Index)
    (index : R.Index) :
    reindex equivalence
        (NormalizedVector.ket (R := R) index : HilbertVector R) =
      (NormalizedVector.ket (R := S) (equivalence index) : HilbertVector S) := by
  apply WithLp.ofLp_injective
  funext output
  by_cases same : output = equivalence index
  · subst output
    simp [NormalizedVector.ket_apply]
  · have pulledBack : equivalence.symm output ≠ index := by
      intro equal
      apply same
      rw [← equivalence.apply_symm_apply output, equal]
    simp [NormalizedVector.ket_apply, same, pulledBack]

/-- Two consecutive vector-coordinate transports equal their composite transport. -/
public theorem reindex_trans (first : R.Index ≃ S.Index)
    (second : S.Index ≃ T.Index) (state : HilbertVector R) :
    reindex second (reindex first state) = reindex (first.trans second) state := by
  apply WithLp.ofLp_injective
  funext index
  rfl

/-- Transporting a vector to new coordinates and back restores it exactly. -/
@[simp] public theorem reindex_symm_reindex (equivalence : R.Index ≃ S.Index)
    (state : HilbertVector R) :
    reindex equivalence.symm (reindex equivalence state) = state := by
  apply WithLp.ofLp_injective
  funext index
  simp

/-- Transporting a vector from the target coordinates and back also cancels. -/
@[simp] public theorem reindex_reindex_symm (equivalence : R.Index ≃ S.Index)
    (state : HilbertVector S) :
    reindex equivalence (reindex equivalence.symm state) = state := by
  apply WithLp.ofLp_injective
  funext index
  simp

end


end QuantumAlg.HilbertVector

namespace QuantumAlg.NormalizedVector

noncomputable section

variable {R S : Register}

/-- Transport a normalized vector along a finite basis equivalence. -/
@[expose] public def reindex (equivalence : R.Index ≃ S.Index)
    (state : NormalizedVector R) : NormalizedVector S :=
  ofVector (HilbertVector.reindex equivalence state.vec) (by
    rw [HilbertVector.norm_reindex, state.norm_eq_one])

@[simp] public theorem reindex_apply (equivalence : R.Index ≃ S.Index)
    (state : NormalizedVector R) (index : S.Index) :
    reindex equivalence state index = state (equivalence.symm index) :=
  rfl

end

end QuantumAlg.NormalizedVector

namespace QuantumAlg.UnitaryOperator

noncomputable section

variable {R S : Register}

/-- Applying a transported unitary to a transported raw vector commutes with
the same basis equivalence. -/
public theorem reindex_applyVec (equivalence : R.Index ≃ S.Index)
    (operator : UnitaryOperator R) (state : HilbertVector R) :
    (reindex equivalence operator).applyVec
        (HilbertVector.reindex equivalence state) =
      HilbertVector.reindex equivalence (operator.applyVec state) := by
  apply WithLp.ofLp_injective
  funext output
  simp only [applyVec_apply, coe_reindex, Matrix.reindex_apply,
    Matrix.submatrix_apply, HilbertVector.reindex_apply]
  rw [← Equiv.sum_comp equivalence
    (fun input =>
      (operator : HilbertOperator R)
        (equivalence.symm output) (equivalence.symm input) *
          state (equivalence.symm input))]
  simp only [Equiv.symm_apply_apply]

end


end QuantumAlg.UnitaryOperator
