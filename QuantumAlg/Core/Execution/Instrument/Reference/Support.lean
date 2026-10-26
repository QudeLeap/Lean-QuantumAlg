/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Instrument.Reference
import all QuantumAlg.Core.Execution.Instrument.Reference
import all QuantumAlg.Core.Base.State.Density.BasisSupport

/-!
# Actual local Kraus blocks retain reference support

An arbitrary local matrix cannot create an unsupported reference label.
The same statement holds after summing all original records and actual
measurement outcomes. No canonical arithmetic premise or preservation of
physical addresses is required, including on exceptional input labels.
-/

@[expose] public section

namespace QuantumAlg.Execution.Instrument

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.decEq

variable {Local Reference : Register}

/-- Local conjugation preserves every internally established reference-support predicate. -/
lemma local_conjugation_support (operator : HilbertOperator Local)
    (state : DensityOperator (Local.prod Reference)) (allowed : Reference.Index → Prop)
    (supported : ∀ basis, ¬allowed basis.2 → state.matrix basis basis = 0)
    (row : (Local.prod Reference).Index) (absent : ¬allowed row.2) :
    (referenceLift Reference operator * state.matrix *
      (referenceLift Reference operator).conjTranspose) row row = 0 := by
  classical
  have zeroProduct (column : (Local.prod Reference).Index) :
      (referenceLift Reference operator * state.matrix) row column = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro basis _
    by_cases same : row.2 = basis.2
    · have unsupported : ¬allowed basis.2 := fun valid => absent (same.symm ▸ valid)
      rw [DensityOperator.row_zero_of_diagonal_zero state basis
        (supported basis unsupported) column, mul_zero]
    · simp only [referenceLift, if_neg same, mul_zero, zero_mul]
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro column _
  rw [zeroProduct, zero_mul]

/-- A concrete full-record local-Kraus equation preserves source support for all inputs. -/
lemma retained_reference_support
    {Original Outcome Result : Type} [Fintype Original] [Fintype Outcome] [Fintype Result]
    (actual : ExecutionState Original (Local.prod Reference) →
      ExecutionState Result (Local.prod Reference))
    (record : Original → Outcome → Result)
    (operators : Original → Outcome → HilbertOperator Local)
    (blocks : ∀ state result,
      ((actual state).block result).matrix =
        ∑ original : Original, ∑ outcome : Outcome,
          if record original outcome = result then
            referenceLift Reference (operators original outcome) * (state.block original).matrix *
              (referenceLift Reference (operators original outcome)).conjTranspose
          else 0)
    (allowed : Reference.Index → Prop)
    (state : ExecutionState Original (Local.prod Reference))
    (supported : ∀ original basis, ¬allowed basis.2 →
      (state.block original).matrix basis basis = 0)
    (result : Result) (basis : (Local.prod Reference).Index) (absent : ¬allowed basis.2) :
    ((actual state).block result).matrix basis basis = 0 := by
  classical
  rw [blocks, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro original _
  rw [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro outcome _
  by_cases selected : record original outcome = result
  · simp only [if_pos selected]
    exact local_conjugation_support (operators original outcome)
      (state.block original) allowed (supported original) basis absent
  · simp only [if_neg selected, Matrix.zero_apply]

end

end QuantumAlg.Execution.Instrument
