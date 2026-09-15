/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Prepared.Unitary
import all QuantumAlg.Core.Base.State.Density.BasisSupport

/-!
# Basis support of independently prepared joint density operators

The prescribed pure factor and the entire original context-reference
matrix use the existing physical preparation equivalence. Their exact
entries show that a fixed fresh basis state and a locally specified old
support also determine the support of the complete prepared state.
Arbitrary old coherences and reference extensions remain allowed
[dW19, qcnotes.tex:5381,5394,6827]. These are matrix laws for the existing
pure tensor construction, with no new execution or allocation mechanism.
-/

namespace QuantumAlg.Execution

noncomputable section

variable {ctx : RuntimeCtx .quantum} {count : Nat} {Reference : Register}

/-- Exact independent tensor entries use the same actual fresh/old/reference wire equivalence. -/
theorem preparedDensity_joined_entry (key : StorageKey) (layout : QuantumLayout count)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (prepared : NormalizedVector layout.register)
    (state : DensityOperator (Register.prod ctx.register Reference))
    (newRow newColumn : layout.register.Index)
    (oldRow oldColumn : (Register.prod ctx.register Reference).Index) :
    (preparedDensity key layout fresh disjoint prepared Reference state).matrix
      (prepareContextBasisEquiv ctx Reference key layout fresh disjoint (newRow, oldRow))
      (prepareContextBasisEquiv ctx Reference key layout fresh disjoint (newColumn, oldColumn)) =
        (prepared.vec newRow * star (prepared.vec newColumn)) * state.matrix oldRow oldColumn := by
  rw [preparedDensity, DensityOperator.reindex_entry]
  simp only [Equiv.symm_apply_apply]
  rfl

/-- Tracing only the reference retains the same actual fresh amplitudes and old local entries. -/
theorem preparedDensity_local_joined_entry (key : StorageKey) (layout : QuantumLayout count)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (prepared : NormalizedVector layout.register)
    (state : DensityOperator (Register.prod ctx.register Reference))
    (newRow newColumn : layout.register.Index) (oldRow oldColumn : ctx.register.Index) :
    (preparedDensity key layout fresh disjoint prepared Reference state).marginalLeft.matrix
      (preparedLocalBasisEquiv ctx key layout fresh disjoint (newRow, oldRow))
      (preparedLocalBasisEquiv ctx key layout fresh disjoint (newColumn, oldColumn)) =
        (prepared.vec newRow * star (prepared.vec newColumn)) *
          state.marginalLeft.matrix oldRow oldColumn := by
  rw [DensityOperator.marginalLeft_matrix]
  calc
    _ = ∑ reference : Reference.Index,
        (prepared.vec newRow * star (prepared.vec newColumn)) *
          state.matrix (oldRow, reference) (oldColumn, reference) := by
      apply Finset.sum_congr rfl
      intro reference _
      exact preparedDensity_joined_entry key layout fresh disjoint prepared state
        newRow newColumn (oldRow, reference) (oldColumn, reference)
    _ = _ := by
      rw [← Finset.mul_sum]
      exact congrArg (fun value : ℂ =>
        (prepared.vec newRow * star (prepared.vec newColumn)) * value)
          (DensityOperator.marginalLeft_matrix state oldRow oldColumn).symm

/-- Local old support and the fixed fresh basis determine the actual prepared local support. -/
theorem preparedDensity_basis_support (key : StorageKey) (layout : QuantumLayout count)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (seed : layout.register.Index) (state : DensityOperator (Register.prod ctx.register Reference))
    (admissible : ctx.register.Index → Prop)
    (support : ∀ basis, ¬admissible basis → state.marginalLeft.matrix basis basis = 0)
    (basis : (ctx.addOwnedLayout key layout fresh disjoint).register.Index)
    (outside : ¬(((preparedLocalBasisEquiv ctx key layout fresh disjoint).symm basis).1 = seed ∧
      admissible ((preparedLocalBasisEquiv ctx key layout fresh disjoint).symm basis).2)) :
    (preparedDensity key layout fresh disjoint (NormalizedVector.ket seed)
      Reference state).marginalLeft.matrix basis basis = 0 := by
  classical
  obtain ⟨⟨newBasis, oldBasis⟩, rfl⟩ :=
    (preparedLocalBasisEquiv ctx key layout fresh disjoint).surjective basis
  have absent : ¬(newBasis = seed ∧ admissible oldBasis) := by
    simpa only [Equiv.symm_apply_apply] using outside
  rw [preparedDensity_local_joined_entry]
  by_cases same : newBasis = seed
  · have oldOutside : ¬admissible oldBasis := fun allowed => absent ⟨same, allowed⟩
    rw [support oldBasis oldOutside, mul_zero]
  · have amplitude : (NormalizedVector.ket (R := layout.register) seed).vec newBasis = 0 := by
      simp only [NormalizedVector.ket_apply, if_neg same]
    rw [amplitude, zero_mul, zero_mul]

end

end QuantumAlg.Execution
