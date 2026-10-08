/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Preparation.Laws
import all QuantumAlg.Core.Execution.Reindex

/-!
# Actual preparation from a context with no quantum systems

If the old context contains no quantum wires, its register has exactly one
basis label. A normalized input may still have arbitrary classical blocks
and a correlated external reference. The actual zero-preparation instruction's
local marginal is nevertheless precisely its canonical pure zero state
[dW19, qcnotes.tex:5381,5394,6827].

The new local register is identified by the same wire-level assembly used
by the interpreter. Its equivalence is obtained by adjoining the unique
empty old basis, not by comparing Hilbert-space dimensions. Classical
storage is unrestricted, and every reference block participates in the
normalization calculation.
-/

namespace QuantumAlg.Execution

noncomputable section

variable {systemCount : Nat} {ctx : RuntimeCtx .quantum} {Reference : Register}

private def emptyContextBasis (ctx : RuntimeCtx .quantum) (empty : ctx.systemCount = 0) :
    ctx.register.Index := by
  intro wire
  exact False.elim (by have bound := wire.isLt; omega)

private theorem emptyContextBasis_unique (ctx : RuntimeCtx .quantum)
    (empty : ctx.systemCount = 0) (left right : ctx.register.Index) : left = right := by
  funext wire
  exact False.elim (by have bound := wire.isLt; omega)

/-- The actual prepared layout supplies every local wire when the previous context has none. -/
def preparedEmptyBasisEquiv (ctx : RuntimeCtx .quantum) (key : StorageKey)
    (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (empty : ctx.systemCount = 0) :
    layout.register.Index ≃ (ctx.addOwnedLayout key layout fresh disjoint).register.Index :=
  let assembly := preparedLocalBasisEquiv ctx key layout fresh disjoint
  { toFun := fun basis => assembly (basis, emptyContextBasis ctx empty)
    invFun := fun basis => (assembly.symm basis).1
    left_inv := fun basis => congrArg Prod.fst
      (assembly.symm_apply_apply (basis, emptyContextBasis ctx empty))
    right_inv := by
      intro basis
      have pair : ((assembly.symm basis).1, emptyContextBasis ctx empty) =
          assembly.symm basis :=
        Prod.ext rfl (emptyContextBasis_unique ctx empty (emptyContextBasis ctx empty)
          (assembly.symm basis).2)
      exact (congrArg assembly pair).trans (assembly.apply_symm_apply basis) }

private theorem preparedEmptyBasisEquiv_apply (key : StorageKey)
    (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (empty : ctx.systemCount = 0) (basis : layout.register.Index) :
    preparedEmptyBasisEquiv ctx key layout fresh disjoint empty basis =
      preparedLocalBasisEquiv ctx key layout fresh disjoint
        (basis, emptyContextBasis ctx empty) := rfl

variable {C : Type} [Fintype C]

private theorem emptyContext_reference_trace
    (state : ExecutionState C (Register.prod ctx.register Reference))
    (empty : ctx.systemCount = 0) (normalized : state.IsNormalized) :
    (∑ reference : Reference.Index, state.quantumMarginal.matrix
      (emptyContextBasis ctx empty, reference) (emptyContextBasis ctx empty, reference)) =
        (1 : ℂ) := by
  have traceOne : state.quantumMarginal.matrix.trace = (1 : ℂ) := by
    apply Complex.ext
    · change state.quantumMarginal.mass = 1
      exact (ExecutionState.quantumMarginal_mass state).trans normalized
    · exact DensityOperator.trace_im_eq_zero state.quantumMarginal
  let : Subsingleton ctx.register.Index := ⟨emptyContextBasis_unique ctx empty⟩
  calc
    _ = ∑ oldBasis : ctx.register.Index, ∑ reference : Reference.Index,
        state.quantumMarginal.matrix (oldBasis, reference) (oldBasis, reference) :=
      (Fintype.sum_subsingleton
        (fun oldBasis : ctx.register.Index => ∑ reference : Reference.Index,
          state.quantumMarginal.matrix (oldBasis, reference) (oldBasis, reference))
        (emptyContextBasis ctx empty)).symm
    _ = state.quantumMarginal.matrix.trace :=
      (Fintype.sum_prod_type (fun basis : ctx.register.Index × Reference.Index =>
        state.quantumMarginal.matrix basis basis)).symm
    _ = 1 := traceOne

/-- The complete normalized input contributes exactly one to every prepared outer-product entry. -/
theorem prepareContext_empty_local_entry
    (state : ExecutionState C (Register.prod ctx.register Reference))
    (key : StorageKey) (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (prepared : NormalizedVector layout.register) (empty : ctx.systemCount = 0)
    (normalized : state.IsNormalized) (newRow newColumn : layout.register.Index) :
    (prepareContext state key layout fresh disjoint prepared).quantumMarginal.marginalLeft.matrix
      (preparedEmptyBasisEquiv ctx key layout fresh disjoint empty newRow)
      (preparedEmptyBasisEquiv ctx key layout fresh disjoint empty newColumn) =
        prepared.vec newRow * star (prepared.vec newColumn) := by
  have entry (reference : Reference.Index) :
      (prepareContext state key layout fresh disjoint prepared).quantumMarginal.matrix
        (preparedEmptyBasisEquiv ctx key layout fresh disjoint empty newRow, reference)
        (preparedEmptyBasisEquiv ctx key layout fresh disjoint empty newColumn, reference) =
      (prepared.vec newRow * star (prepared.vec newColumn)) *
        state.quantumMarginal.matrix (emptyContextBasis ctx empty, reference)
          (emptyContextBasis ctx empty, reference) := by
    simpa only [prepareContextBasisEquiv_pair, preparedEmptyBasisEquiv_apply] using
      prepareContext_quantumMarginal_joined_entry state key layout fresh disjoint prepared
        newRow newColumn (emptyContextBasis ctx empty, reference)
          (emptyContextBasis ctx empty, reference)
  rw [DensityOperator.marginalLeft_matrix]
  simp only [entry]
  rw [← Finset.mul_sum, emptyContext_reference_trace state empty normalized, mul_one]

/-- The local density is exactly the prescribed pure state on the actual newly allocated wires. -/
theorem prepareContext_empty_local_density
    (state : ExecutionState C (Register.prod ctx.register Reference))
    (key : StorageKey) (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (prepared : NormalizedVector layout.register) (empty : ctx.systemCount = 0)
    (normalized : state.IsNormalized) :
    (prepareContext state key layout fresh disjoint prepared).quantumMarginal.marginalLeft =
      DensityOperator.reindex
        (S := (ctx.addOwnedLayout key layout fresh disjoint).register)
        (DensityOperator.ofPure prepared)
        (preparedEmptyBasisEquiv ctx key layout fresh disjoint empty) := by
  apply DensityOperator.ext
  ext row column
  obtain ⟨newRow, rfl⟩ :=
    (preparedEmptyBasisEquiv ctx key layout fresh disjoint empty).surjective row
  obtain ⟨newColumn, rfl⟩ :=
    (preparedEmptyBasisEquiv ctx key layout fresh disjoint empty).surjective column
  rw [DensityOperator.reindex_entry, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact prepareContext_empty_local_entry state key layout fresh disjoint prepared empty normalized
    newRow newColumn

end

end QuantumAlg.Execution

namespace QuantumAlg.Circuit

open Execution

noncomputable section

variable {systemCount : Nat} {ctx : RuntimeCtx .quantum} {Reference : Register}
  {H : Type} [Fintype H]

/-- Actual zero preparation produces its canonical pure state from every normalized
classical-reference input whenever the old context has no quantum systems. -/
theorem prepareZero_empty_local_density {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
    (state : State ctx Reference (classicalOracles.HiddenState × H))
    (key : StorageKey) (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (empty : ctx.systemCount = 0)
    (normalized : state.IsNormalized) :
    ((Circuit.prepareZero (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles)
      ctx key layout fresh disjoint).execute
      Reference state).quantumMarginal.marginalLeft =
        DensityOperator.reindex
          (S := (ctx.addOwnedLayout key layout fresh disjoint).register)
          (DensityOperator.ofPure (BasisPreparation.zero layout).normalized)
          (preparedEmptyBasisEquiv ctx key layout fresh disjoint empty) := by
  rw [execute_prepareZero]
  simp only [State.mapHistory, ExecutionState.mapClassical_quantumMarginal,
    State.prepare_quantumMarginal]
  exact prepareContext_empty_local_density state key layout fresh disjoint
    (BasisPreparation.zero layout).normalized empty normalized

end

end QuantumAlg.Circuit
