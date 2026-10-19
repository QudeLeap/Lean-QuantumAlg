/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Prepared.Unitary
import all QuantumAlg.Core.Base.State.Density.BasisSupport
import all QuantumAlg.Core.Execution.Reference.Unitary

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
lemma preparedDensity_joined_entry (key : StorageKey) (layout : QuantumLayout count)
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
lemma preparedDensity_local_joined_entry (key : StorageKey) (layout : QuantumLayout count)
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
lemma preparedDensity_basis_support (key : StorageKey) (layout : QuantumLayout count)
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

/-- A local unitary that loads one fixed fresh ket transports the entire old
quantum-reference density, including its off-diagonal entries. -/
lemma preparedDensity_load_ket (key : StorageKey) (layout : QuantumLayout count)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (source target : layout.register.Index)
    (operator : UnitaryOperator (ctx.addOwnedLayout key layout fresh disjoint).register)
    (action : ∀ old : ctx.register.Index,
      operator.apply (NormalizedVector.ket
        (preparedLocalBasisEquiv ctx key layout fresh disjoint (source, old))) =
      NormalizedVector.ket
        (preparedLocalBasisEquiv ctx key layout fresh disjoint (target, old)))
    (state : DensityOperator (Register.prod ctx.register Reference)) :
    DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference))
      (preparedDensity key layout fresh disjoint (NormalizedVector.ket source)
        Reference state) =
      preparedDensity key layout fresh disjoint (NormalizedVector.ket target)
        Reference state := by
  classical
  let assembly := preparedLocalBasisEquiv ctx key layout fresh disjoint
  let permutation : Equiv.Perm (ctx.addOwnedLayout key layout fresh disjoint).register.Index :=
    assembly.symm.trans
      ((Equiv.prodCongr (Equiv.swap source target) (Equiv.refl ctx.register.Index)).trans
        assembly)
  let replacement : UnitaryOperator (ctx.addOwnedLayout key layout fresh disjoint).register :=
    UnitaryOperator.ofPerm permutation.symm
  have support : ∀ basis, ¬(assembly.symm basis).1 = source →
      (preparedDensity key layout fresh disjoint (NormalizedVector.ket source)
        Reference state).marginalLeft.matrix basis basis = 0 := by
    intro basis outside
    apply preparedDensity_basis_support key layout fresh disjoint source state
      (fun _ => True) (by simp) basis
    intro allowed
    exact outside allowed.1
  have columns : ∀ basis, (assembly.symm basis).1 = source → ∀ row,
      operator row basis = replacement row basis := by
    intro basis allowed row
    obtain ⟨⟨new, old⟩, rfl⟩ := assembly.surjective basis
    have same : new = source := by simpa only [Equiv.symm_apply_apply] using allowed
    subst new
    have actual := congrArg (fun ψ : NormalizedVector _ => ψ.vec row) (action old)
    have prescribed := congrArg (fun ψ : NormalizedVector _ => ψ.vec row)
      (UnitaryOperator.ofPerm_apply_ket permutation.symm
        (assembly (source, old)))
    have swapped : permutation (assembly (source, old)) = assembly (target, old) := by
      simp [permutation, assembly]
    change ((UnitaryOperator.ofPerm permutation.symm).apply
      (NormalizedVector.ket (assembly (source, old)))).vec row =
        (NormalizedVector.ket (permutation (assembly (source, old)))).vec row
      at prescribed
    rw [swapped] at prescribed
    have values := actual.trans prescribed.symm
    change HilbertOperator.applyVec
        (operator : HilbertOperator (ctx.addOwnedLayout key layout fresh disjoint).register)
        (NormalizedVector.ket (assembly (source, old))) row =
      HilbertOperator.applyVec
        (replacement : HilbertOperator (ctx.addOwnedLayout key layout fresh disjoint).register)
        (NormalizedVector.ket (assembly (source, old))) row at values
    simpa only [HilbertOperator.applyVec_ket] using values
  have same := DensityOperator.applyLocalUnitary_eq_on_basis_support
    (preparedDensity key layout fresh disjoint (NormalizedVector.ket source)
      Reference state) (fun basis => (assembly.symm basis).1 = source)
    operator replacement support columns
  rw [same]
  apply DensityOperator.ext
  ext row column
  obtain ⟨⟨freshRow, oldRow⟩, rfl⟩ :=
    (prepareContextBasisEquiv ctx Reference key layout fresh disjoint).surjective row
  obtain ⟨⟨freshColumn, oldColumn⟩, rfl⟩ :=
    (prepareContextBasisEquiv ctx Reference key layout fresh disjoint).surjective column
  rcases oldRow with ⟨oldRow, refRow⟩
  rcases oldColumn with ⟨oldColumn, refColumn⟩
  have permuted (freshBasis : layout.register.Index) (old : ctx.register.Index) :
      permutation.symm (assembly (freshBasis, old)) =
        assembly (Equiv.swap source target freshBasis, old) := by
    simp [permutation, assembly, Equiv.symm_swap]
  have amplitude (basis : layout.register.Index) :
      (NormalizedVector.ket source).vec (Equiv.swap source target basis) =
        (NormalizedVector.ket target).vec basis := by
    simp only [NormalizedVector.ket_apply]
    by_cases h : basis = target
    · subst basis
      simp
    · have ne : Equiv.swap source target basis ≠ source := by
        intro equal
        have := congrArg (Equiv.swap source target) equal
        exact h (by simpa only [Equiv.swap_apply_self, Equiv.swap_apply_left] using this)
      simp [h, ne]
  change (DensityOperator.applyUnitary (UnitaryOperator.prodTensor replacement
      (1 : UnitaryOperator Reference))
      (preparedDensity key layout fresh disjoint (NormalizedVector.ket source)
        Reference state)).matrix
      (assembly (freshRow, oldRow), refRow) (assembly (freshColumn, oldColumn), refColumn) = _
  rw [DensityOperator.localUnitary_block]
  change ((permutation⁻¹ : Equiv.Perm _).permMatrix ℂ *
    (preparedDensity key layout fresh disjoint (NormalizedVector.ket source)
      Reference state).matrix.submatrix (fun i => (i, refRow)) (fun j => (j, refColumn)) *
    ((permutation⁻¹ : Equiv.Perm _).permMatrix ℂ).conjTranspose)
      (assembly (freshRow, oldRow)) (assembly (freshColumn, oldColumn)) = _
  rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  simp only [Matrix.submatrix_apply, Matrix.submatrix_apply]
  change (preparedDensity key layout fresh disjoint (NormalizedVector.ket source)
      Reference state).matrix
      (permutation.symm (assembly (freshRow, oldRow)), refRow)
      (permutation.symm (assembly (freshColumn, oldColumn)), refColumn) =
    (preparedDensity key layout fresh disjoint (NormalizedVector.ket target)
      Reference state).matrix
      (assembly (freshRow, oldRow), refRow) (assembly (freshColumn, oldColumn), refColumn)
  rw [permuted, permuted]
  change (preparedDensity key layout fresh disjoint (NormalizedVector.ket source)
      Reference state).matrix
      (prepareContextBasisEquiv ctx Reference key layout fresh disjoint
        (Equiv.swap source target freshRow, (oldRow, refRow)))
      (prepareContextBasisEquiv ctx Reference key layout fresh disjoint
        (Equiv.swap source target freshColumn, (oldColumn, refColumn))) =
    (preparedDensity key layout fresh disjoint (NormalizedVector.ket target)
      Reference state).matrix
      (prepareContextBasisEquiv ctx Reference key layout fresh disjoint
        (freshRow, (oldRow, refRow)))
      (prepareContextBasisEquiv ctx Reference key layout fresh disjoint
        (freshColumn, (oldColumn, refColumn)))
  rw [preparedDensity_joined_entry, preparedDensity_joined_entry,
    amplitude, amplitude]

end

end QuantumAlg.Execution
