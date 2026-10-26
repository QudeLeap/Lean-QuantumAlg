/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Preparation.Carrier
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.Observation
import all QuantumAlg.Core.Execution.Basis.Reference
import all QuantumAlg.Core.Execution.Circuit.History

/-!
# Internal comparison of the true prepared seed and its complete reference density

Only mathematical input histories are grouped. Real storage and every local
and reference matrix entry remain. The unit-one tensor is a proof comparison
to the actual internally prepared complete frame, not a runtime preparation,
an external input promise, or a free reset [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution
open scoped Kronecker

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private def comparisonReferenceDensity {Local Reference : Register}
    (density : DensityOperator (Local.prod Reference)) : DensityOperator Reference :=
  DensityOperator.marginalLeft (DensityOperator.reindex (S := Reference.prod Local) density
    (Equiv.prodComm Local.Index Reference.Index))

private lemma comparisonReferenceDensity_mass {Local Reference : Register}
    (density : DensityOperator (Local.prod Reference)) :
    (comparisonReferenceDensity density).mass = density.mass :=
  (DensityOperator.marginalLeft_mass _).trans (DensityOperator.reindex_mass _ _)

private lemma comparison_tensor_seed {Source Target Reference : Register}
    (operator : Matrix Target.Index Source.Index ℂ) (seed : Source.Index)
    (reference : DensityOperator Reference) (left right : Target.Index)
    (leftRef rightRef : Reference.Index) :
    let kraus : Matrix (Target.prod Reference).Index (Source.prod Reference).Index ℂ :=
      operator ⊗ₖ (1 : HilbertOperator Reference)
    (kraus * (BasisReference.target seed reference).matrix * kraus.conjTranspose)
        (left, leftRef) (right, rightRef) =
      operator left seed * reference.matrix leftRef rightRef * star (operator right seed) := by
  let kraus : Matrix (Target.prod Reference).Index (Source.prod Reference).Index ℂ :=
    operator ⊗ₖ (1 : HilbertOperator Reference)
  let density : Matrix (Source.prod Reference).Index (Source.prod Reference).Index ℂ :=
    (BasisReference.target seed reference).matrix
  change (kraus * density * kraus.conjTranspose) (left, leftRef) (right, rightRef) = _
  have block :
      (kraus * density * kraus.conjTranspose) (left, leftRef) (right, rightRef) =
        (operator * density.submatrix
          (fun index => (index, leftRef)) (fun index => (index, rightRef)) *
          operator.conjTranspose) left right := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    change (∑ second : Source.Index × Reference.Index,
      (∑ first : Source.Index × Reference.Index,
        (operator left first.1 * (1 : HilbertOperator Reference) leftRef first.2) *
          density first second) *
        star (operator right second.1 *
          (1 : HilbertOperator Reference) rightRef second.2)) = _
    simp [Fintype.sum_prod_type, Matrix.one_apply, apply_ite]
  rw [block]
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply,
    density, BasisReference.target_entry, ite_and, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

private lemma comparison_embedding_target {Source Target Reference : Register}
    (embedding : Source.Index ↪ Target.Index) (seed : Source.Index)
    (reference : DensityOperator Reference) :
    BasisEmbedding.density (BasisEmbedding.withReference embedding Reference)
        (BasisReference.target seed reference) =
      BasisReference.target (embedding seed) reference := by
  apply DensityOperator.ext
  ext ⟨left, leftRef⟩ ⟨right, rightRef⟩
  change (BasisEmbedding.matrix (BasisEmbedding.withReference embedding Reference) *
    (BasisReference.target seed reference).matrix *
    (BasisEmbedding.matrix (BasisEmbedding.withReference embedding Reference)).conjTranspose)
      (left, leftRef) (right, rightRef) = _
  rw [BasisEmbedding.reference_matrix, comparison_tensor_seed, BasisReference.target_entry]
  by_cases first : left = embedding seed <;> by_cases second : right = embedding seed <;>
    simp only [BasisEmbedding.matrix, first, second, eq_comm, if_true, if_false,
      star_one, star_zero, one_mul, mul_one, zero_mul, mul_zero, and_self, and_false, false_and]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev ComparisonCtx := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat]

/-- A mathematical unit-one comparison keeps each actual compressed Store/reference density. -/
def unitSeedComparison {Reference : Register} {History : Type} [Fintype History]
    (state : State (ComparisonCtx base noQuantum m ell width) Reference
      (model.HiddenState × History)) :
    ExecutionState (Store (ComparisonCtx base noQuantum m ell width) × (model.HiddenState × Unit))
      ((Recycling.Carrier.units modulus.toNat).prod Reference) where
  block entry := BasisReference.target 1
    (comparisonReferenceDensity
      ((state.mapHistory (fun record => (record.1, ()))).block entry))
  total_le_one := by
    simpa only [BasisReference.target_mass, comparisonReferenceDensity_mass] using
      (state.mapHistory (fun record => (record.1, ()))).total_le_one

omit [NeZero modulus.toNat] in
private lemma comparison_compressed_block {Reference : Register} {History : Type} [Fintype History]
    (state : State (ComparisonCtx base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (entry : Store (ComparisonCtx base noQuantum m ell width) × (model.HiddenState × Unit)) :
    ((state.mapHistory (fun record => (record.1, ()))).block entry).matrix =
      (state.filterClassical (fun original => original.1 = entry.1)).quantumMarginal.matrix := by
  refine Eq.trans ?_ (BasisSeeded.store_matrix state entry.1)
  simp only [State.mapHistory, ExecutionState.mapClassical_block_matrix]
  apply Finset.sum_congr rfl
  intro original _
  have condition : (original.1, (original.2.1, ())) = entry ↔ original.1 = entry.1 := by
    constructor
    · exact congrArg Prod.fst
    · intro same
      let _ : Subsingleton (model.HiddenState × Unit) := by
        change Subsingleton (Unit × Unit)
        infer_instance
      exact Prod.ext same (Subsingleton.elim _ _)
  simp only [condition]

omit [NeZero modulus.toNat] in
private lemma comparison_reference_entry {Reference : Register} {History : Type} [Fintype History]
    (state : State (ComparisonCtx base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (seeded : BasisSeeded.Holds (preparedSeed base noQuantum m ell width modulus.toNat) state)
    (entry : Store (ComparisonCtx base noQuantum m ell width) × (model.HiddenState × Unit))
    (leftRef rightRef : Reference.Index) :
    (comparisonReferenceDensity
        ((state.mapHistory (fun record => (record.1, ()))).block entry)).matrix leftRef rightRef =
      (state.filterClassical (fun original => original.1 = entry.1)).quantumMarginal.matrix
        (preparedSeed base noQuantum m ell width modulus.toNat, leftRef)
        (preparedSeed base noQuantum m ell width modulus.toNat, rightRef) := by
  unfold comparisonReferenceDensity
  rw [DensityOperator.marginalLeft_matrix]
  simp only [DensityOperator.reindex_entry, comparison_compressed_block]
  exact BasisSeeded.reference_entry _ state seeded entry.1 leftRef rightRef

/-- The same actual seeded state is its unit-one encoding after only input-history grouping. -/
lemma unitSeedComparison_encoded {Reference : Register} {History : Type} [Fintype History]
    (state : State (ComparisonCtx base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (seeded : BasisSeeded.Holds (preparedSeed base noQuantum m ell width modulus.toNat) state) :
    encodeUnitState base noQuantum m ell width modulus
        (unitSeedComparison base noQuantum m ell width modulus state) =
      state.mapHistory (fun record => (record.1, ())) := by
  apply ExecutionState.ext
  intro entry
  apply DensityOperator.ext
  ext ⟨left, leftRef⟩ ⟨right, rightRef⟩
  change (BasisEmbedding.density
    (BasisEmbedding.withReference (Placement.zeroEmbedding base noQuantum m ell width modulus)
      Reference)
    (BasisReference.target 1 (comparisonReferenceDensity
      ((state.mapHistory (fun record => (record.1, ()))).block entry)))).matrix
        (left, leftRef) (right, rightRef) = _
  rw [comparison_embedding_target, BasisReference.target_entry,
    ← preparedSeed_zeroEmbedding base noQuantum m ell width modulus,
    comparison_reference_entry base noQuantum m ell width modulus state seeded entry leftRef
      rightRef]
  exact (seeded entry.1 left right leftRef rightRef).symm.trans
    (congrArg (fun matrix => matrix (left, leftRef) (right, rightRef))
      (comparison_compressed_block base noQuantum m ell width state entry)).symm

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
