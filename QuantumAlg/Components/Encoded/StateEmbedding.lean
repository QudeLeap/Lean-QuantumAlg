/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Unitary.Permutation
public import QuantumAlg.Core.Base.State.Density
public import QuantumAlg.Core.Base.Gate.Effect.Extension
public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Gate.Effect.Extension
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.State.Density
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Faithful computational-basis embeddings of complete states

An injective basis encoding is an isometry, including for mixed inputs and
arbitrary external reference systems. The matrix sandwich below preserves
trace and every encoded matrix entry. It is a mathematical comparison of two
representations, never an executable gate or a free physical conversion.
Unitary compatibility must be proved for the actual operators being compared
[dW19, qcnotes.tex:5381-5409].
-/

namespace QuantumAlg.BasisEmbedding

noncomputable section

open scoped ComplexOrder Kronecker

variable {R S : Register}

/-- The rectangular isometry that places each source basis at its prescribed label. -/
public def matrix (embedding : S.Index ↪ R.Index) : Matrix R.Index S.Index ℂ :=
  fun row column => if embedding column = row then 1 else 0

/-- Different source columns of the basis injection are orthonormal. -/
public lemma adjoint_mul (embedding : S.Index ↪ R.Index) :
    (matrix embedding).conjTranspose * matrix embedding = 1 := by
  classical
  ext left right
  simp [matrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, embedding.injective.eq_iff, eq_comm]

/-- The encoding changes neither total mass nor normalization. -/
public lemma trace_sandwich (embedding : S.Index ↪ R.Index)
    (operator : HilbertOperator S) :
    (matrix embedding * operator * (matrix embedding).conjTranspose).trace =
      operator.trace := by
  rw [Matrix.trace_mul_cycle, adjoint_mul, Matrix.one_mul]

/-- Encode the complete mixed state, retaining all off-diagonal coherences. -/
public def density (embedding : S.Index ↪ R.Index) (state : DensityOperator S) :
    DensityOperator R where
  matrix := matrix embedding * state.matrix * (matrix embedding).conjTranspose
  positive := state.positive.mul_mul_conjTranspose_same (matrix embedding)
  trace_le_one := by rw [trace_sandwich]; exact state.trace_le_one

/-- Encoding preserves the mass of each subnormalized execution branch. -/
@[simp] public lemma basisEmbedding_density_mass (embedding : S.Index ↪ R.Index)
    (state : DensityOperator S) : (density embedding state).mass = state.mass := by
  exact congrArg Complex.re (trace_sandwich embedding state.matrix)

/-- Each encoded pair retains precisely its original matrix entry. -/
public lemma density_image (embedding : S.Index ↪ R.Index)
    (state : DensityOperator S) (left right : S.Index) :
    (density embedding state).matrix (embedding left) (embedding right) =
      state.matrix left right := by
  classical
  simp [density, matrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    embedding.injective.eq_iff]

/-- A non-image row or column has zero amplitude, including its coherent cross terms. -/
public lemma density_unused (embedding : S.Index ↪ R.Index)
    (state : DensityOperator S) (left right : R.Index)
    (unused : left ∉ Set.range embedding ∨ right ∉ Set.range embedding) :
    (density embedding state).matrix left right = 0 := by
  classical
  rcases unused with unused | unused
  · have different : ∀ source, embedding source ≠ left :=
      fun source same => unused ⟨source, same⟩
    simp [density, matrix, Matrix.mul_apply, different]
  · have different : ∀ source, embedding source ≠ right :=
      fun source same => unused ⟨source, same⟩
    simp [density, matrix, Matrix.mul_apply, Matrix.conjTranspose_apply, different]

/-- Preserve every amplitude under the same basis encoding. -/
public def vector (embedding : S.Index ↪ R.Index) (state : NormalizedVector S) :
    NormalizedVector R :=
  NormalizedVector.ofVector (Effect.extensionVector embedding state.vec) (by
    rw [Effect.norm_extensionVector embedding embedding.injective]
    exact state.norm_eq_one)

/-- The normalized encoding has exactly the source amplitude on its image. -/
public lemma vector_image (embedding : S.Index ↪ R.Index)
    (state : NormalizedVector S) (index : S.Index) :
    vector embedding state (embedding index) = state index :=
  Effect.extensionVector_image embedding embedding.injective state.vec index

/-- Every unused encoded basis label has zero amplitude. -/
public lemma vector_unused (embedding : S.Index ↪ R.Index)
    (state : NormalizedVector S) (index : R.Index)
    (unused : index ∉ Set.range embedding) :
    vector embedding state index = 0 := by
  classical
  have different : ∀ source, embedding source ≠ index :=
    fun source same => unused ⟨source, same⟩
  change Effect.extensionVector embedding state.vec index = 0
  simp [Effect.extensionVector_apply, different]

/-- The rectangular matrix and the amplitude-wise extension are the same linear map. -/
public lemma matrix_mulVec (embedding : S.Index ↪ R.Index) (state : HilbertVector S) :
    (matrix embedding).mulVec state.ofLp =
      (Effect.extensionVector embedding state).ofLp := by
  classical
  funext row
  simp [Matrix.mulVec, dotProduct, matrix, Effect.extensionVector_apply]

/-- A matrix intertwiner transfers arbitrary coherent vectors, retaining exact phase. -/
public lemma applyVec_extension (embedding : S.Index ↪ R.Index)
    (source : UnitaryOperator S) (target : UnitaryOperator R)
    (intertwines : (target : HilbertOperator R) * matrix embedding =
      matrix embedding * (source : HilbertOperator S)) (state : HilbertVector S) :
    target.applyVec (Effect.extensionVector embedding state) =
      Effect.extensionVector embedding (source.applyVec state) := by
  apply WithLp.ofLp_injective
  change (target : HilbertOperator R).mulVec
      (Effect.extensionVector embedding state).ofLp = _
  rw [← matrix_mulVec, Matrix.mulVec_mulVec, intertwines, ← Matrix.mulVec_mulVec,
    matrix_mulVec]
  rfl

/-- Entrywise encoded columns suffice to establish the complete operator intertwiner. -/
public lemma intertwines_of_columns (embedding : S.Index ↪ R.Index)
    (source : UnitaryOperator S) (target : UnitaryOperator R)
    (columns : ∀ row column, target row (embedding column) =
      ∑ index : S.Index, if embedding index = row then source index column else 0) :
    (target : HilbertOperator R) * matrix embedding =
      matrix embedding * (source : HilbertOperator S) := by
  classical
  ext row column
  simpa [Matrix.mul_apply, matrix] using columns row column

/-- The pure-state and complete mixed-state encodings are the same representation. -/
public lemma density_ofPure (embedding : S.Index ↪ R.Index)
    (state : NormalizedVector S) :
    density embedding (DensityOperator.ofPure state) =
      DensityOperator.ofPure (vector embedding state) := by
  classical
  apply DensityOperator.ext
  ext left right
  by_cases leftImage : left ∈ Set.range embedding
  · obtain ⟨sourceLeft, rfl⟩ := leftImage
    by_cases rightImage : right ∈ Set.range embedding
    · obtain ⟨sourceRight, rfl⟩ := rightImage
      rw [density_image, DensityOperator.ofPure_matrix,
        DensityOperator.ofPure_matrix, vector_image, vector_image]
    · rw [density_unused embedding _ _ _ (Or.inr rightImage),
        DensityOperator.ofPure_matrix, vector_unused embedding _ _ rightImage]
      simp
  · rw [density_unused embedding _ _ _ (Or.inl leftImage),
      DensityOperator.ofPure_matrix, vector_unused embedding _ _ leftImage]
    simp

/-- A proved operator intertwiner transfers complete mixed evolution, without a purity premise. -/
public lemma density_applyUnitary (embedding : S.Index ↪ R.Index)
    (source : UnitaryOperator S) (target : UnitaryOperator R)
    (intertwines : (target : HilbertOperator R) * matrix embedding =
      matrix embedding * (source : HilbertOperator S)) (state : DensityOperator S) :
    DensityOperator.applyUnitary target (density embedding state) =
      density embedding (DensityOperator.applyUnitary source state) := by
  have adjoints :
      (matrix embedding).conjTranspose * (target : HilbertOperator R).conjTranspose =
        (source : HilbertOperator S).conjTranspose * (matrix embedding).conjTranspose := by
    simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose intertwines
  apply DensityOperator.ext
  change (target : HilbertOperator R) *
      (matrix embedding * state.matrix * (matrix embedding).conjTranspose) *
        (target : HilbertOperator R).conjTranspose =
    matrix embedding *
      ((source : HilbertOperator S) * state.matrix * (source : HilbertOperator S).conjTranspose) *
        (matrix embedding).conjTranspose
  calc
    _ = ((target : HilbertOperator R) * matrix embedding) * state.matrix *
        ((matrix embedding).conjTranspose * (target : HilbertOperator R).conjTranspose) := by
      simp only [Matrix.mul_assoc]
    _ = (matrix embedding * (source : HilbertOperator S)) * state.matrix *
        ((source : HilbertOperator S).conjTranspose * (matrix embedding).conjTranspose) := by
      rw [intertwines, adjoints]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- Leave an arbitrary reference coordinate untouched by the physical encoding. -/
public def withReference (embedding : S.Index ↪ R.Index) (Reference : Register) :
    (Register.prod S Reference).Index ↪ (Register.prod R Reference).Index where
  toFun value := (embedding value.1, value.2)
  inj' := by
    intro left right same
    exact Prod.ext
      (embedding.injective
        (congrArg (fun value : (Register.prod R Reference).Index => value.1) same))
      (congrArg (fun value : (Register.prod R Reference).Index => value.2) same)

private lemma reference_matrix (embedding : S.Index ↪ R.Index) (Reference : Register) :
    matrix (withReference embedding Reference) =
      matrix embedding ⊗ₖ (1 : HilbertOperator Reference) := by
  classical
  funext row column
  have equal : withReference embedding Reference column = row ↔
      embedding column.1 = row.1 ∧ column.2 = row.2 := by
    constructor
    · intro same
      exact ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩
    · rintro ⟨first, second⟩
      exact Prod.ext first second
  change (if withReference embedding Reference column = row then (1 : ℂ) else 0) =
    (if embedding column.1 = row.1 then 1 else 0) *
      (1 : HilbertOperator Reference) row.2 column.2
  simp only [equal, Matrix.one_apply]
  by_cases first : embedding column.1 = row.1 <;>
    by_cases second : row.2 = column.2 <;> simp [first, second, eq_comm]

private lemma reference_operator (operator : UnitaryOperator R) (Reference : Register) :
    (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference) :
        HilbertOperator (Register.prod R Reference)) =
      (operator : HilbertOperator R) ⊗ₖ (1 : HilbertOperator Reference) := by
  funext row column
  exact UnitaryOperator.unitaryOperator_prodTensor_apply operator 1 row column

/-- Every source-reference matrix entry, including entangled coherences, is retained. -/
public lemma density_reference_entry (embedding : S.Index ↪ R.Index)
    (Reference : Register) (state : DensityOperator (Register.prod S Reference))
    (left right : S.Index) (leftRef rightRef : Reference.Index) :
    (density (withReference embedding Reference) state).matrix
      (embedding left, leftRef) (embedding right, rightRef) =
      state.matrix (left, leftRef) (right, rightRef) :=
  density_image (withReference embedding Reference) state (left, leftRef) (right, rightRef)

/-- Exact compatibility of basis permutations extends to their full coherent operators. -/
public lemma permutation_intertwines (embedding : S.Index ↪ R.Index)
    (source : Equiv.Perm S.Index) (target : Equiv.Perm R.Index)
    (compatible : ∀ basis, target (embedding basis) = embedding (source basis)) :
    (UnitaryOperator.ofPerm target.symm : HilbertOperator R) * matrix embedding =
      matrix embedding * (UnitaryOperator.ofPerm source.symm : HilbertOperator S) := by
  classical
  ext row column
  simp [Matrix.mul_apply, matrix, UnitaryOperator.ofPerm_entry,
    Equiv.eq_symm_apply, compatible, eq_comm]

/-- Tensoring with an arbitrary untouched reference preserves the proved intertwiner. -/
public lemma reference_intertwines (embedding : S.Index ↪ R.Index)
    (source : UnitaryOperator S) (target : UnitaryOperator R)
    (intertwines : (target : HilbertOperator R) * matrix embedding =
      matrix embedding * (source : HilbertOperator S)) (Reference : Register) :
    (UnitaryOperator.prodTensor target (1 : UnitaryOperator Reference) :
        HilbertOperator (Register.prod R Reference)) *
      matrix (withReference embedding Reference) =
    matrix (withReference embedding Reference) *
      (UnitaryOperator.prodTensor source (1 : UnitaryOperator Reference) :
        HilbertOperator (Register.prod S Reference)) := by
  classical
  rw [reference_matrix (R := R) (S := S) embedding Reference,
    reference_operator (R := R) target Reference, reference_operator (R := S) source Reference,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, intertwines]

/-- A complete mixed source/reference block evolves compatibly with its binary representation. -/
public lemma density_applyUnitary_reference (embedding : S.Index ↪ R.Index)
    (source : UnitaryOperator S) (target : UnitaryOperator R)
    (intertwines : (target : HilbertOperator R) * matrix embedding =
      matrix embedding * (source : HilbertOperator S)) (Reference : Register)
    (state : DensityOperator (Register.prod S Reference)) :
    DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor target (1 : UnitaryOperator Reference))
      (density (withReference embedding Reference) state) =
    density (withReference embedding Reference)
      (DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor source (1 : UnitaryOperator Reference)) state) :=
  density_applyUnitary (withReference embedding Reference) _ _
    (reference_intertwines embedding source target intertwines Reference) state

end

end QuantumAlg.BasisEmbedding
