/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Layout.Quantum.Append
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Execution.Reindex
import Mathlib.Analysis.Matrix.Order

/-!
# Preparing fresh physical systems beside an existing joint state

The internal preparation step appends disjoint physical wires in a prescribed
pure state. The existing register remains an arbitrary mixed state, retaining
all its internal correlations. Classical blocks retain their original labels.
Preparation events and live storage are supplied by the instruction syntax.

The matrix is the tensor product with the pure-state outer product
[dW19, qcnotes.tex:5381], using the tensor rule [dW19, qcnotes.tex:8071] and
reindexing by the actual appended wire coordinates. Summing the fresh coordinates
recovers the complete old matrix [dW19, qcnotes.tex:6827], without any separability
assumption inside it.
-/

section

namespace QuantumAlg.Execution

open scoped ComplexOrder Kronecker

noncomputable section

variable {leftCount rightCount : Nat}

private theorem appendedMatrix_trace (left : QuantumLayout leftCount)
    (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (matrix : Matrix (left.Basis × right.Basis) (left.Basis × right.Basis) ℂ) :
    (matrix.submatrix (QuantumLayout.appendBasisEquiv left right disjoint)
      (QuantumLayout.appendBasisEquiv left right disjoint)).trace = matrix.trace :=
  (QuantumLayout.appendBasisEquiv left right disjoint).sum_comp
    (fun basis : left.Basis × right.Basis => matrix basis basis)

private theorem pureProduct_trace {R S : Register}
    (state : DensityOperator R) (prepared : NormalizedVector S) :
    (state.matrix ⊗ₖ (DensityOperator.ofPure prepared).matrix).trace = state.matrix.trace := by
  have normalized : (DensityOperator.ofPure prepared).matrix.trace = 1 :=
    DensityOperator.trace_pureMatrix prepared
  rw [Matrix.trace_kronecker, normalized, mul_one]

/-- Append newly prepared physical systems to the complete previous density operator. -/
def appendPure (left : QuantumLayout leftCount) (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (state : DensityOperator left.register) (prepared : NormalizedVector right.register) :
    DensityOperator (QuantumLayout.append left right disjoint).register where
  matrix := (state.matrix ⊗ₖ (DensityOperator.ofPure prepared).matrix).submatrix
    (QuantumLayout.appendBasisEquiv left right disjoint)
    (QuantumLayout.appendBasisEquiv left right disjoint)
  positive := (state.positive.kronecker (DensityOperator.ofPure prepared).positive).submatrix
    (QuantumLayout.appendBasisEquiv left right disjoint)
  trace_le_one := by
    exact (congrArg Complex.re
      ((appendedMatrix_trace left right disjoint _).trans
        (pureProduct_trace state prepared))).le.trans state.trace_le_one

/-- Every joint entry uses the exact left and right basis coordinates. -/
theorem appendPure_entry (left : QuantumLayout leftCount) (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (state : DensityOperator left.register) (prepared : NormalizedVector right.register)
    (row column : (QuantumLayout.append left right disjoint).Basis) :
    (appendPure left right disjoint state prepared).matrix row column =
      state.matrix (QuantumLayout.appendBasisEquiv left right disjoint row).1
        (QuantumLayout.appendBasisEquiv left right disjoint column).1 *
          (prepared.vec (QuantumLayout.appendBasisEquiv left right disjoint row).2 *
            star (prepared.vec
              (QuantumLayout.appendBasisEquiv left right disjoint column).2)) := rfl

/-- Preparation preserves the probability mass of the complete old branch. -/
theorem appendPure_mass (left : QuantumLayout leftCount) (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (state : DensityOperator left.register) (prepared : NormalizedVector right.register) :
    (appendPure left right disjoint state prepared).mass = state.mass := by
  exact congrArg Complex.re
    ((appendedMatrix_trace left right disjoint _).trans (pureProduct_trace state prepared))

/-- Reassembled basis labels give the tensor product entry on the actual layout. -/
theorem appendPure_joined_entry (left : QuantumLayout leftCount)
    (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (state : DensityOperator left.register) (prepared : NormalizedVector right.register)
    (oldRow oldColumn : left.Basis) (newRow newColumn : right.Basis) :
    (appendPure left right disjoint state prepared).matrix
      (QuantumLayout.appendJoinBasis left right disjoint oldRow newRow)
      (QuantumLayout.appendJoinBasis left right disjoint oldColumn newColumn) =
        state.matrix oldRow oldColumn * (prepared.vec newRow * star (prepared.vec newColumn)) := by
  refine (appendPure_entry left right disjoint state prepared _ _).trans ?_
  simp only [QuantumLayout.appendBasisEquiv_join]

/-- Summing the prepared coordinates preserves every old matrix entry,
including coherences between any systems already present in the old layout. -/
theorem appendPure_old_marginal (left : QuantumLayout leftCount)
    (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (state : DensityOperator left.register) (prepared : NormalizedVector right.register)
    (oldRow oldColumn : left.Basis) :
    ∑ basis : right.Basis, (appendPure left right disjoint state prepared).matrix
      (QuantumLayout.appendJoinBasis left right disjoint oldRow basis)
      (QuantumLayout.appendJoinBasis left right disjoint oldColumn basis) =
        state.matrix oldRow oldColumn := by
  have normalized :
      (∑ basis : right.Basis, prepared.vec basis * star (prepared.vec basis)) = (1 : ℂ) :=
    DensityOperator.trace_pureMatrix (R := right.register) prepared
  simp only [appendPure_joined_entry]
  rw [← Finset.mul_sum, normalized, mul_one]

private def prependedBasisEquiv (left : QuantumLayout leftCount)
    (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities) :
    (QuantumLayout.append left right disjoint).Basis ≃
      (QuantumLayout.append right left disjoint.symm).Basis :=
  (QuantumLayout.appendBasisEquiv left right disjoint).trans
    ((Equiv.prodComm left.Basis right.Basis).trans
      (QuantumLayout.appendBasisEquiv right left disjoint.symm).symm)

private theorem prependedBasisEquiv_symm_join (left : QuantumLayout leftCount)
    (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (oldBasis : left.Basis) (newBasis : right.Basis) :
    (prependedBasisEquiv left right disjoint).symm
      (QuantumLayout.appendJoinBasis right left disjoint.symm newBasis oldBasis) =
        QuantumLayout.appendJoinBasis left right disjoint oldBasis newBasis := by
  change (QuantumLayout.appendBasisEquiv left right disjoint).symm
    ((QuantumLayout.appendBasisEquiv right left disjoint.symm
      (QuantumLayout.appendJoinBasis right left disjoint.symm newBasis oldBasis)).swap) = _
  rw [QuantumLayout.appendBasisEquiv_join]
  rfl

/-- Prepare the fresh systems at the head of the physical layout, retaining
the old state on the same old physical identities. -/
def prependPure (left : QuantumLayout leftCount) (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (state : DensityOperator left.register) (prepared : NormalizedVector right.register) :
    DensityOperator (QuantumLayout.append right left disjoint.symm).register :=
  DensityOperator.reindex
    (S := (QuantumLayout.append right left disjoint.symm).register)
    (appendPure left right disjoint state prepared) (prependedBasisEquiv left right disjoint)

private theorem prependPure_joined_eq_append (left : QuantumLayout leftCount)
    (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (state : DensityOperator left.register) (prepared : NormalizedVector right.register)
    (oldRow oldColumn : left.Basis) (newRow newColumn : right.Basis) :
    (prependPure left right disjoint state prepared).matrix
      (QuantumLayout.appendJoinBasis right left disjoint.symm newRow oldRow)
      (QuantumLayout.appendJoinBasis right left disjoint.symm newColumn oldColumn) =
        (appendPure left right disjoint state prepared).matrix
          (QuantumLayout.appendJoinBasis left right disjoint oldRow newRow)
          (QuantumLayout.appendJoinBasis left right disjoint oldColumn newColumn) := by
  refine (DensityOperator.reindex_entry
    (S := (QuantumLayout.append right left disjoint.symm).register)
    (appendPure left right disjoint state prepared)
    (prependedBasisEquiv left right disjoint) _ _).trans ?_
  exact congrArg₂
    (fun row column : (QuantumLayout.append left right disjoint).Basis =>
      (appendPure left right disjoint state prepared).matrix row column)
    (prependedBasisEquiv_symm_join left right disjoint oldRow newRow)
    (prependedBasisEquiv_symm_join left right disjoint oldColumn newColumn)

/-- Head preparation has the same exact tensor entry on the named physical systems. -/
theorem prependPure_joined_entry (left : QuantumLayout leftCount)
    (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (state : DensityOperator left.register) (prepared : NormalizedVector right.register)
    (oldRow oldColumn : left.Basis) (newRow newColumn : right.Basis) :
    (prependPure left right disjoint state prepared).matrix
      (QuantumLayout.appendJoinBasis right left disjoint.symm newRow oldRow)
      (QuantumLayout.appendJoinBasis right left disjoint.symm newColumn oldColumn) =
        state.matrix oldRow oldColumn * (prepared.vec newRow * star (prepared.vec newColumn)) :=
  (prependPure_joined_eq_append left right disjoint state prepared
    oldRow oldColumn newRow newColumn).trans
      (appendPure_joined_entry left right disjoint state prepared oldRow oldColumn newRow newColumn)

/-- Placing the prepared systems at the head preserves the old branch mass. -/
theorem prependPure_mass (left : QuantumLayout leftCount) (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (state : DensityOperator left.register) (prepared : NormalizedVector right.register) :
    (prependPure left right disjoint state prepared).mass = state.mass :=
  (DensityOperator.reindex_mass
    (S := (QuantumLayout.append right left disjoint.symm).register)
    (appendPure left right disjoint state prepared)
    (prependedBasisEquiv left right disjoint)).trans
      (appendPure_mass left right disjoint state prepared)

/-- Summing the fresh head coordinates recovers the complete old joint marginal. -/
theorem prependPure_old_marginal (left : QuantumLayout leftCount)
    (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (state : DensityOperator left.register) (prepared : NormalizedVector right.register)
    (oldRow oldColumn : left.Basis) :
    ∑ basis : right.Basis, (prependPure left right disjoint state prepared).matrix
      (QuantumLayout.appendJoinBasis right left disjoint.symm basis oldRow)
      (QuantumLayout.appendJoinBasis right left disjoint.symm basis oldColumn) =
        state.matrix oldRow oldColumn := by
  simp only [prependPure_joined_eq_append]
  exact appendPure_old_marginal left right disjoint state prepared oldRow oldColumn

variable {Classical : Type} [Fintype Classical] {left : QuantumLayout leftCount}

/-- Internal interpretation of preparing disjoint fresh physical systems.
Every existing classical block and its quantum correlations remain present. -/
def prepare (state : ExecutionState Classical left.register)
    (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (prepared : NormalizedVector right.register) :
    ExecutionState Classical (QuantumLayout.append left right disjoint).register where
  block value := appendPure left right disjoint (state.block value) prepared
  total_le_one := by
    simp only [appendPure_mass]
    exact state.total_le_one

/-- Preparation preserves each existing classical branch's probability. -/
theorem prepare_block_mass (state : ExecutionState Classical left.register)
    (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (prepared : NormalizedVector right.register) (value : Classical) :
    ((prepare state right disjoint prepared).block value).mass = (state.block value).mass :=
  appendPure_mass left right disjoint (state.block value) prepared

/-- The complete execution mass is unchanged by preparing fresh systems. -/
theorem prepare_mass (state : ExecutionState Classical left.register)
    (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (prepared : NormalizedVector right.register) :
    (prepare state right disjoint prepared).mass = state.mass := by
  simp only [ExecutionState.mass, prepare_block_mass]

/-- The old marginal is preserved separately in every classical block, so
preparation also retains all prior classical and quantum correlations. -/
theorem prepare_old_block_marginal (state : ExecutionState Classical left.register)
    (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (prepared : NormalizedVector right.register) (value : Classical)
    (oldRow oldColumn : left.Basis) :
    ∑ basis : right.Basis, ((prepare state right disjoint prepared).block value).matrix
      (QuantumLayout.appendJoinBasis left right disjoint oldRow basis)
      (QuantumLayout.appendJoinBasis left right disjoint oldColumn basis) =
        (state.block value).matrix oldRow oldColumn :=
  appendPure_old_marginal left right disjoint (state.block value) prepared oldRow oldColumn

/-- Prepare fresh physical systems at the head, as used when adding an owned layout. -/
def prepareHead (state : ExecutionState Classical left.register)
    (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (prepared : NormalizedVector right.register) :
    ExecutionState Classical (QuantumLayout.append right left disjoint.symm).register :=
  ExecutionState.reindex
    (S := (QuantumLayout.append right left disjoint.symm).register)
    (prepare state right disjoint prepared) (prependedBasisEquiv left right disjoint)

/-- Each existing classical block uses precisely the head-preparation state update. -/
theorem prepareHead_block (state : ExecutionState Classical left.register)
    (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (prepared : NormalizedVector right.register) (value : Classical) :
    (prepareHead state right disjoint prepared).block value =
      prependPure left right disjoint (state.block value) prepared := rfl

/-- Head preparation preserves the probability of every existing classical value. -/
theorem prepareHead_block_mass (state : ExecutionState Classical left.register)
    (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (prepared : NormalizedVector right.register) (value : Classical) :
    ((prepareHead state right disjoint prepared).block value).mass = (state.block value).mass :=
  prependPure_mass left right disjoint (state.block value) prepared

/-- Head preparation preserves the complete execution probability. -/
theorem prepareHead_mass (state : ExecutionState Classical left.register)
    (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (prepared : NormalizedVector right.register) :
    (prepareHead state right disjoint prepared).mass = state.mass := by
  simp only [ExecutionState.mass, prepareHead_block_mass]

/-- The old marginal and all previous classical and quantum correlations survive
head preparation separately in every classical block. -/
theorem prepareHead_old_block_marginal (state : ExecutionState Classical left.register)
    (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities)
    (prepared : NormalizedVector right.register) (value : Classical)
    (oldRow oldColumn : left.Basis) :
    ∑ basis : right.Basis, ((prepareHead state right disjoint prepared).block value).matrix
      (QuantumLayout.appendJoinBasis right left disjoint.symm basis oldRow)
      (QuantumLayout.appendJoinBasis right left disjoint.symm basis oldColumn) =
        (state.block value).matrix oldRow oldColumn :=
  prependPure_old_marginal left right disjoint (state.block value) prepared oldRow oldColumn

end

end QuantumAlg.Execution

end
