/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Algorithm.ExecutionState
import Mathlib.Analysis.Matrix.Order

/-!
# Context preparation with an arbitrary external reference

Preparation tensors a fresh pure register with the entire old context and its
external reference. That old joint state may be mixed or entangled. Exact
layout equivalences then identify the result with the extended context tensor
the same reference, whose basis coordinate is unchanged.

The pure-state outer product and tensor rule are [dW19, qcnotes.tex:5381] and
[dW19, qcnotes.tex:8071]. Summing the fresh coordinates recovers every old joint
matrix entry [dW19, qcnotes.tex:6827]. The reference is a mathematical register;
it is never inserted into the physical context or its storage accounting.
-/

section

namespace QuantumAlg.Execution

open scoped ComplexOrder Kronecker

noncomputable section

private lemma prependedProduct_trace {R S : Register}
    (state : DensityOperator R) (prepared : NormalizedVector S) :
    ((DensityOperator.ofPure prepared).matrix ⊗ₖ state.matrix).trace = state.matrix.trace := by
  have normalized : (DensityOperator.ofPure prepared).matrix.trace = 1 :=
    DensityOperator.trace_pureMatrix prepared
  rw [Matrix.trace_kronecker, normalized, one_mul]

private def prependPrepared {R S : Register}
    (state : DensityOperator R) (prepared : NormalizedVector S) :
    DensityOperator (Register.prod S R) where
  matrix := (DensityOperator.ofPure prepared).matrix ⊗ₖ state.matrix
  positive := (DensityOperator.ofPure prepared).positive.kronecker state.positive
  trace_le_one :=
    (congrArg Complex.re (prependedProduct_trace state prepared)).le.trans state.trace_le_one

private lemma prependPrepared_mass {R S : Register}
    (state : DensityOperator R) (prepared : NormalizedVector S) :
    (prependPrepared state prepared).mass = state.mass :=
  congrArg Complex.re (prependedProduct_trace state prepared)

variable {systemCount : Nat}

/-- Reassociate fresh, old-context, and reference labels, using the actual
context-layout correspondence and the identity map on the reference. -/
def prepareContextBasisEquiv (ctx : RuntimeCtx .quantum) (Reference : Register)
    (key : StorageKey) (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    (Register.prod layout.register (Register.prod ctx.register Reference)).Index ≃
      (Register.prod (ctx.addOwnedLayout key layout fresh disjoint).register Reference).Index :=
  (Equiv.prodAssoc layout.register.Index ctx.register.Index Reference.Index).symm.trans
    (((QuantumLayout.appendBasisEquiv layout ctx.quantumLayout
      (ctx.addOwnedLayout_layoutDisjoint layout disjoint)).symm.trans
        (ctx.addOwnedLayoutBasisEquiv key layout fresh disjoint)).prodCongr
          (Equiv.refl Reference.Index))

/-- The reference coordinate is unchanged by the complete physical allocation bridge. -/
lemma prepareContextBasisEquiv_reference (ctx : RuntimeCtx .quantum) (Reference : Register)
    (key : StorageKey) (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (newBasis : layout.register.Index) (oldBasis : ctx.register.Index)
    (referenceBasis : Reference.Index) :
    (prepareContextBasisEquiv ctx Reference key layout fresh disjoint
      (newBasis, (oldBasis, referenceBasis))).2 = referenceBasis := rfl

/-- The context coordinate uses the exact newly prepended and old physical wire labels. -/
lemma prepareContextBasisEquiv_context (ctx : RuntimeCtx .quantum) (Reference : Register)
    (key : StorageKey) (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (newBasis : layout.register.Index) (oldBasis : ctx.register.Index)
    (referenceBasis : Reference.Index) :
    (prepareContextBasisEquiv ctx Reference key layout fresh disjoint
      (newBasis, (oldBasis, referenceBasis))).1 =
        ctx.addOwnedLayoutBasisEquiv key layout fresh disjoint
          (QuantumLayout.appendJoinBasis layout ctx.quantumLayout
            (ctx.addOwnedLayout_layoutDisjoint layout disjoint) newBasis oldBasis) := rfl

variable {C : Type} [Fintype C] {ctx : RuntimeCtx .quantum} {Reference : Register}

/-- Prepare fresh physical systems beside the complete old context-reference state.
The unchanged classical labels are subsequently updated by the instruction's storage step. -/
def prepareContext (state : ExecutionState C (Register.prod ctx.register Reference))
    (key : StorageKey) (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (prepared : NormalizedVector layout.register) :
    ExecutionState C
      (Register.prod (ctx.addOwnedLayout key layout fresh disjoint).register Reference) where
  block value := DensityOperator.reindex
    (S := Register.prod (ctx.addOwnedLayout key layout fresh disjoint).register Reference)
    (prependPrepared (state.block value) prepared)
    (prepareContextBasisEquiv ctx Reference key layout fresh disjoint)
  total_le_one := by
    simp only [DensityOperator.reindex_mass, prependPrepared_mass]
    exact state.total_le_one

/-- Physical preparation preserves each old classical branch's probability. -/
lemma prepareContext_block_mass
    (state : ExecutionState C (Register.prod ctx.register Reference))
    (key : StorageKey) (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (prepared : NormalizedVector layout.register) (value : C) :
    ((prepareContext state key layout fresh disjoint prepared).block value).mass =
      (state.block value).mass :=
  (DensityOperator.reindex_mass
    (S := Register.prod (ctx.addOwnedLayout key layout fresh disjoint).register Reference)
    (prependPrepared (state.block value) prepared)
    (prepareContextBasisEquiv ctx Reference key layout fresh disjoint)).trans
      (prependPrepared_mass (state.block value) prepared)

/-- Physical preparation preserves the complete execution mass for any reference. -/
lemma prepareContext_mass (state : ExecutionState C (Register.prod ctx.register Reference))
    (key : StorageKey) (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (prepared : NormalizedVector layout.register) :
    (prepareContext state key layout fresh disjoint prepared).mass = state.mass := by
  simp only [ExecutionState.mass, prepareContext_block_mass]

/-- Exact joint entries retain all old context-reference coherences in each classical block. -/
lemma prepareContext_joined_entry
    (state : ExecutionState C (Register.prod ctx.register Reference))
    (key : StorageKey) (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (prepared : NormalizedVector layout.register) (value : C)
    (newRow newColumn : layout.register.Index)
    (oldRow oldColumn : (Register.prod ctx.register Reference).Index) :
    ((prepareContext state key layout fresh disjoint prepared).block value).matrix
      (prepareContextBasisEquiv ctx Reference key layout fresh disjoint (newRow, oldRow))
      (prepareContextBasisEquiv ctx Reference key layout fresh disjoint (newColumn, oldColumn)) =
        (prepared.vec newRow * star (prepared.vec newColumn)) *
          (state.block value).matrix oldRow oldColumn := by
  refine (DensityOperator.reindex_entry
    (S := Register.prod (ctx.addOwnedLayout key layout fresh disjoint).register Reference)
    (prependPrepared (state.block value) prepared)
    (prepareContextBasisEquiv ctx Reference key layout fresh disjoint) _ _).trans ?_
  exact (congrArg₂
    (fun row column : (Register.prod layout.register
        (Register.prod ctx.register Reference)).Index =>
      (prependPrepared (state.block value) prepared).matrix row column)
    ((prepareContextBasisEquiv ctx Reference key layout fresh disjoint).symm_apply_apply
      (newRow, oldRow))
    ((prepareContextBasisEquiv ctx Reference key layout fresh disjoint).symm_apply_apply
      (newColumn, oldColumn))).trans rfl

/-- Summing only the newly prepared labels recovers every matrix entry of the
entire old context and external reference, separately in each classical block. -/
lemma prepareContext_old_block_marginal
    (state : ExecutionState C (Register.prod ctx.register Reference))
    (key : StorageKey) (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (prepared : NormalizedVector layout.register) (value : C)
    (oldRow oldColumn : (Register.prod ctx.register Reference).Index) :
    ∑ newBasis : layout.register.Index,
      ((prepareContext state key layout fresh disjoint prepared).block value).matrix
        (prepareContextBasisEquiv ctx Reference key layout fresh disjoint (newBasis, oldRow))
        (prepareContextBasisEquiv ctx Reference key layout fresh disjoint (newBasis, oldColumn)) =
          (state.block value).matrix oldRow oldColumn := by
  have normalized :
      (∑ basis : layout.register.Index, prepared.vec basis * star (prepared.vec basis)) = (1 : ℂ) :=
    DensityOperator.trace_pureMatrix (R := layout.register) prepared
  simp only [prepareContext_joined_entry]
  rw [← Finset.sum_mul, normalized, one_mul]

end

end QuantumAlg.Execution

end
