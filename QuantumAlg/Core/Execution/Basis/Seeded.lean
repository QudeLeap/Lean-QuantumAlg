/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Classical.Branch
import all QuantumAlg.Core.Execution.Reference.Unitary
import all QuantumAlg.Core.Execution.Measurement.Fibers

/-!
# Basis support in complete actual store-reference blocks

The closed invariant below refers to the actual state's matrix entries.
Every complete classical store has one local basis seed; its reference
coefficient is that same state's seed entry. It retains off-diagonal reference
coordinates and allows zero-mass stores. It is an internal state fact for
preparation and reuse proofs, with no second quantum state or probability
carrier and no implicit storage release.
-/

namespace QuantumAlg.Execution.BasisSeeded

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
  {History : Type} [Fintype History]

/-- Closed support at one local basis label in every complete actual store-reference block. -/
def Holds (seed : ctx.register.Index) (state : State ctx Reference History) : Prop :=
  ∀ (original : Store ctx) (left right : ctx.register.Index) (leftRef rightRef : Reference.Index),
    (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      if left = seed ∧ right = seed then
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          (seed, leftRef) (seed, rightRef)
      else 0

private lemma ket_factor {R : Register} (seed left right : R.Index) (coefficient : ℂ) :
    NormalizedVector.ket (R := R) seed left * coefficient *
        star (NormalizedVector.ket (R := R) seed right) =
      if left = seed ∧ right = seed then coefficient else 0 := by
  by_cases hleft : left = seed <;> by_cases hright : right = seed <;>
    simp [hleft, hright]

/-- A proved actual seed outer-product formula establishes the intrinsic support invariant. -/
lemma of_entries (seed : ctx.register.Index) (state : State ctx Reference History)
    (coefficient : Store ctx → Reference.Index → Reference.Index → ℂ)
    (entries : ∀ (original : Store ctx) (left right : ctx.register.Index)
      (leftRef rightRef : Reference.Index),
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          (left, leftRef) (right, rightRef) =
        NormalizedVector.ket (R := ctx.register) seed left * coefficient original leftRef rightRef *
          star (NormalizedVector.ket (R := ctx.register) seed right)) : Holds seed state := by
  intro original left right leftRef rightRef
  have atSeed := entries original seed seed leftRef rightRef
  have seedFactor := ket_factor seed seed seed (coefficient original leftRef rightRef)
  have seedValue :
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          (seed, leftRef) (seed, rightRef) = coefficient original leftRef rightRef :=
    atSeed.trans (seedFactor.trans (if_pos ⟨rfl, rfl⟩))
  exact (entries original left right leftRef rightRef).trans
    ((ket_factor seed left right (coefficient original leftRef rightRef)).trans
      (congrArg (fun value : ℂ => if left = seed ∧ right = seed then value else 0)
        seedValue.symm))

/-- The seed entry is the entire actual reference block after summing the local register. -/
lemma reference_entry (seed : ctx.register.Index) (state : State ctx Reference History)
    (seeded : Holds seed state) (original : Store ctx) (leftRef rightRef : Reference.Index) :
    (∑ basis : ctx.register.Index,
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        (basis, leftRef) (basis, rightRef)) =
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        (seed, leftRef) (seed, rightRef) := by
  have entries :
      (∑ basis : ctx.register.Index,
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          (basis, leftRef) (basis, rightRef)) =
      ∑ basis : ctx.register.Index, if basis = seed then
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          (seed, leftRef) (seed, rightRef) else 0 := by
    apply Finset.sum_congr rfl
    intro basis _
    simpa only [and_self] using seeded original basis basis leftRef rightRef
  exact entries.trans (by
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true])

/-- A local unitary acts on the actual seed column and preserves the complete reference entry. -/
lemma unitary_entry (seed : ctx.register.Index) (state : State ctx Reference History)
    (seeded : Holds seed state) (operator : UnitaryOperator ctx.register) (original : Store ctx)
    (left right : ctx.register.Index) (leftRef rightRef : Reference.Index) :
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference))
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal).matrix
        (left, leftRef) (right, rightRef) =
      operator left seed *
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          (seed, leftRef) (seed, rightRef) * star (operator right seed) := by
  have atSeed : ∀ row column,
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          (row, leftRef) (column, rightRef) =
        if row = seed ∧ column = seed then
          (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
            (seed, leftRef) (seed, rightRef) else 0 :=
    fun row column => seeded original row column leftRef rightRef
  generalize
    (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
      (seed, leftRef) (seed, rightRef) = coefficient at atSeed ⊢
  rw [DensityOperator.localUnitary_block]
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, atSeed,
    ite_and, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- Forgetting history groups precisely the actual density blocks of each complete store. -/
lemma store_matrix (state : State ctx Reference History) (original : Store ctx) :
    ((state.mapClassical (fun entry => entry.1)).block original).matrix =
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix := by
  change (∑ entry : Store ctx × History,
    if entry.1 = original then (state.block entry).matrix else 0) =
      ∑ entry : Store ctx × History,
        ((state.filterClassical (fun entry => entry.1 = original)).block entry).matrix
  apply Finset.sum_congr rfl
  intro entry _
  by_cases same : entry.1 = original <;>
    simp only [ExecutionState.filterClassical_block, same, if_true, if_false,
      DensityOperator.zero_matrix]

/-- Reference observations can sum complete actual store blocks before summing local labels. -/
lemma fiber_store_blocks (state : State ctx Reference History)
    (weight : Store ctx → ctx.register.Index → ℂ) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum state (fun entry basis => weight entry.1 basis)
        leftRef rightRef =
      ∑ basis : ctx.register.Index, ∑ original : Store ctx, weight original basis *
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          (basis, leftRef) (basis, rightRef) := by
  have observed := ExecutionState.referenceFiberSum_mapClassical
    (R := ctx.register) (Reference := Reference) (decision := inferInstance) state
    (fun entry => entry.1) weight leftRef rightRef
  refine observed.symm.trans ?_
  unfold ExecutionState.referenceFiberSum
  apply Finset.sum_congr rfl
  intro basis _
  apply Finset.sum_congr rfl
  intro original _
  exact congrArg
    (fun matrix : HilbertOperator (Register.prod ctx.register Reference) =>
      weight original basis * matrix (basis, leftRef) (basis, rightRef))
    (store_matrix state original)

private lemma readout_matrix {Outcome : Type} [Fintype Outcome] [DecidableEq Outcome]
    (state : State ctx Reference History) (read : Store ctx → Outcome) (outcome : Outcome) :
    ((state.mapClassical (fun entry => read entry.1)).block outcome).matrix =
      ∑ original : Store ctx, if read original = outcome then
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        else 0 := by
  have composed := congrArg
    (fun result : ExecutionState Outcome (Register.prod ctx.register Reference) =>
      (result.block outcome).matrix)
    (ExecutionState.executionState_mapClassical_comp state (fun entry => entry.1) read)
  refine composed.symm.trans ?_
  change (∑ original : Store ctx, if read original = outcome then
    ((state.mapClassical (fun entry => entry.1)).block original).matrix else 0) = _
  exact Finset.sum_congr rfl fun original _ =>
    congrArg (fun matrix : HilbertOperator (Register.prod ctx.register Reference) =>
      if read original = outcome then matrix else 0) (store_matrix state original)

/-- A read of actual storage retains the seed outer product
and that result's complete reference fiber. -/
lemma readout_entry {Outcome : Type} [Fintype Outcome] [DecidableEq Outcome]
    (seed : ctx.register.Index) (state : State ctx Reference History) (seeded : Holds seed state)
    (read : Store ctx → Outcome) (outcome : Outcome)
    (left right : ctx.register.Index) (leftRef rightRef : Reference.Index) :
    ((state.mapClassical (fun entry => read entry.1)).block outcome).matrix
        (left, leftRef) (right, rightRef) =
      if left = seed ∧ right = seed then
        ExecutionState.referenceFiberSum state
          (fun entry _ => if read entry.1 = outcome then 1 else 0) leftRef rightRef
      else 0 := by
  have fiber : ExecutionState.referenceFiberSum state
      (fun entry _ => if read entry.1 = outcome then 1 else 0) leftRef rightRef =
      ∑ original : Store ctx, if read original = outcome then
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          (seed, leftRef) (seed, rightRef) else 0 := by
    refine (fiber_store_blocks state
      (fun original _ => if read original = outcome then 1 else 0) leftRef rightRef).trans ?_
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro original _
    rw [← Finset.mul_sum, reference_entry seed state seeded]
    by_cases same : read original = outcome <;>
      simp only [same, if_true, if_false, one_mul, zero_mul]
  have actual := congrArg
    (fun matrix : HilbertOperator (Register.prod ctx.register Reference) =>
      matrix (left, leftRef) (right, rightRef)) (readout_matrix state read outcome)
  refine actual.trans ?_
  simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply]
  have entries : ∀ original : Store ctx,
      (if read original = outcome then
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          (left, leftRef) (right, rightRef) else 0) =
      if left = seed ∧ right = seed then
        (if read original = outcome then
          (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
            (seed, leftRef) (seed, rightRef) else 0) else 0 := by
    intro original
    rw [seeded original left right leftRef rightRef]
    by_cases observed : read original = outcome
    · simp only [if_pos observed]
    · simp only [if_neg observed, ite_self]
  simp only [entries]
  by_cases supported : left = seed ∧ right = seed
  · simp only [supported]
    exact fiber.symm
  · simp only [supported, if_false, Finset.sum_const_zero]

end

end QuantumAlg.Execution.BasisSeeded
