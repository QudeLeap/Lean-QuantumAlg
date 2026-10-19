/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.State.Density.ReferenceBlock
import all QuantumAlg.Core.Execution.Basis.Reference
import all QuantumAlg.Core.Execution.State

/-!
# Pure reference records and basis-seeded density families

Principal reference blocks retain their intrinsic positivity and actual
subnormalized mass. A fixed local basis seed tensors each complete reference
block separately. Finite classical transport sums precisely its colliding
records; recording the source label in history prevents those collisions.

The formulas retain independent left and right reference coordinates, arbitrary
record types and zero-mass records. These are mathematical state constructors
and observations. They contain no Circuit, allocation, reset or readout run.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ReferenceRecords

noncomputable section

open QuantumAlg QuantumAlg.Execution
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Each source record supplies its own positive principal reference block. -/
def referenceSlices {C : Type} [Fintype C] {R Reference : Register}
    (source : ExecutionState C (R.prod Reference)) (label : R.Index) :
    ExecutionState C Reference where
  block record := (source.block record).basisSlice label
  total_le_one := (Finset.sum_le_sum (fun record _ =>
    DensityOperator.basisSlice_mass_le (source.block record) label)).trans source.total_le_one

/-- Both complex reference coordinates of each original record are retained. -/
lemma referenceSlices_entry {C : Type} [Fintype C] {R Reference : Register}
    (source : ExecutionState C (R.prod Reference)) (label : R.Index)
    (record : C) (left right : Reference.Index) :
    ((referenceSlices source label).block record).matrix left right =
      (source.block record).matrix (label, left) (label, right) := rfl

/-- Principal slicing never creates additional total mass. -/
lemma referenceSlices_mass_le {C : Type} [Fintype C] {R Reference : Register}
    (source : ExecutionState C (R.prod Reference)) (label : R.Index) :
    (referenceSlices source label).mass ≤ source.mass :=
  Finset.sum_le_sum (fun record _ =>
    DensityOperator.basisSlice_mass_le (source.block record) label)

/-- A proved local reset factor, record by record, preserves exactly the original total mass. -/
lemma referenceSlices_mass_of_factor {C : Type} [Fintype C] {R Reference : Register}
    (source : ExecutionState C (R.prod Reference)) (label : R.Index)
    (factor : ∀ record : C, ∀ left right : R.Index, ∀ refLeft refRight : Reference.Index,
      (source.block record).matrix (left, refLeft) (right, refRight) =
        NormalizedVector.ket label left *
          (source.block record).matrix (label, refLeft) (label, refRight) *
            star (NormalizedVector.ket label right)) :
    (referenceSlices source label).mass = source.mass := by
  change (∑ record : C, ((source.block record).basisSlice label).mass) =
    ∑ record : C, (source.block record).mass
  apply Finset.sum_congr rfl
  intro record _
  exact DensityOperator.basisSlice_mass_of_factor (source.block record) label (factor record)

/-- Tensor the old local seed with every certified reference coefficient separately. -/
def seededBlocks {C : Type} [Fintype C] (ctx : RuntimeCtx .quantum)
    (seed : ctx.register.Index) {Reference : Register}
    (coefficients : ExecutionState C Reference) :
    ExecutionState C (ctx.register.prod Reference) where
  block record := BasisReference.target seed (coefficients.block record)
  total_le_one := by
    simpa only [BasisReference.target_mass] using coefficients.total_le_one

/-- Each complete record retains every off-diagonal reference entry. -/
lemma seededBlocks_entry {C : Type} [Fintype C] (ctx : RuntimeCtx .quantum)
    (seed : ctx.register.Index) {Reference : Register}
    (coefficients : ExecutionState C Reference) (record : C)
    (left right : ctx.register.Index) (refLeft refRight : Reference.Index) :
    ((seededBlocks ctx seed coefficients).block record).matrix
        (left, refLeft) (right, refRight) =
      if left = seed ∧ right = seed then
        (coefficients.block record).matrix refLeft refRight else 0 :=
  BasisReference.target_entry seed (coefficients.block record) left right refLeft refRight

/-- A fixed basis ket adds no probability mass. -/
lemma seededBlocks_mass {C : Type} [Fintype C] (ctx : RuntimeCtx .quantum)
    (seed : ctx.register.Index) {Reference : Register}
    (coefficients : ExecutionState C Reference) :
    (seededBlocks ctx seed coefficients).mass = coefficients.mass := by
  simp only [ExecutionState.mass, seededBlocks, BasisReference.target_mass]

/-- An impossible reference record remains the zero joint density operator. -/
lemma seededBlocks_zero_record {C : Type} [Fintype C] (ctx : RuntimeCtx .quantum)
    (seed : ctx.register.Index) {Reference : Register}
    (coefficients : ExecutionState C Reference) (record : C)
    (zero : (coefficients.block record).mass = 0) :
    (seededBlocks ctx seed coefficients).block record =
      DensityOperator.zero (ctx.register.prod Reference) :=
  DensityOperator.eq_zero_of_mass_eq_zero _
    ((BasisReference.target_mass seed (coefficients.block record)).trans zero)

/-- Transport complete classical records; collisions use the actual intrinsic finite pushforward. -/
def transportedState {C H : Type} [Fintype C] [Fintype H] (ctx : RuntimeCtx .quantum)
    (seed : ctx.register.Index) {Reference : Register}
    (coefficients : ExecutionState C Reference) (transport : C → Store ctx × H) :
    State ctx Reference H :=
  (seededBlocks ctx seed coefficients).mapClassical transport

/-- Every transported record has exactly the sum of its original reference fibers. -/
lemma transportedState_entry {C H : Type} [Fintype C] [Fintype H]
    (ctx : RuntimeCtx .quantum) (seed : ctx.register.Index) {Reference : Register}
    (coefficients : ExecutionState C Reference) (transport : C → Store ctx × H)
    (record : Store ctx × H) (left right : ctx.register.Index)
    (refLeft refRight : Reference.Index) :
    ((transportedState ctx seed coefficients transport).block record).matrix
        (left, refLeft) (right, refRight) =
      if left = seed ∧ right = seed then
        ∑ original : C, if transport original = record then
          (coefficients.block original).matrix refLeft refRight else 0
      else 0 := by
  change (∑ original : C, if transport original = record then
    ((seededBlocks ctx seed coefficients).block original).matrix else 0)
      (left, refLeft) (right, refRight) = _
  simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply, seededBlocks_entry]
  by_cases supported : left = seed ∧ right = seed
  · simp only [if_pos supported]
  · simp only [if_neg supported, ite_self, Finset.sum_const_zero]

/-- Arbitrary complete-record transport preserves total probability, even at collisions. -/
lemma transportedState_mass {C H : Type} [Fintype C] [Fintype H]
    (ctx : RuntimeCtx .quantum) (seed : ctx.register.Index) {Reference : Register}
    (coefficients : ExecutionState C Reference) (transport : C → Store ctx × H) :
    (transportedState ctx seed coefficients transport).mass = coefficients.mass :=
  (ExecutionState.mapClassical_mass _ _).trans (seededBlocks_mass ctx seed coefficients)

/-- The whole marginal keeps the full reference density and exactly the prescribed local seed. -/
lemma transportedState_marginal_entry {C H : Type} [Fintype C] [Fintype H]
    (ctx : RuntimeCtx .quantum) (seed : ctx.register.Index) {Reference : Register}
    (coefficients : ExecutionState C Reference) (transport : C → Store ctx × H)
    (left right : ctx.register.Index) (refLeft refRight : Reference.Index) :
    (transportedState ctx seed coefficients transport).quantumMarginal.matrix
        (left, refLeft) (right, refRight) =
      if left = seed ∧ right = seed then
        coefficients.quantumMarginal.matrix refLeft refRight else 0 := by
  rw [transportedState, ExecutionState.mapClassical_quantumMarginal]
  change (∑ record : C, ((seededBlocks ctx seed coefficients).block record).matrix)
      (left, refLeft) (right, refRight) = _
  simp only [Matrix.sum_apply, seededBlocks_entry]
  by_cases supported : left = seed ∧ right = seed
  · simp only [if_pos supported]
    simp only [ExecutionState.quantumMarginal, Matrix.sum_apply]
  · simp only [if_neg supported, Finset.sum_const_zero]

/-- The old theorem's exact diagonal support requirement follows without normalization. -/
lemma transportedState_supported {C H : Type} [Fintype C] [Fintype H]
    (ctx : RuntimeCtx .quantum) (seed : ctx.register.Index) {Reference : Register}
    (coefficients : ExecutionState C Reference) (transport : C → Store ctx × H)
    (basis : (ctx.register.prod Reference).Index) (outside : basis.1 ≠ seed) :
    (transportedState ctx seed coefficients transport).quantumMarginal.matrix basis basis = 0 := by
  rcases basis with ⟨left, reference⟩
  exact (transportedState_marginal_entry ctx seed coefficients transport
    left left reference reference).trans (if_neg (fun supported => outside supported.1))

/-- Retaining the whole original record in history prevents any accidental record collision. -/
def recordState {C : Type} [Fintype C] (ctx : RuntimeCtx .quantum)
    (seed : ctx.register.Index) {Reference : Register}
    (coefficients : ExecutionState C Reference) (store : C → Store ctx) :
    State ctx Reference C :=
  transportedState ctx seed coefficients (fun record => (store record, record))

/-- Exact original-record density, including both arbitrary reference coordinates. -/
lemma recordState_entry {C : Type} [Fintype C] (ctx : RuntimeCtx .quantum)
    (seed : ctx.register.Index) {Reference : Register}
    (coefficients : ExecutionState C Reference) (store : C → Store ctx) (record : C)
    (left right : ctx.register.Index) (refLeft refRight : Reference.Index) :
    ((recordState ctx seed coefficients store).block (store record, record)).matrix
        (left, refLeft) (right, refRight) =
      if left = seed ∧ right = seed then
        (coefficients.block record).matrix refLeft refRight else 0 := by
  have same (original : C) :
      (store original, original) = (store record, record) ↔ original = record := by
    constructor
    · intro equal
      exact congrArg (fun value : Store ctx × C => value.2) equal
    · intro equal
      subst original
      rfl
  rw [recordState, transportedState_entry]
  simp only [same, Fintype.sum_ite_eq']

/-- The complete record-preserving state has exactly its coefficient family's mass. -/
lemma recordState_mass {C : Type} [Fintype C] (ctx : RuntimeCtx .quantum)
    (seed : ctx.register.Index) {Reference : Register}
    (coefficients : ExecutionState C Reference) (store : C → Store ctx) :
    (recordState ctx seed coefficients store).mass = coefficients.mass :=
  transportedState_mass ctx seed coefficients (fun record => (store record, record))

end

end ReferenceRecords
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
