/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Teleportation.Parallel.Execution
import all QuantumAlg.Algorithms.Teleportation.Parallel.Store
import all QuantumAlg.Algorithms.Teleportation.Parallel.Construction
import all QuantumAlg.Algorithms.Teleportation.Parallel.Geometry
import all QuantumAlg.Core.Execution.Measurement.Matrix
import all QuantumAlg.Core.Execution.QubitReadouts
import all QuantumAlg.Core.Execution.Unitary.Local
import all QuantumAlg.Core.Execution.Reference.Unitary
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Full stored branches of the actual teleportation instrument

The actual native Alice word, projective writes and store-selected Bob
correction define one complete instrument [dW19, qcnotes.tex:790,802,804].
Every initial result cell is overwritten, so each final-store branch depends
on the original complete quantum marginal even when those cells were
correlated with the quantum input. Both external-reference coordinates remain
arbitrary, and all Alice and Bob systems remain live. These equations need no
Bell initialization, normalization, independence or admission hypothesis.
-/

namespace QuantumAlg.QuantumTeleportation.Parallel.StoreInstrument

noncomputable section

open Execution
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- A constant block weight sums the original complete quantum marginal. -/
lemma weightedMatrixEntry_const {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (weight : ℂ) (left right : R.Index) :
    ExecutionState.weightedMatrixEntry state (fun _ => weight) left right =
      weight * state.quantumMarginal.matrix left right := by
  change (∑ value : C, weight * (state.block value).matrix left right) =
    weight * (∑ value : C, (state.block value).matrix) left right
  simp only [Matrix.sum_apply, Finset.mul_sum]

/-- The actual physical Alice labels equal the values in the complete output store. -/
def matchesStored (count : Nat) (stored : Store (context count))
    (basis : (context count).register.Index) : Prop :=
  ∀ index : Fin (count * 2),
    (basis (measuredPosition count index)).val =
      (stored.read (.storage (resultCell count index).toCStorageRef)).toFin.val

/-- Every old result value is overwritten, even in a classically correlated input state. -/
lemma weighted_writtenStore {count : Nat} {Reference : Register} {History : Type}
    [Fintype History] (state : State (context count) Reference History)
    (stored : Store (context count)) (row column : (context count).register.Index)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.weightedMatrixEntry state (fun original =>
      if writtenStore count original.1 row = stored then 1 else 0)
        (row, leftRef) (column, rightRef) =
      if matchesStored count stored row then
        state.quantumMarginal.matrix (row, leftRef) (column, rightRef)
      else 0 := by
  by_cases matched : matchesStored count stored row
  · have written (original : Store (context count)) :
        writtenStore count original row = stored :=
      (writtenStore_eq_iff count original stored row).mpr matched
    have weights : (fun original : Store (context count) × History =>
        if writtenStore count original.1 row = stored then (1 : ℂ) else 0) =
        (fun _ => (1 : ℂ)) := by
      funext original
      exact if_pos (written original.1)
    rw [weights, weightedMatrixEntry_const, if_pos matched, one_mul]
  · have unwritten (original : Store (context count)) :
        writtenStore count original row ≠ stored := fun same =>
      matched ((writtenStore_eq_iff count original stored row).mp same)
    have weights : (fun original : Store (context count) × History =>
        if writtenStore count original.1 row = stored then (1 : ℂ) else 0) =
        (fun _ => (0 : ℂ)) := by
      funext original
      exact if_neg (unwritten original.1)
    rw [weights, weightedMatrixEntry_const, if_neg matched, zero_mul]

private lemma labelsAgree_iff_forall {ctx : RuntimeCtx .quantum}
    (items : List (ZReadout ctx)) (left right : ctx.register.Index) :
    Circuit.measurementLabelsAgree items left right ↔
      ∀ item ∈ items, left item.wire = right item.wire := by
  induction items with
  | nil => simp [Circuit.measurementLabelsAgree]
  | cons head tail ih =>
      simp [Circuit.measurementLabelsAgree, ih]

/-- The interpreter's actual agreement predicate reads precisely Alice's physical wires. -/
lemma labelsAgree_iff (count : Nat) (left right : (context count).register.Index) :
    Circuit.measurementLabelsAgree (readouts count) left right ↔
      ∀ index : Fin (count * 2),
        (left (measuredPosition count index)).val =
          (right (measuredPosition count index)).val := by
  rw [labelsAgree_iff_forall]
  change (∀ item ∈ (List.ofFn fun index : Fin (count * 2) =>
      QubitReadouts.readout (measuredPosition count index)
        (measuredPosition_dimension count index) (resultCell count index)),
      left item.wire = right item.wire) ↔ _
  constructor
  · intro same index
    exact congrArg Fin.val (same _ (List.mem_ofFn.mpr ⟨index, rfl⟩))
  · intro same item present
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
    exact Fin.ext (same index)

lemma labelsAgree_and_matches_iff (count : Nat) (stored : Store (context count))
    (left right : (context count).register.Index) :
    (Circuit.measurementLabelsAgree (readouts count) left right ∧
        matchesStored count stored left) ↔
      (matchesStored count stored left ∧ matchesStored count stored right) := by
  rw [labelsAgree_iff]
  constructor
  · rintro ⟨same, matched⟩
    exact ⟨matched, fun index => (same index).symm.trans (matched index)⟩
  · rintro ⟨leftMatched, rightMatched⟩
    exact ⟨fun index => (leftMatched index).trans (rightMatched index).symm, leftMatched⟩

/-- Square projector on the actual measured labels; every Alice and Bob system remains live. -/
def actualProjector (count : Nat) (stored : Store (context count)) :
    HilbertOperator (context count).register :=
  Matrix.diagonal fun basis => if matchesStored count stored basis then 1 else 0

lemma actualProjector_sandwich_entry (count : Nat) (stored : Store (context count))
    (matrix : HilbertOperator (context count).register)
    (left right : (context count).register.Index) :
    (actualProjector count stored * matrix *
      (actualProjector count stored).conjTranspose) left right =
        if matchesStored count stored left ∧ matchesStored count stored right then
          matrix left right else 0 := by
  by_cases hl : matchesStored count stored left <;>
    by_cases hr : matchesStored count stored right <;>
      simp [actualProjector, Matrix.diagonal_mul, Matrix.mul_diagonal,
        Matrix.diagonal_conjTranspose, hl, hr]

/-- Actual measured writes act on every reference matrix slice by the full square projector. -/
lemma measured_writtenStore_entry {count : Nat} {Reference : Register} {History : Type}
    [Fintype History] (state : State (context count) Reference History)
    (stored : Store (context count)) (row column : (context count).register.Index)
    (leftRef rightRef : Reference.Index) :
    (if Circuit.measurementLabelsAgree (readouts count) row column then
      ExecutionState.weightedMatrixEntry state (fun original =>
        if writtenStore count original.1 row = stored then 1 else 0)
          (row, leftRef) (column, rightRef)
    else 0) =
      (actualProjector count stored *
        state.quantumMarginal.matrix.submatrix (fun index => (index, leftRef))
          (fun index => (index, rightRef)) *
        (actualProjector count stored).conjTranspose) row column := by
  rw [weighted_writtenStore, actualProjector_sandwich_entry]
  have paired := labelsAgree_and_matches_iff count stored row column
  by_cases same : Circuit.measurementLabelsAgree (readouts count) row column
  · by_cases matched : matchesStored count stored row
    · have both : matchesStored count stored row ∧ matchesStored count stored column :=
        paired.mp ⟨same, matched⟩
      simp only [if_pos same, if_pos matched, if_pos both, Matrix.submatrix_apply]
    · have notBoth : ¬(matchesStored count stored row ∧ matchesStored count stored column) :=
        fun both => matched both.1
      simp only [if_pos same, if_neg matched, if_neg notBoth]
  · have notBoth : ¬(matchesStored count stored row ∧ matchesStored count stored column) :=
      fun both => same (paired.mpr both).1
    simp only [if_neg same, if_neg notBoth]

/-- The same actual branch's correction, measurement projector and Alice native operator. -/
def actualInstrument (environment : model.Environment) (count : Nat) (stored : Store (context
    count)) :
    HilbertOperator (context count).register :=
  ((selectedCorrection count (stored.read (resultInput count))).matrix environment.quantum) *
    actualProjector count stored * ((onContext count (aliceWord count)).matrix environment.quantum)

/-- The actual full-store branch depends on the original full quantum marginal only.

Both external-reference coordinates are arbitrary. No subsystem is discarded, no
initial classical independence is assumed, and the selector is the actual stored result.
-/
lemma code_store_instrument_entry
    (environment : model.Environment) (count : Nat) {Reference : Register} {History : Type}
    [Fintype History] (state : State (context count) Reference (model.HiddenState × History))
    (stored : Store (context count)) (left right : (context count).register.Index)
    (leftRef rightRef : Reference.Index) :
    (ExecutionState.filterClassical (((code count).execute environment) Reference state)
      (fun entry => entry.1 = stored)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      (actualInstrument environment count stored *
        state.quantumMarginal.matrix.submatrix (fun index => (index, leftRef))
          (fun index => (index, rightRef)) *
        (actualInstrument environment count stored).conjTranspose) left right := by
  let alice : State (context count) Reference (model.HiddenState × (History × Unit)) :=
    ((Circuit.unitary (allowAllocation := false) (operations := .empty)
      (classicalOracles := .empty) (onContext count (aliceWord count))).execute environment)
        Reference state
  let A : HilbertOperator (context count).register := ((onContext count (aliceWord count)).matrix
    environment.quantum)
  let C : HilbertOperator (context count).register :=
    ((selectedCorrection count (stored.read (resultInput count))).matrix environment.quantum)
  let P : HilbertOperator (context count).register := actualProjector count stored
  let original : HilbertOperator (context count).register :=
    state.quantumMarginal.matrix.submatrix (fun index => (index, leftRef))
      (fun index => (index, rightRef))
  let afterAlice : HilbertOperator (context count).register :=
    alice.quantumMarginal.matrix.submatrix (fun index => (index, leftRef))
      (fun index => (index, rightRef))
  have aliceSame : afterAlice = A * original * A.conjTranspose := by
    ext row column
    exact (congrArg (fun density : DensityOperator ((context count).register.prod Reference) =>
      density.matrix (row, leftRef) (column, rightRef))
        (Circuit.unitary_jointDensity (allowAllocation := false) (operations := .empty)
          (services := .empty) environment (onContext count (aliceWord count)) state)).trans
      (DensityOperator.localUnitary_block ((onContext count (aliceWord count)).matrix
        environment.quantum)
        state.quantumMarginal row column leftRef rightRef)
  have actual :
      (ExecutionState.filterClassical (((code count).execute environment) Reference state)
        (fun entry => entry.1 = stored)).quantumMarginal.matrix
          (left, leftRef) (right, rightRef) =
        (C * (P * afterAlice * P.conjTranspose) * C.conjTranspose) left right := by
    rw [code_store_entry]
    change (∑ column : (context count).register.Index,
      (∑ row : (context count).register.Index, C left row *
        (if Circuit.measurementLabelsAgree (readouts count) row column then
          ExecutionState.weightedMatrixEntry alice (fun entry =>
            if writtenStore count entry.1 row = stored then 1 else 0)
              (row, leftRef) (column, rightRef)
        else 0)) * star (C right column)) = _
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro column _
    rw [Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply congrArg (fun value : ℂ => value * star (C right column))
    apply Finset.sum_congr rfl
    intro row _
    exact congrArg (fun value : ℂ => C left row * value)
      (measured_writtenStore_entry alice stored row column leftRef rightRef)
  rw [actual, aliceSame]
  change (C * (P * (A * original * A.conjTranspose) * P.conjTranspose) *
    C.conjTranspose) left right =
    ((C * P * A) * original * (C * P * A).conjTranspose) left right
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end

end QuantumAlg.QuantumTeleportation.Parallel.StoreInstrument
