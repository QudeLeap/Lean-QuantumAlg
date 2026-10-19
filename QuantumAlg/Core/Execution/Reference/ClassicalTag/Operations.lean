/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Reference.ClassicalTag.State
import all QuantumAlg.Core.Execution.Reference.ClassicalTag.Coordinates
import all QuantumAlg.Core.Execution.Reference.Unitary
import all QuantumAlg.Core.Execution.Random.Kernel
import all QuantumAlg.Core.Execution.State.Coordinates
import all QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# Complete reference-tag slices through the existing primitive state maps

The auxiliary outcome coordinates merely reassociate the same kernel and
measurement records already used by the interpreter. No new instruction or
choice of transition is exposed by these mathematical equalities.
-/

namespace QuantumAlg.Execution.State

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference Tag : Register}
  {H K Outcome : Type} [Fintype H] [Fintype K] [Fintype Outcome]

/-- Retain the original tag after the newly recorded actual outcome. -/
def tagOutcomeExchange (History TagValue Result : Type) :
    ((History × TagValue) × Result) ≃ ((History × Result) × TagValue) where
  toFun value := ((value.1.1, value.2), value.1.2)
  invFun value := ((value.1.1, value.2), value.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- A bijective history coordinate map retains its complete original block. -/
lemma mapHistory_equiv_entry (state : State ctx Reference H) (labels : H ≃ K)
    (store : Store ctx) (history : K) (row column : (ctx.register.prod Reference).Index) :
    ((state.mapHistory labels).block (store, history)).matrix row column =
      (state.block (store, labels.symm history)).matrix row column := by
  change ((state.mapClassical ((Equiv.refl (Store ctx)).prodCongr labels)).block
      (store, history)).matrix row column = _
  rw [ExecutionState.coordinate_mapClassical_block]
  rfl

/-- An arbitrary actual store/history update retains the external tag unchanged. -/
lemma decodeReferenceTag_mapRecord (state : State ctx (Tag.prod Reference) H)
    (update : Store ctx × H → Store ctx × K) :
    decodeReferenceTag (state.mapClassical update) =
      (decodeReferenceTag state).mapClassical (fun record =>
        let result := update (record.1, record.2.1)
        (result.1, (result.2, record.2.2))) := by
  apply ExecutionState.ext
  rintro ⟨store, history, tag⟩
  apply DensityOperator.ext
  ext row column
  rw [decodeReferenceTag_entry]
  simp only [ExecutionState.mapClassical_block_matrix, Matrix.sum_apply, Matrix.ite_apply,
    Matrix.zero_apply, Fintype.sum_prod_type, Prod.mk.injEq, decodeReferenceTag_entry]
  apply Finset.sum_congr rfl
  intro originalStore _
  apply Finset.sum_congr rfl
  intro originalHistory _
  by_cases sameStore : (update (originalStore, originalHistory)).1 = store <;>
    by_cases sameHistory : (update (originalStore, originalHistory)).2 = history <;>
      simp [Prod.ext_iff, sameStore, sameHistory]

/-- Reassociate the existing conditional sampling outcome into mathematical history. -/
def kernelOutcome (state : State ctx Reference H)
    (transition : Store ctx × H → PMF Outcome) : State ctx Reference (H × Outcome) :=
  (kernelChoice state transition).mapClassical (Equiv.prodAssoc (Store ctx) H Outcome)

/-- The reassociation leaves exactly the original kernel-weighted density block. -/
lemma kernelOutcome_entry (state : State ctx Reference H)
    (transition : Store ctx × H → PMF Outcome) (store : Store ctx)
    (history : H) (outcome : Outcome) (row column : (ctx.register.prod Reference).Index) :
    ((kernelOutcome state transition).block (store, (history, outcome))).matrix row column =
      (transition (store, history) outcome).toReal •
        (state.block (store, history)).matrix row column := by
  rw [kernelOutcome, ExecutionState.coordinate_mapClassical_block,
    kernelChoice_block_matrix]
  rfl

/-- A declared kernel acts on every tag slice with exactly the same actual probability. -/
lemma decodeReferenceTag_kernelOutcome (state : State ctx (Tag.prod Reference) H)
    (transition : Store ctx × H → PMF Outcome) :
    decodeReferenceTag (kernelOutcome state transition) =
      (kernelOutcome (decodeReferenceTag state)
        (fun record => transition (record.1, record.2.1))).mapHistory
          (tagOutcomeExchange H Tag.Index Outcome) := by
  apply ExecutionState.ext
  rintro ⟨store, ⟨history, outcome⟩, tag⟩
  apply DensityOperator.ext
  ext row column
  rw [decodeReferenceTag_entry, mapHistory_equiv_entry]
  change _ = ((kernelOutcome (decodeReferenceTag state)
    (fun record => transition (record.1, record.2.1))).block
      (store, ((history, tag), outcome))).matrix row column
  rw [kernelOutcome_entry, kernelOutcome_entry, decodeReferenceTag_entry]

/-- A local quantum operation preserves each complete external-reference tag block. -/
lemma decodeReferenceTag_applyLocalUnitary (state : State ctx (Tag.prod Reference) H)
    (operator : Store ctx × H → UnitaryOperator ctx.register) :
    decodeReferenceTag
        (state.applyUnitary fun record => UnitaryOperator.prodTensor (operator record)
          (1 : UnitaryOperator (Tag.prod Reference))) =
      (decodeReferenceTag state).applyUnitary fun record =>
        UnitaryOperator.prodTensor (operator (record.1, record.2.1))
          (1 : UnitaryOperator Reference) := by
  apply ExecutionState.ext
  rintro ⟨store, history, tag⟩
  apply DensityOperator.ext
  ext row column
  rcases row with ⟨row, leftRef⟩
  rcases column with ⟨column, rightRef⟩
  rw [decodeReferenceTag_entry]
  simp only [ExecutionState.applyUnitary_block, DensityOperator.localUnitary_block,
    Matrix.mul_apply, Matrix.submatrix_apply, decodeReferenceTag_entry]

/-- Reassociate the existing retained Z outcome into the same mathematical history. -/
def measureOutcome (state : State ctx Reference H) (readout : ctx.register.Index → Outcome) :
    State ctx Reference (H × Outcome) :=
  (ExecutionState.measureZ state (fun basis => readout basis.1)).mapClassical
    (Equiv.prodAssoc (Store ctx) H Outcome)

/-- The reassociated measurement keeps the exact surviving original matrix entry. -/
lemma measureOutcome_entry (state : State ctx Reference H)
    (readout : ctx.register.Index → Outcome) (store : Store ctx) (history : H)
    (outcome : Outcome) (row column : (ctx.register.prod Reference).Index) :
    ((measureOutcome state readout).block (store, (history, outcome))).matrix row column =
      if readout row.1 = outcome ∧ readout column.1 = outcome then
        (state.block (store, history)).matrix row column else 0 := by
  rw [measureOutcome, ExecutionState.coordinate_mapClassical_block,
    ExecutionState.measureZ_block, ZMeasurement.branch_matrix]
  rfl

/-- Actual measurement and every classical recorded outcome preserve the untouched tag. -/
lemma decodeReferenceTag_measureOutcome (state : State ctx (Tag.prod Reference) H)
    (readout : ctx.register.Index → Outcome) :
    decodeReferenceTag (measureOutcome state readout) =
      (measureOutcome (decodeReferenceTag state) readout).mapHistory
        (tagOutcomeExchange H Tag.Index Outcome) := by
  apply ExecutionState.ext
  rintro ⟨store, ⟨history, outcome⟩, tag⟩
  apply DensityOperator.ext
  ext row column
  rw [decodeReferenceTag_entry, mapHistory_equiv_entry]
  change _ = ((measureOutcome (decodeReferenceTag state) readout).block
    (store, ((history, tag), outcome))).matrix row column
  rw [measureOutcome_entry, measureOutcome_entry, decodeReferenceTag_entry]

end

end QuantumAlg.Execution.State
