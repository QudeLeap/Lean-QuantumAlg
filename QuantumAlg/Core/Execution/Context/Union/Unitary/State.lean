/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Union.State
import all QuantumAlg.Core.Execution.Context.Union.Unitary
import all QuantumAlg.Core.Execution.Local.Marginals
import all QuantumAlg.Core.Execution.Interpret.Laws

/-!
# Complete state naturality of a physically framed unitary

The actual tensor instruction commutes with the exact union store and wire
coordinates. Its Unit execution record is reassociated with the untouched
right store; no classical block or quantum/reference coordinate is summed
away. The proof uses complete unitary conjugation
[dW19, qcnotes.tex:389,5405] on arbitrary correlated input blocks.
-/

namespace QuantumAlg.Execution.ContextUnion

noncomputable section

open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (left right : RuntimeCtx .quantum)
  (separate : RuntimeCtx.StorageDisjoint left right)
  (program : UnitaryCircuit left.register) (placed : program.physical_idx = left.physicalIdx)

/-- The actual framed operator is the original unitary beside the full reassociated reference. -/
theorem contextUnion_unitary_referenceBasis (Reference : Register) :
    UnitaryOperator.reindex (referenceBasis left right separate Reference)
      (UnitaryOperator.prodTensor (frameUnitary left right separate program placed).matrix
        (1 : UnitaryOperator Reference)) =
      UnitaryOperator.prodTensor program.matrix
        (1 : UnitaryOperator (Register.prod right.register Reference)) := by
  apply Subtype.ext
  funext row column
  obtain ⟨leftRow, rightRow, refRow⟩ := row
  obtain ⟨leftColumn, rightColumn, refColumn⟩ := column
  change (UnitaryOperator.prodTensor
    (frameUnitary left right separate program placed).matrix (1 : UnitaryOperator Reference))
      ((unionBasisEquiv left right separate).symm (leftRow, rightRow), refRow)
      ((unionBasisEquiv left right separate).symm (leftColumn, rightColumn), refColumn) =
    (UnitaryOperator.prodTensor program.matrix
      (1 : UnitaryOperator (Register.prod right.register Reference)))
        (leftRow, (rightRow, refRow)) (leftColumn, (rightColumn, refColumn))
  rw [contextUnion_frameUnitary_reference_entry, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, UnitaryOperator.prodTensor_apply]
  change (program.matrix leftRow leftColumn * (if rightRow = rightColumn then 1 else 0)) *
      (if refRow = refColumn then 1 else 0) =
    program.matrix leftRow leftColumn *
      (if ((rightRow, refRow) : (Register.prod right.register Reference).Index) =
        (rightColumn, refColumn) then 1 else 0)
  have same : ((rightRow, refRow) : (Register.prod right.register Reference).Index) =
      (rightColumn, refColumn) ↔ rightRow = rightColumn ∧ refRow = refColumn := by
    constructor
    · intro equal
      exact ⟨congrArg Prod.fst equal, congrArg Prod.snd equal⟩
    · intro equal
      exact Prod.ext equal.1 equal.2
  simp only [same]
  by_cases rightSame : rightRow = rightColumn <;>
    by_cases refSame : refRow = refColumn <;> simp [rightSame, refSame]

private theorem density_naturality {Reference : Register}
    (density : DensityOperator
      (Register.prod (left.disjointUnion right separate).register Reference)) :
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor (frameUnitary left right separate program placed).matrix
        (1 : UnitaryOperator Reference)) density).reindex
          (referenceBasis left right separate Reference) =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor program.matrix
          (1 : UnitaryOperator (Register.prod right.register Reference)))
        (density.reindex (referenceBasis left right separate Reference)) :=
  (DensityOperator.applyUnitary_reindex
    (UnitaryOperator.prodTensor (frameUnitary left right separate program placed).matrix
      (1 : UnitaryOperator Reference)) density
    (referenceBasis left right separate Reference)).trans
      (congrArg (fun operator => DensityOperator.applyUnitary operator
        (density.reindex (referenceBasis left right separate Reference)))
        (contextUnion_unitary_referenceBasis left right separate program placed Reference))

variable {Reference : Register} {History : Type} [Fintype History]

private theorem split_block
    (state : State (left.disjointUnion right separate) Reference History)
    (first : Store left) (second : Store right) (history : History) :
    (splitState left right separate state).block (first, (second, history)) =
      (state.block (join separate first second, history)).reindex
        (referenceBasis left right separate Reference) := by
  apply DensityOperator.ext
  ext row column
  exact contextUnion_splitState_entry left right separate state
    (first, (second, history)) row column

private theorem historyEquiv_block {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {H K : Type} [Fintype H] [Fintype K] (state : State ctx Reference H)
    (histories : H ≃ K) (store : Store ctx) (history : K) :
    (state.mapHistory histories).block (store, history) =
      state.block (store, histories.symm history) := by
  apply DensityOperator.ext
  change (∑ record : Store ctx × H,
    if (record.1, histories record.2) = (store, history) then
      (state.block record).matrix else 0) = (state.block (store, histories.symm history)).matrix
  have key (record : Store ctx × H) :
      (record.1, histories record.2) = (store, history) ↔
        record = (store, histories.symm history) := by
    constructor
    · intro same
      exact Prod.ext (congrArg (fun value : Store ctx × K => value.1) same)
        (histories.eq_symm_apply.mpr
          (congrArg (fun value : Store ctx × K => value.2) same))
    · rintro rfl
      exact Prod.ext rfl (histories.apply_symm_apply history)
  simp only [key, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem historyAssoc_block
    (state : State left (Register.prod right.register Reference)
      ((Store right × History) × Unit))
    (first : Store left) (second : Store right) (history : History) :
    (state.mapHistory (fun record => (record.1.1, (record.1.2, record.2)))).block
      (first, (second, (history, ()))) = state.block (first, ((second, history), ())) := by
  exact historyEquiv_block state (Equiv.prodAssoc (Store right) History Unit)
    first (second, (history, ()))

/-- Actual unitary execution preserves the entire frame under exact block coordinates. -/
theorem contextUnion_splitState_unitary
    (state : State (left.disjointUnion right separate) Reference History) :
    splitState left right separate
      (state.unitary (frameUnitary left right separate program placed)) =
      ((splitState left right separate state).unitary program).mapHistory
        (fun record => (record.1.1, (record.1.2, record.2))) := by
  apply ExecutionState.ext
  rintro ⟨first, second, history, path⟩
  cases path
  let basis := referenceBasis left right separate Reference
  let fullOperator := UnitaryOperator.prodTensor
    (frameUnitary left right separate program placed).matrix (1 : UnitaryOperator Reference)
  let localOperator := UnitaryOperator.prodTensor program.matrix
    (1 : UnitaryOperator (Register.prod right.register Reference))
  let original := state.block (join separate first second, history)
  calc
    (splitState left right separate
        (state.unitary (frameUnitary left right separate program placed))).block
          (first, (second, (history, ()))) =
        ((state.unitary (frameUnitary left right separate program placed)).block
          (join separate first second, (history, ()))).reindex basis :=
      split_block left right separate _ first second (history, ())
    _ = (DensityOperator.applyUnitary fullOperator original).reindex basis :=
      congrArg (fun density => density.reindex basis)
        (Circuit.execute_unitary_block state (frameUnitary left right separate program placed)
          (contextUnion_frameUnitary_physical left right separate program placed)
          (join separate first second) history)
    _ = DensityOperator.applyUnitary localOperator (original.reindex basis) :=
      density_naturality left right separate program placed original
    _ = DensityOperator.applyUnitary localOperator
        ((splitState left right separate state).block (first, (second, history))) :=
      congrArg (DensityOperator.applyUnitary localOperator)
        (split_block left right separate state first second history).symm
    _ = ((splitState left right separate state).unitary program).block
        (first, ((second, history), ())) :=
      (Circuit.execute_unitary_block (splitState left right separate state)
        program placed first (second, history)).symm
    _ = (((splitState left right separate state).unitary program).mapHistory
        (fun record => (record.1.1, (record.1.2, record.2)))).block
          (first, (second, (history, ()))) :=
      (historyAssoc_block left right
        ((splitState left right separate state).unitary program) first second history).symm

end

end QuantumAlg.Execution.ContextUnion
