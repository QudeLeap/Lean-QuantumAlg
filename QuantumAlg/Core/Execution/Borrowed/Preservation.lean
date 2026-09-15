/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Borrowed.State
import all QuantumAlg.Core.Execution.Borrowed.Classical
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Compositional restoration of actual borrowed storage

Classical updates write only writable cells, so they preserve the entire joint
borrowed classical-quantum-reference observation. Retaining a new classical
cell has the same property. Restoration composes along actual circuit
execution and its recorded histories; no final-state promise excuses it.
-/

namespace QuantumAlg

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
  {H K : Type} [Fintype H] [Fintype K]

/-- Relabeling records preserves the full borrowed observation when actual borrowed reads agree. -/
theorem observeBorrowed_mapClassical (state : State ctx Reference H)
    (update : Store ctx × H → Store ctx × K)
    (preserves : ∀ value,
      (update value).1.readBorrowedClassical = value.1.readBorrowedClassical) :
    observeBorrowed Reference (state.mapClassical update) = observeBorrowed Reference state := by
  apply ExecutionState.ext
  intro value
  rw [observeBorrowed_block, observeBorrowed_block,
    ExecutionState.executionState_mapClassical_comp]
  have same : (fun result : Store ctx × K => result.1.readBorrowedClassical) ∘ update =
      (fun result : Store ctx × H => result.1.readBorrowedClassical) := funext preserves
  rw [same]

/-- Mathematical history changes do not alter any actual borrowed correlation. -/
theorem observeBorrowed_mapHistory (state : State ctx Reference H) (update : H → K) :
    observeBorrowed Reference (state.mapHistory update) = observeBorrowed Reference state :=
  observeBorrowed_mapClassical state _ (fun _ => rfl)

/-- When the live context is unchanged, borrowed observation transport is the identity. -/
theorem observeBorrowedAfter_sameContext (code : Circuit ctx ctx) (state : State ctx Reference H) :
    observeBorrowedAfter code Reference state = observeBorrowed Reference state := rfl

end Execution

namespace Circuit

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
  {H : Type} [Fintype H]

/-- Every closed classical operation restores all borrowed values and quantum correlations. -/
theorem borrowedRestored_classical {input output : CShape}
    (op : ClassicalOp input output ctx ctx) (state : State ctx Reference H) :
    (Circuit.classical op).BorrowedRestored Reference state
      ((Circuit.classical op).execute Reference state) := by
  rw [BorrowedRestored, observeBorrowedAfter_sameContext, execute_classical]
  apply ExecutionState.ext
  intro value
  simp only [observeBorrowed_block, State.classicalStep,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def,
    Store.readBorrowedClassical_applyOp]

/-- Allocating a retained classical cell restores the complete original borrowed interface. -/
theorem borrowedRestored_retain (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (state : State ctx Reference H) :
    (Circuit.retain ctx key shape fresh).BorrowedRestored Reference state
      ((Circuit.retain ctx key shape fresh).execute Reference state) := by
  change observeBorrowed (ctx := ctx.addRetained key shape fresh) Reference
    (state.mapClassical (fun value =>
      (value.1.pushRetained key shape fresh, (value.2, ())))) = observeBorrowed Reference state
  apply ExecutionState.ext
  intro value
  rw [observeBorrowed_block, observeBorrowed_block,
    ExecutionState.executionState_mapClassical_comp]
  rfl

/-- Two actual restoring executions restore the same complete borrowed interface in sequence. -/
theorem borrowedRestored_seq {middle post : RuntimeCtx kind}
    (first : Circuit ctx middle) (second : Circuit middle post) (state : State ctx Reference H)
    (firstRestores : first.BorrowedRestored Reference state (first.execute Reference state))
    (secondRestores : second.BorrowedRestored Reference (first.execute Reference state)
      (second.execute Reference (first.execute Reference state))) :
    (Circuit.seq first second).BorrowedRestored Reference state
      ((Circuit.seq first second).execute Reference state) := by
  unfold BorrowedRestored observeBorrowedAfter at firstRestores secondRestores ⊢
  rw [execute_seq, observeBorrowed_mapHistory]
  change transportBorrowed Reference
    (second.borrowedClassicalShape_preserved.trans first.borrowedClassicalShape_preserved)
    (second.borrowedRegister_preserved.trans first.borrowedRegister_preserved) _ = _
  rw [← transportBorrowed_trans Reference
    second.borrowedClassicalShape_preserved first.borrowedClassicalShape_preserved
    second.borrowedRegister_preserved first.borrowedRegister_preserved,
    secondRestores, firstRestores]

end Circuit

end

end QuantumAlg
