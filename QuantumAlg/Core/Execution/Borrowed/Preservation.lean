/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Core.Execution.Random.Kernel.Discard
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

variable {allowAllocation : Bool}

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
  {H K : Type} [Fintype H] [Fintype K]

/-- Relabeling records preserves the full borrowed observation when actual borrowed reads agree. -/
lemma observeBorrowed_mapClassical (state : State ctx Reference H)
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
lemma observeBorrowed_mapHistory (state : State ctx Reference H) (update : H → K) :
    observeBorrowed Reference (state.mapHistory update) = observeBorrowed Reference state :=
  observeBorrowed_mapClassical state _ (fun _ => rfl)

/-- When the live context is unchanged, borrowed observation transport is the identity. -/
lemma observeBorrowedAfter_sameContext {model : ExecutionModel}
    {ctx : RuntimeCtx model.kind} (code : Circuit model ctx ctx allowAllocation)
    (state : State ctx Reference H) :
    observeBorrowedAfter code Reference state = observeBorrowed Reference state := rfl

/-- A declared stochastic service preserves the complete borrowed observation of its input. -/
lemma observeBorrowed_queryStep {oracles : ClassicalOracleModel}
    (environment : oracles.Interpretation)
    (application : oracles.Application ctx)
    (state : State ctx Reference (oracles.HiddenState × H)) :
    observeBorrowed Reference (queryStep environment application state) =
      observeBorrowed Reference state := by
  apply ExecutionState.ext
  intro value
  rw [observeBorrowed_block, observeBorrowed_block]
  congr 1
  dsimp only [queryStep]
  rw [ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
  simpa only [Function.comp_def, Store.readBorrowedClassical_write] using
    congrArg (fun observed : ExecutionState ctx.borrowedClassicalShape.Value
      (Register.prod ctx.register Reference) => observed.block value)
      (kernelChoice_map_ignore state
        (fun entry => oracles.transition environment application.query entry.2.1
          (entry.1.read application.input)) (fun entry => entry.1.readBorrowedClassical))

end Execution

namespace Circuit

open Execution

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind} {Reference : Register}
  {H : Type} [Fintype H]

variable (environment : model.Environment)

/-- The identity instruction records its path without changing any borrowed correlation. -/
lemma borrowedRestored_id (state : State ctx Reference (model.HiddenState × H)) :
    (Circuit.id
        (allowAllocation := allowAllocation)
        (model := model) ctx).BorrowedRestored Reference state
      ((Circuit.id
          (allowAllocation := allowAllocation)
          (model := model) ctx).execute environment Reference state) := by
  rw [BorrowedRestored, observeBorrowedAfter_sameContext, execute_id]
  apply ExecutionState.ext
  intro value
  rw [observeBorrowed_block, observeBorrowed_block]
  congr 1
  rw [ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
  rfl

/-- A granted native operation restores the complete borrowed classical-quantum interface. -/
lemma borrowedRestored_classical
    (application : model.classicalOperations.Application ctx)
    (state : State ctx Reference (model.HiddenState × H)) :
    (Circuit.classical
        (allowAllocation := allowAllocation)
        (model := model) application).BorrowedRestored Reference state
      ((Circuit.classical
          (allowAllocation := allowAllocation)
          (model := model) application).execute environment Reference state) := by
  rw [BorrowedRestored, observeBorrowedAfter_sameContext, execute_classical]
  apply ExecutionState.ext
  intro value
  rw [observeBorrowed_block, observeBorrowed_block]
  congr 1
  rw [ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
  simpa only [Function.comp_def, Store.readBorrowedClassical_write] using
    congrArg (fun observed : ExecutionState ctx.borrowedClassicalShape.Value
      (Register.prod ctx.register Reference) => observed.block value)
      (kernelChoice_map_ignore state
        (fun entry => model.classicalOperations.evaluate application.token
          (entry.1.read application.input)) (fun entry => entry.1.readBorrowedClassical))

/-- A stateful randomized query preserves every borrowed correlation after its actual update. -/
lemma borrowedRestored_classicalQuery
    (application : model.classicalOracles.Application ctx)
    (state : State ctx Reference (model.HiddenState × H)) :
    (Circuit.classicalQuery
        (allowAllocation := allowAllocation)
        (model := model) application).BorrowedRestored Reference state
      ((Circuit.classicalQuery
          (allowAllocation := allowAllocation)
          (model := model) application).execute environment Reference state) := by
  rw [BorrowedRestored, observeBorrowedAfter_sameContext, execute_classicalQuery]
  exact observeBorrowed_queryStep environment.classical application state

/-- Allocating a retained classical cell restores the complete original borrowed interface. -/
lemma borrowedRestored_retain (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (state : State ctx Reference (model.HiddenState × H)) :
    (Circuit.retain (model := model) ctx key shape fresh).BorrowedRestored Reference state
      ((Circuit.retain (model := model) ctx key shape fresh).execute
        environment Reference state) := by
  rw [BorrowedRestored, observeBorrowedAfter, execute_retain]
  change observeBorrowed (ctx := ctx.addRetained key shape fresh) Reference
    (state.mapClassical fun value =>
      (value.1.pushRetained key shape fresh, (value.2.1, (value.2.2, ())))) =
        observeBorrowed Reference state
  apply ExecutionState.ext
  intro value
  rw [observeBorrowed_block, observeBorrowed_block,
    ExecutionState.executionState_mapClassical_comp]
  rfl

/-- Two actual restoring executions restore the same complete borrowed interface in sequence. -/
lemma borrowedRestored_seq {middle post : RuntimeCtx model.kind}
    (first : Circuit model ctx middle allowAllocation)
    (second : Circuit model middle post allowAllocation)
    (state : State ctx Reference (model.HiddenState × H))
    (firstRestores : first.BorrowedRestored Reference state
      (first.execute environment Reference state))
    (secondRestores : second.BorrowedRestored Reference (first.execute environment Reference state)
      (second.execute environment Reference (first.execute environment Reference state))) :
    (Circuit.seq first second).BorrowedRestored Reference state
      ((Circuit.seq first second).execute environment Reference state) := by
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
