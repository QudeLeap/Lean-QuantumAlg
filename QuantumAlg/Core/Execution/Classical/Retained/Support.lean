/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Retained.Execution
import all QuantumAlg.Core.Execution.Classical.Retained.Read
import all QuantumAlg.Core.Execution.State.Support

/-! # Supported output Stores of actual retained allocation -/

namespace QuantumAlg.Execution.RetainedCells
noncomputable section
local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- A supported output of the generic real retained allocation is the
initialized `pushStore` image of an actual input. Keeping this step generic
prevents proof elaboration from unfolding the P-256 Store and register. -/
lemma allocated_store_of_support
    {model : ExecutionModel} (environment : model.Environment)
    (ctx : RuntimeCtx model.kind) (shapes : List CShape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History))
    (property : Store (RetainedCells.context ctx shapes) → Prop)
    (all : ∀ source : Store ctx,
      property (RetainedCells.pushStore ctx shapes source))
    (value : Store (RetainedCells.context ctx shapes) ×
      (model.HiddenState ×
        (History × (RetainedCells.allocate (model := model) ctx shapes).Path)))
    (supported :
      0 < (((RetainedCells.allocate (model := model) ctx shapes).execute
        environment Reference state).block value).mass) :
    property value.1 := by
  have complete := RetainedCells.allocate_execute environment ctx shapes state
  rw [complete] at supported
  exact supported_register_cast_mapClassical
    (h := (RetainedCells.context_register ctx shapes).symm)
    (decision := Classical.decEq _)
    (state := state)
    (update := fun entry =>
      (RetainedCells.pushStore ctx shapes entry.1,
        (entry.2.1, (entry.2.2,
          RetainedCells.allocatePath (model := model) ctx shapes))))
    (property := fun label => property label.1)
    (all := fun entry => all entry.1)
    (value := value) supported

/-- A real preceding circuit feeds retained allocation without imposing any
initial condition on its supported Stores. -/
lemma sequence_allocated_store_of_support
    {model : ExecutionModel} (environment : model.Environment)
    {initial ctx : RuntimeCtx model.kind} (preceding : Circuit model initial ctx)
    (shapes : List CShape) {Reference : Register} {History : Type} [Fintype History]
    (state : State initial Reference (model.HiddenState × History))
    (property : Store (context ctx shapes) → Prop)
    (all : ∀ source : Store ctx, property (pushStore ctx shapes source))
    (value : Store (context ctx shapes) × (model.HiddenState ×
      (History × (preceding.seq (allocate (model := model) ctx shapes)).Path)))
    (supported : 0 < (((preceding.seq (allocate (model := model) ctx shapes)).execute
      environment Reference state).block value).mass) : property value.1 := by
  rw [Circuit.execute_seq] at supported
  apply State.supported_store_mapHistory
    (state := (allocate (model := model) ctx shapes).execute environment Reference
      (preceding.execute environment Reference state))
    (historyMap := fun history =>
      (history.1, (history.2.1.1, (history.2.1.2, history.2.2))))
    (property := property) (value := value) ?_ supported
  intro allocated positive
  exact allocated_store_of_support environment ctx shapes
    (preceding.execute environment Reference state) property all allocated positive


end
end QuantumAlg.Execution.RetainedCells
