/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import QuantumAlg.Core.Execution.Random.Kernel.Map
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Retained allocation followed by one actual classical instruction

This construction uses the common circuit interpreter. Its execution equation
preserves each complete quantum-reference block while updating the actual
store. The granted declaration supplies its actual, possibly stochastic,
result. Native events and space are derived from the same two instructions.
-/

namespace QuantumAlg.Circuit

variable {model : ExecutionModel} (ctx : RuntimeCtx model.kind) (key : StorageKey)
  (shape : CShape) (fresh : key ∉ ctx.keys)
  (op : model.classicalOperations.Application (ctx.addRetained key shape fresh))

/-- Allocate the actual retained cell before executing the supplied closed instruction. -/
public def retainedStep : Circuit model ctx (ctx.addRetained key shape fresh) :=
  .seq (.retain ctx key shape fresh) (.classical op)

/-- The unique instruction emits its own native event after the allocation. -/
lemma retainedStep_eventTrace (path : (retainedStep ctx key shape fresh op).Path) :
    (retainedStep ctx key shape fresh op).eventTrace path =
      [.classicalOperation (model.classicalOperations.coordinate op.token)] := rfl

/-- Every actual visited context is the input or the extended live store. -/
lemma retainedStep_visitedContexts (path : (retainedStep ctx key shape fresh op).Path) :
    (retainedStep ctx key shape fresh op).visitedContexts path =
      [ctx, ctx.addRetained key shape fresh, ctx.addRetained key shape fresh] := rfl

/-- The resident peak includes the newly retained cell and all original systems. -/
lemma retainedStep_peakResidentSpace (path : (retainedStep ctx key shape fresh op).Path) :
    (retainedStep ctx key shape fresh op).peakResidentSpace path =
      (ctx.addRetained key shape fresh).residentSpace := by
  funext axis
  change max (ctx.residentSpace axis)
    (max ((ctx.addRetained key shape fresh).residentSpace axis)
      (max ((ctx.addRetained key shape fresh).residentSpace axis) 0)) = _
  simp only [Nat.max_zero, Nat.max_self]
  apply max_eq_right
  rw [RuntimeCtx.residentSpace_addRetained]
  exact Nat.le_add_left _ _

/-- The retained result counts as auxiliary storage in the actual path peak. -/
lemma retainedStep_peakAuxiliarySpace (path : (retainedStep ctx key shape fresh op).Path) :
    (retainedStep ctx key shape fresh op).peakAuxiliarySpace path =
      (ctx.addRetained key shape fresh).auxiliarySpace := by
  funext axis
  change max (ctx.auxiliarySpace axis)
    (max ((ctx.addRetained key shape fresh).auxiliarySpace axis)
      (max ((ctx.addRetained key shape fresh).auxiliarySpace axis) 0)) = _
  simp only [Nat.max_zero, Nat.max_self]
  apply max_eq_right
  rw [RuntimeCtx.auxiliarySpace_addRetained]
  exact Nat.le_add_left _ _

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Execution retains each declared probability, actual write, and complete reference block. -/
lemma execute_retainedStep (environment : model.Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : Execution.State ctx Reference (model.HiddenState × History)) :
    (retainedStep ctx key shape fresh op).execute environment Reference state =
      (Execution.kernelChoice state (fun original =>
        model.classicalOperations.evaluate op.token
          ((original.1.pushRetained key shape fresh).read op.input))).mapClassical
        (fun result =>
          ((result.1.1.pushRetained key shape fresh).write op.output result.2,
            (result.1.2.1, (result.1.2.2, ((), result.2))))) := by
  simp only [retainedStep, execute_seq, execute_retain, execute_classical,
    Execution.State.mapHistory]
  rw [Execution.kernelChoice_mapClassical (afterMap := inferInstance),
    ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance),
    ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Borrowed classical values, quantum systems, and external correlations are restored jointly. -/
lemma retainedStep_borrowedRestored (environment : model.Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : Execution.State ctx Reference (model.HiddenState × History)) :
    (retainedStep ctx key shape fresh op).BorrowedRestored Reference state
      ((retainedStep ctx key shape fresh op).execute environment Reference state) := by
  unfold retainedStep
  apply borrowedRestored_seq
  · exact borrowedRestored_retain (environment := environment) key shape fresh state
  · exact borrowedRestored_classical (environment := environment) op _

end

end QuantumAlg.Circuit
