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
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# Retained allocation followed by one actual classical instruction

This construction uses the common circuit interpreter. Its execution equation
preserves each complete quantum-reference block while updating the actual
store. Native events and space are derived from the same two instructions.
-/

namespace QuantumAlg.Circuit

variable {kind : ProblemKind} (ctx : RuntimeCtx kind) (key : StorageKey)
  (shape : CShape) (fresh : key ∉ ctx.keys) {input output : CShape}
  (op : ClassicalOp input output
    (ctx.addRetained key shape fresh) (ctx.addRetained key shape fresh))

/-- Allocate the actual retained cell before executing the supplied closed instruction. -/
public def retainedStep : Circuit ctx (ctx.addRetained key shape fresh) :=
  .seq (.retain ctx key shape fresh) (.classical op)

/-- The unique instruction emits its own native event after the allocation. -/
theorem retainedStep_eventTrace (path : (retainedStep ctx key shape fresh op).Path) :
    (retainedStep ctx key shape fresh op).eventTrace path = op.eventTrace := rfl

/-- Every actual visited context is the input or the extended live store. -/
theorem retainedStep_visitedContexts (path : (retainedStep ctx key shape fresh op).Path) :
    (retainedStep ctx key shape fresh op).visitedContexts path =
      [ctx, ctx.addRetained key shape fresh, ctx.addRetained key shape fresh] := rfl

/-- The resident peak includes the newly retained cell and all original systems. -/
theorem retainedStep_peakResidentSpace (path : (retainedStep ctx key shape fresh op).Path) :
    (retainedStep ctx key shape fresh op).peakResidentSpace path =
      (ctx.addRetained key shape fresh).residentSpace := by
  funext axis
  change max (ctx.residentSpace axis)
    (max ((ctx.addRetained key shape fresh).residentSpace axis)
      (max ((ctx.addRetained key shape fresh).residentSpace axis) 0)) = _
  simp only [Nat.max_zero, Nat.max_self]
  apply max_eq_right
  cases axis <;> simp

/-- The retained result counts as auxiliary storage in the actual path peak. -/
theorem retainedStep_peakAuxiliarySpace (path : (retainedStep ctx key shape fresh op).Path) :
    (retainedStep ctx key shape fresh op).peakAuxiliarySpace path =
      (ctx.addRetained key shape fresh).auxiliarySpace := by
  funext axis
  change max (ctx.auxiliarySpace axis)
    (max ((ctx.addRetained key shape fresh).auxiliarySpace axis)
      (max ((ctx.addRetained key shape fresh).auxiliarySpace axis) 0)) = _
  simp only [Nat.max_zero, Nat.max_self]
  apply max_eq_right
  cases axis <;> simp

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Execution updates the real store and retains every input block and reference correlation. -/
theorem execute_retainedStep {Reference : Register} {History : Type} [Fintype History]
    (state : Execution.State ctx Reference History) :
    (retainedStep ctx key shape fresh op).execute Reference state =
      state.mapClassical (fun value =>
        ((value.1.pushRetained key shape fresh).applyOp op, (value.2, ((), ())))) := by
  simp only [retainedStep, execute_seq, execute_retain, execute_classical,
    Execution.State.classicalStep, Execution.State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Borrowed classical values, quantum systems, and external correlations are restored jointly. -/
theorem retainedStep_borrowedRestored {Reference : Register} {History : Type} [Fintype History]
    (state : Execution.State ctx Reference History) :
    (retainedStep ctx key shape fresh op).BorrowedRestored Reference state
      ((retainedStep ctx key shape fresh op).execute Reference state) := by
  unfold retainedStep
  apply borrowedRestored_seq
  · exact borrowedRestored_retain key shape fresh state
  · exact borrowedRestored_classical op _

end

end QuantumAlg.Circuit
