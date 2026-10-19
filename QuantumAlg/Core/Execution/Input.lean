/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.ExecutionState
public import QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Base.State.Density
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Normalized inputs and their local classical and quantum state

An input retains the entire joint state of its physical context and an arbitrary
external reference. Its local projection traces out that reference separately in
each classical block, preserving both classical probabilities and local quantum
states. Input validity can therefore depend on local data without distinguishing
different reference extensions of that same data.

Normalization uses the mixed-state convention [dW19, qcnotes.tex:5394]; the local
projection is the partial trace [dW19, qcnotes.tex:6827]. This projection is a
mathematical observation and does not release physical storage.
-/

namespace QuantumAlg.Execution

/-- A normalized finite classical and quantum input, including its full reference extension. -/
public structure Input {kind : ProblemKind} (ctx : RuntimeCtx kind) (Reference : Register) where
  /-- Joint classical blocks on the complete context and external reference. -/
  state : ExecutionState (Store ctx) (Register.prod ctx.register Reference)
  /-- The complete input distribution has total mass one. -/
  normalized : state.IsNormalized

namespace Input

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}

/-- The state visible to the input specification, retaining every actual classical value. -/
public def localState (input : Input ctx Reference) : ExecutionState (Store ctx) ctx.register where
  block value := DensityOperator.marginalLeft (input.state.block value)
  total_le_one := by
    simp_rw [DensityOperator.marginalLeft_mass]
    exact input.state.total_le_one

/-- Each local block is the reference marginal of that same classical input block. -/
@[simp] lemma localState_block (input : Input ctx Reference) (value : Store ctx) :
    input.localState.block value = DensityOperator.marginalLeft (input.state.block value) := rfl

/-- Local input entries retain off-diagonal coherences on the complete physical context. -/
lemma localState_block_entry (input : Input ctx Reference) (value : Store ctx)
    (left right : ctx.register.Index) :
    (input.localState.block value).matrix left right =
      ∑ reference : Reference.Index,
        (input.state.block value).matrix (left, reference) (right, reference) :=
  DensityOperator.marginalLeft_matrix (input.state.block value) left right

/-- Projecting away the reference does not change any classical input probability. -/
lemma localState_block_mass (input : Input ctx Reference) (value : Store ctx) :
    (input.localState.block value).mass = (input.state.block value).mass :=
  DensityOperator.marginalLeft_mass (input.state.block value)

/-- The local projection retains the complete input mass. -/
lemma localState_mass (input : Input ctx Reference) :
    input.localState.mass = input.state.mass := by
  simp only [ExecutionState.mass, localState_block_mass]

/-- Every certified input has a normalized local state. -/
lemma localState_normalized (input : Input ctx Reference) :
    input.localState.IsNormalized :=
  (localState_mass input).trans input.normalized

end

end Input

end QuantumAlg.Execution
