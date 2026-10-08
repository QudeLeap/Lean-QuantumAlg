/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.ZReset.Circuit
public import QuantumAlg.Core.Execution.Interpret
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Semantics
import all QuantumAlg.Primitives.ZReset.Circuit

/-!
# Complete execution semantics of measurement followed by exact native correction

The canonical component proves that the selected system ends in its zero basis
state and that the other systems retain their complete joint marginal with an
arbitrary external reference. These primitive observations use that same actual
execution and impose no separability or normalization assumption on the input.

The state calculation uses unitary conjugation [dW19, qcnotes.tex:5405], projective
measurement [dW19, qcnotes.tex:5409], and the local projector tensored with the
reference identity [dW19, qcnotes.tex:5420]. Any positive wire dimension is allowed
when its exact correction circuits are supplied in the chosen native model.
-/

namespace QuantumAlg.ZReset

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

/-- The actual complete execution has support only at the selected zero label.
Its surviving entries are the original joint marginal of all other systems
and the arbitrary reference. Classical input blocks and all observed outcomes
are summed exactly once. -/
public theorem zReset_execute_entry {gates : GateModel} {oracles : OracleModel}
    {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (realizations : QuditShift.Realizations gates oracles ctx.quantumLayout wire)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles).HiddenState × H))
    (left right : ctx.quantumLayout.Basis) (leftRef rightRef : Reference.Index) :
    ((circuit wire output realizations).execute Reference state).quantumMarginal.matrix
      (left, leftRef) (right, rightRef) =
      if left wire = ctx.quantumLayout.zeroLabel wire ∧
          right wire = ctx.quantumLayout.zeroLabel wire then
        ∑ entry : Store ctx × ((ExecutionModel.quantum gates oracles).HiddenState × H),
          ∑ outcome : Fin (ctx.quantumLayout.wire wire).dimension,
          (state.block entry).matrix (Function.update left wire outcome, leftRef)
            (Function.update right wire outcome, rightRef)
      else 0 :=
  QuditShift.resetCircuit_quantum_entry wire output realizations state
    left right leftRef rightRef

/-- No nonzero selected-system row survives in the actual final quantum state,
including entries correlated with any external reference. -/
public theorem zReset_execute_selected_zero {gates : GateModel} {oracles : OracleModel}
    {ctx : RuntimeCtx .quantum}
    (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (realizations : QuditShift.Realizations gates oracles ctx.quantumLayout wire)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles).HiddenState × H))
    (left right : ctx.quantumLayout.Basis) (leftRef rightRef : Reference.Index)
    (nonzero : left wire ≠ ctx.quantumLayout.zeroLabel wire) :
    ((circuit wire output realizations).execute Reference state).quantumMarginal.matrix
      (left, leftRef) (right, rightRef) = 0 := by
  rw [zReset_execute_entry]
  simp only [nonzero, false_and, if_false]

/-- Each complete store, service-state and path block has zero support away
from the reset basis label, before any classical outcomes are summed. -/
public theorem zReset_execute_block_selected_zero {gates : GateModel} {oracles : OracleModel}
    {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (realizations : QuditShift.Realizations gates oracles ctx.quantumLayout wire)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles).HiddenState × H))
    (result : Store ctx × ((ExecutionModel.quantum gates oracles).HiddenState ×
      (H × (circuit wire output realizations).Path)))
    (left right : ctx.quantumLayout.Basis) (leftRef rightRef : Reference.Index)
    (nonzero : left wire ≠ ctx.quantumLayout.zeroLabel wire) :
    (((circuit wire output realizations).execute Reference state).block result).matrix
      (left, leftRef) (right, rightRef) = 0 := by
  change (((QuditShift.resetCircuit wire output realizations).execute Reference state).block
    result).matrix (left, leftRef) (right, rightRef) = 0
  rw [QuditShift.resetCircuit_block_entry]
  change left wire ≠ 0 at nonzero
  simp [nonzero]

end

end QuantumAlg.ZReset
