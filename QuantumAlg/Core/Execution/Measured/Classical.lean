/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Fibers

/-!
# Actual Z writes followed by a closed classical instruction

The finite measurement sequence supplies its real outcomes and writes them
into actual storage. The following existing classical opcode reads that
storage and writes its result. Every observation of the resulting store
retains the complete reference matrix entry of that same actual fiber.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- A real classical opcode after Z writes has exactly its actual store-reference fiber. -/
theorem measurementSequence_classical_reference_entry {ctx : RuntimeCtx .quantum}
    (readouts : List (ZReadout ctx)) {input output : CShape}
    (op : ClassicalOp input output ctx ctx)
    {Reference : Register} {History Observed : Type} [Fintype History] [Fintype Observed]
    (state : State ctx Reference History) (observe : Store ctx → Observed) (value : Observed)
    (left right : Reference.Index) :
    (∑ basis : ctx.register.Index,
      DensityOperator.matrix
        ((ExecutionState.mapClassical
          ((Circuit.seq (measurementSequence readouts) (.classical op)).execute Reference state)
          (fun entry => observe entry.1)).block value) (basis, left) (basis, right)) =
      ExecutionState.referenceFiberSum state (fun original basis =>
        if observe ((writeMeasurementPath readouts original.1
          (measurementBasisPath readouts basis)).applyOp op) = value then 1 else 0) left right := by
  rw [ExecutionState.mapClassical_block_referenceFiberSum, execute_seq]
  simp only [State.mapHistory, ExecutionState.referenceFiberSum_mapClassical]
  rw [execute_classical]
  simp only [State.classicalStep, ExecutionState.referenceFiberSum_mapClassical]
  exact measurementSequence_referenceFiberSum readouts state
    (fun entry _ => if observe (entry.1.applyOp op) = value then 1 else 0) left right

end

end QuantumAlg.Circuit
