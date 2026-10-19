/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Context.Embedding
public import QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Context.Embedding
import all QuantumAlg.Core.Execution.Context.Permutation.Store
import all QuantumAlg.Core.Execution.Context.Relabeling.Store
import all QuantumAlg.Core.Execution.Context.Union.Store.Laws

/-!
# Structural readout through a physical context embedding

The same key placement used by execution lifts existing input references and
output observations. A caller output manifest includes its entire complement,
even when the child's result does not read it. No packing operation or new
runtime cell is hidden in the observation.
-/

namespace QuantumAlg.ContextEmbedding

noncomputable section

open Execution

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller) {shape : CShape}

/-- Follow the declared key placement for every structural read operand. -/
public def input (ref : CInputRef localCtx shape) : CInputRef caller shape :=
  ContextPermutation.input placement.covers
    (ContextUnion.inputLeft placement.separate
      (ContextRelabeling.input placement.keys placement.physical ref))

/-- The embedded reference reads the original child's value in the exact complete store. -/
public lemma contextEmbedding_input_read
    (localStore : Store localCtx) (frameStore : Store placement.frame)
    (ref : CInputRef localCtx shape) :
    (placement.store.symm (localStore, frameStore)).read (placement.input ref) =
      localStore.read ref := by
  change (ContextPermutation.store placement.covers
    (ContextUnion.join placement.separate
      (ContextRelabeling.storeEquiv placement.keys placement.physical localCtx localStore)
      frameStore)).read _ = _
  rw [input, ContextPermutation.store_read_input, ContextUnion.contextUnion_read_join_left,
    ContextRelabeling.store_read_input]

/-- Preserve the child's structural result without removing any caller resource. -/
public def outputRead (placement : ContextEmbedding localCtx caller) :
    {shape : CShape} → OutputRead localCtx shape → OutputRead caller shape
  | _, .unit => .unit
  | _, .read ref => .read (placement.input ref)
  | _, .product first second =>
      .product (outputRead placement first) (outputRead placement second)

/-- The caller manifest keeps all live keys and reads the child's placed result. -/
public def output (child : Output localCtx shape) : Output caller shape :=
  Output.all caller (placement.outputRead child.result)

/-- Every paired or payload-free child observation retains its actual finite value. -/
public lemma contextEmbedding_outputRead_eval
    (localStore : Store localCtx) (frameStore : Store placement.frame)
    (read : OutputRead localCtx shape) :
    (placement.outputRead read).eval (placement.store.symm (localStore, frameStore)) =
      read.eval localStore := by
  induction read with
  | unit => rfl
  | read ref => exact placement.contextEmbedding_input_read localStore frameStore ref
  | product first second firstIH secondIH =>
      exact congrArg₂ CShape.Value.product firstIH secondIH

/-- A complete placed output returns precisely the result of its local final store. -/
public lemma contextEmbedding_output_eval
    (localStore : Store localCtx) (frameStore : Store placement.frame)
    (child : Output localCtx shape) :
    (placement.output child).eval (placement.store.symm (localStore, frameStore)) =
      child.eval localStore :=
  placement.contextEmbedding_outputRead_eval localStore frameStore child.result

end

end QuantumAlg.ContextEmbedding
