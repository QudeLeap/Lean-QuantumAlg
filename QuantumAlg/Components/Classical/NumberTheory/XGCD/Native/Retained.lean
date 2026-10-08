/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Public

/-!
# Actual retained public XGCD entry

The original right-nested gcd and two signed coefficients occupy one real
retained result beside every original context entry. Its actual allocation
precedes the shared raw arithmetic and original five public packing operations.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The complete actual final context retains the original public result shape. -/
def retainedCtx (ctx : RuntimeCtx kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys) : RuntimeCtx kind :=
  ctx.addRetained key (XGCDOutputShape width) fresh

/-- Read the original nominal public result from its actual retained cell. -/
def retainedRead (ctx : RuntimeCtx kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    CInputRef (retainedCtx ctx width key fresh) (XGCDOutputShape width) :=
  .storage (CStorageRef.retainedHead ctx key (XGCDOutputShape width) fresh)

/-- Allocate the original public result and execute its complete actual XGCD body. -/
def retainedCircuit {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    Circuit model ctx (retainedCtx ctx width key fresh) :=
  .seq (.retain ctx key (XGCDOutputShape width) fresh)
    (publicIntoResult (model := model) (input.underRetained key (XGCDOutputShape width) fresh)
      (CWriteRef.retainedHead ctx key (XGCDOutputShape width) fresh))

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
