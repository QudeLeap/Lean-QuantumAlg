/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Classical.Model
public import QuantumAlg.Core.Algorithm.ClassicalOp

/-!
# Typed placement of a selected classical native operation

A placed instruction contains a token of the selected model and its actual
readable and writable references. Its input shape, output shape, distribution
and native coordinate are fixed by that same token. Placement supplies neither
an evaluator nor an alternative resource label.
-/

namespace QuantumAlg.ClassicalOpModel

/-- One granted native operation at exact live classical references. -/
public structure Application (model : ClassicalOpModel) {kind : ProblemKind}
    (ctx : RuntimeCtx kind) where
  /-- The selected model grants this particular operation instance. -/
  token : model.Token
  /-- Read only the operand shape required by this token. -/
  input : CInputRef ctx (model.inputShape token)
  /-- Write its declared result into a writable cell of the exact shape. -/
  output : CWriteRef ctx (model.outputShape token)

end QuantumAlg.ClassicalOpModel
