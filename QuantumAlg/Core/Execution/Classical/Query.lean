/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Classical.Oracle
public import QuantumAlg.Core.Algorithm.ClassicalOp

/-!
# Typed placement of a granted classical query

The oracle signature owns the hidden-state type and accounting coordinate.
The execution environment supplies its transition. A query placement supplies
only the granted query instance and
its exact caller-visible input and output references. It cannot supply a
replacement transition, initialize the service or read its hidden state.
-/

namespace QuantumAlg.ClassicalOracleModel

/-- One granted classical query at exact live caller storage coordinates. -/
public structure Application (model : ClassicalOracleModel) {kind : ProblemKind}
    (ctx : RuntimeCtx kind) where
  /-- A query from this declaration's actual access language. -/
  query : model.Query
  /-- Read the declared operand from actual caller storage. -/
  input : CInputRef ctx (model.inputShape query)
  /-- Store the visible result in an actual writable cell. -/
  output : CWriteRef ctx (model.outputShape query)

end QuantumAlg.ClassicalOracleModel
