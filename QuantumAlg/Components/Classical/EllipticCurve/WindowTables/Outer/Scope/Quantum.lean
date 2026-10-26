/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Tables
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Circuit
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Quantum
import all QuantumAlg.Core.Base.Accounting.Context.Embedding.Construction

/-!
# Actual table allocation retaining the complete quantum wire record

The same five arrays and paid builder precede the actual point kernel.
The kernel receives the unchanged ordered physical wires and the real
fresh table references. Its type forbids further allocation. The wrapper
adds only the original lexical classical workspaces and identity embedding.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

variable {gates : GateModel} {oracles : OracleModel} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel}

local notation "Model" => ExecutionModel.quantum gates oracles operations services

/-- Five actual constructed arrays surround an allocation-free kernel on the same physical bank. -/
def Frame.withConstructedQuantumTables [BitWord.Selected Model]
    {ctx : RuntimeCtx .quantum} {wordWidth window : Nat}
    (frame : Frame ctx wordWidth) (spec : ModulusSpec wordWidth) (row : Fin 34)
    (body : ∀ {inner : RuntimeCtx .quantum}, Transport ctx inner →
      ctx.quantumLayout.wires = inner.quantumLayout.wires →
      TableFrame inner wordWidth (2 ^ window) → Circuit Model inner inner false) :
    Circuit Model ctx ctx :=
  withCellsWithQuantumWires (model := Model) ctx (tableShapes wordWidth (2 ^ window))
    fun cells distinct lift separated same =>
      let table := frame.tableFrame lift cells distinct separated row
      .seq (table.circuit spec)
        (.embed (ContextEmbedding.identity _) (body lift
          (quantumLayout_wires_of_quantumWires same) table))

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer
