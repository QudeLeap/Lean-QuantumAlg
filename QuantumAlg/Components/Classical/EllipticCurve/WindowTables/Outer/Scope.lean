/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Program

/-!
# Actual constructed-table lexical scope for a concrete point-kernel body

The body receives the same fresh array references written by the original
paid builder and the structural transport of every caller reference. The
body is an actual circuit, so an interleaved point kernel must provide its
real code and prove its own resources and table-graph preservation. No
supplied operator, table value, free action or budget replaces execution.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

/-- Real five-array allocation, paid construction, actual supplied consumer, and lexical release. -/
def Frame.withConstructedTables {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {wordWidth window : Nat}
    (frame : Frame ctx wordWidth) (spec : ModulusSpec wordWidth) (row : Fin 34)
    (body : ∀ {inner : RuntimeCtx model.kind}, Transport ctx inner →
      TableFrame inner wordWidth (2 ^ window) → Circuit model inner inner) :
    Circuit model ctx ctx :=
  withCells (model := model) ctx (tableShapes wordWidth (2 ^ window))
    fun cells distinct lift separated =>
      let table := frame.tableFrame lift cells distinct separated row
      .seq (table.circuit spec) (body lift table)

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {wordWidth lowWidth highRemaining : Nat}

/-- The query fragment is a literal specialization of the same actual constructed-table scope. -/
lemma Frame.windowCircuit_eq_withConstructedTables (frame : Frame ctx wordWidth)
    (spec : ModulusSpec wordWidth) (row : Fin 34) (column : Fin 6 → Fin 5)
    (queries : ∀ {inner : RuntimeCtx .quantum}, Transport ctx inner →
      Fin 6 → QueryPlacement encoding inner wordWidth lowWidth highRemaining) :
    frame.windowCircuit (services := services) spec row column queries =
      frame.withConstructedTables spec row (fun lift table =>
        Circuit.forRange 6 fun occurrence =>
          (queries lift occurrence).circuit
            (.storage (table.arrays.column (column occurrence)).toCStorageRef)) := rfl

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer
