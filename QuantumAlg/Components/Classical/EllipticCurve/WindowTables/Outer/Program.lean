/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Tables
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Query
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Circuit
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame.Columns
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Rows
import all QuantumAlg.Components.Classical.ConstantWord.Circuit

/-!
# Literal persistent preparation and short-lived five-table windows

Constants are loaded by actual native shifts/increments. Both original
point families occupy their disjoint seventeen-row halves of the same
two small arrays. A window allocates five arrays, builds them using the
same four persistent scalar words, executes six actual table-selected
query pairs, then exits all five array scopes. Complete point arithmetic
between loads and unlookups remains a separate integration boundary.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

namespace Frame

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat} (frame : Frame ctx width)

/-- Actual loaders for the public modulus/coefficient and the initially zero one-cell. -/
def initializeConstants (spec : ModulusSpec width) (coefficient : Nat) : Circuit model ctx ctx :=
  .seq (ConstantWord.circuit frame.modulus spec.modulus)
    (.seq (ConstantWord.circuit frame.curveA coefficient)
      (BitWord.instruction (ConstantWord.incrementOp frame.one)))

/-- Two paid base families in the original disjoint halves of the actual X/Y arrays. -/
def preparePairedBases (spec : ModulusSpec width)
    (firstX firstY secondX secondY : CInputRef ctx (.unsignedWord width)) :
    Circuit model ctx ctx :=
  .seq (frame.coordinates.prepareBasesAt spec firstX firstY (@firstBaseRows 16))
    (frame.coordinates.prepareBasesAt spec secondX secondY (@secondBaseRows 16))

end Frame

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {wordWidth lowWidth highRemaining : Nat}

local notation "Model" =>
  ExecutionModel.quantum AlgorithmGate.model OracleModel.empty BitWord.model services

/-- Build once, consume six actual columns from that same Store, and release all five arrays. -/
def Frame.windowCircuit (frame : Frame ctx wordWidth) (spec : ModulusSpec wordWidth)
    (row : Fin 34) (column : Fin 6 → Fin 5)
    (queries : ∀ {inner : RuntimeCtx .quantum}, Transport ctx inner →
      Fin 6 → QueryPlacement encoding inner wordWidth lowWidth highRemaining) :
    Circuit Model ctx ctx :=
  withCells (model := Model) ctx (tableShapes wordWidth (2 ^ (highRemaining + lowWidth + 1)))
    fun cells distinct lift separated =>
      let table := frame.tableFrame lift cells distinct separated row
      .seq (table.circuit spec)
        (Circuit.forRange 6 fun occurrence =>
          (queries lift occurrence).circuit
            (.storage (table.arrays.column (column occurrence)).toCStorageRef))

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer
