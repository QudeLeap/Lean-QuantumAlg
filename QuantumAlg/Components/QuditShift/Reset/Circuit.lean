/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.QuditShift
public import QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Components.QuditShift
import all QuantumAlg.Core.Execution.Context.Layout

/-!
# Actual measurement and stored-result correction on one wire

The circuit measures the selected physical wire into an existing finite
classical cell, reads that actual cell, and executes its negative cyclic
shift. Both operations use the same complete live context. No quantum
system is released and no fresh storage is allocated. State and resource
theorems are derived separately from this instruction sequence.
-/

namespace QuantumAlg.QuditShift

noncomputable section

variable {ctx : RuntimeCtx .quantum}

private instance circuitDimensionNeZero (dimension : ℕ+) : NeZero (dimension : ℕ) :=
  ⟨Nat.ne_of_gt dimension.property⟩

/-- Measure, store the result, then read it to select the actual correcting gate. -/
public def resetCircuit (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension)) :
    Circuit ctx ctx :=
  (Circuit.measureZ wire output).seq
    (.branch (.storage output.toCStorageRef) (fun value =>
      .unitary (program ctx.quantumLayout wire (-value.toFin))
        ((program_physical_idx ctx.quantumLayout wire (-value.toFin)).trans
          ctx.quantumLayout_identities)))

end

end QuantumAlg.QuditShift
