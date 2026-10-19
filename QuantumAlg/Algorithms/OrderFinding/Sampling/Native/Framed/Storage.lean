/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Readout
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Coordinates
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Measure.Distribution

/-!
# The packed word contains the actual source phase readout

The selected finite-word opcode reads the real retained measurement cells.
For every basis path its result is the source phase-prefix outcome in the
same big-endian bit order used by the Born calculation.
-/

namespace QuantumAlg.OrderFinding.Sampling.Native.Framed

noncomputable section

open QuantumAlg.Execution

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])

/-- Packing the actually written cells yields the original phase outcome. -/
lemma packing_measured_value (t width : Nat)
    (store : Store (post ctx noQuantum t width))
    (basis : (post ctx noQuantum t width).register.Index)
    {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel} :
    (packing ctx noQuantum t width).eval
      ((Circuit.writeMeasurementPath (allowAllocation := true) (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := services)
        (readouts ctx noQuantum t width) store
        (Circuit.measurementBasisPath (allowAllocation := true)
          (gates := gates) (oracles := oracles)
          (operations := operations) (classicalOracles := services)
          (readouts ctx noQuantum t width) basis)).read
          (MeasurementCells.input (resultContext ctx noQuantum t width) 2 t)) =
      CShape.Value.bits ((OrderFinding.Native.measurement t width).readout
        (outputBasisEquiv ctx noQuantum t width basis)) := by
  change CShape.Value.bits (fun index => decide
    (((Circuit.writeMeasurementPath (allowAllocation := true) (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services)
      (readouts ctx noQuantum t width) store
      (Circuit.measurementBasisPath (allowAllocation := true) (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := services)
        (readouts ctx noQuantum t width) basis)).read
        (.storage
          (MeasurementCells.reference
            (resultContext ctx noQuantum t width) 2 t index).toCStorageRef)).toFin.val =
          1)) = _
  apply congrArg CShape.Value.bits
  funext index
  rw [measuredCell_value]
  exact phaseWire_bit ctx noQuantum t width basis index

end

end QuantumAlg.OrderFinding.Sampling.Native.Framed
