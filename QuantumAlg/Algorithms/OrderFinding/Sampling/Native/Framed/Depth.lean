/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed
public import QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Depth
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Depth
import all QuantumAlg.Core.Execution.Preparation.Resources
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Core.Execution.Trace

/-!
# Complete sample depth with a classical input frame

The source preparation, native phase/query/readout word, sequential Z writes
and packed-word instruction have the same independent unit-event depth for
every pre-existing classical input. This is the full sample path, before any
classical order recovery.
-/

namespace QuantumAlg.OrderFinding.Sampling.Native.Framed

noncomputable section

open QuantumAlg.Execution

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])

private theorem preparation_depth {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    DepthExpr.depthEval (fun _ => 1)
      (ZeroPreparation.eventDepth AlgorithmGate.model
        (OrderFinding.Native.sourceModel access)
        (Sampling.Native.runtimeLayout t width) BitWord.model .empty) =
      if t + width = 0 then 0 else 1 :=
  ZeroPreparation.zeroPreparation_unit_depth AlgorithmGate.model
    (OrderFinding.Native.sourceModel access) (Sampling.Native.runtimeLayout t width)
    BitWord.model .empty

private theorem program_depth {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    DepthExpr.depthEval (fun _ => 1)
      ((nativeProgram ctx noQuantum access).eventDepth BitWord.model .empty) =
      (if t = 0 then 0 else 1) + 1 +
        (t + 5 * t.choose 2 + 3 * (t / 2)) := by
  rw [UnitaryCircuit.unitaryCircuit_unit_depth_classical_context]
  change (OrderFinding.Native.circuit access).evaluatedEventDepth (fun _ => 1) = _
  exact OrderFinding.Native.circuit_unit_depth access

/-- Every complete framed sample path has the independent unit-event depth. -/
public theorem code_depth {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (path : (code ctx noQuantum access).Path) :
    (code ctx noQuantum access).depth (fun _ => 1) path =
      Sampling.Native.depthBudget t width := by
  change (DepthExpr.depthEval (fun _ => 1)
      (ZeroPreparation.eventDepth AlgorithmGate.model
        (OrderFinding.Native.sourceModel access)
        (Sampling.Native.runtimeLayout t width) BitWord.model .empty) +
    (DepthExpr.depthEval (fun _ => 1)
      ((nativeProgram ctx noQuantum access).eventDepth BitWord.model .empty) +
      (0 + (MeasurementCells.allocate (model := model access)
        (resultContext ctx noQuantum t width) 2 t).depth (fun _ => 1)
          path.1.2.2.2))) +
    ((Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := OrderFinding.Native.sourceModel access)
      (operations := BitWord.model) (classicalOracles := .empty)
      (readouts ctx noQuantum t width)).depth (fun _ => 1) path.2.1 + 1) = _
  rw [preparation_depth, program_depth, MeasurementCells.allocate_depth,
    Circuit.measurementSequence_unitDepth]
  simp only [readouts, List.length_ofFn, zero_add]
  unfold Sampling.Native.depthBudget
  omega

end

end QuantumAlg.OrderFinding.Sampling.Native.Framed
