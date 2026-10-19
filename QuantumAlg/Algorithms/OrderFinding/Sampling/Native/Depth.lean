/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Sampling.Native
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native
import all QuantumAlg.Core.Execution.Preparation.Resources
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Core.Execution.Trace

/-!
# Complete source-sample unit-event depth

The path contains one parallel preparation layer when the register is
nonempty, the full native phase/query/readout dependency, every sequential Z
write, and one finite-word packing instruction.
-/

namespace QuantumAlg.OrderFinding.Sampling.Native

noncomputable section

open QuantumAlg.Execution

/-- Independent duration limit from source widths and the expanded native QFT. -/
public def depthBudget (t width : Nat) : Nat :=
  (if t + width = 0 then 0 else 1) +
    ((if t = 0 then 0 else 1) + 1 +
      (t + 5 * t.choose 2 + (if t / 2 = 0 then 0 else 3))) + t + 1

private lemma preparation_depth (t width : Nat) :
    DepthExpr.depthEval (fun _ => 1)
      (ZeroPreparation.eventDepth AlgorithmGate.model
        (OrderFinding.Native.sourceModel t width)
        (runtimeLayout t width) BitWord.model .empty) =
      if t + width = 0 then 0 else 1 :=
  ZeroPreparation.zeroPreparation_unit_depth AlgorithmGate.model
    (OrderFinding.Native.sourceModel t width) (runtimeLayout t width)
    BitWord.model .empty

private lemma program_depth (t width : Nat) :
    DepthExpr.depthEval (fun _ => 1)
      ((nativeProgram t width).eventDepth BitWord.model .empty) =
      (if t = 0 then 0 else 1) + 1 +
        (t + 5 * t.choose 2 + (if t / 2 = 0 then 0 else 3)) := by
  rw [UnitaryCircuit.unitaryCircuit_unit_depth_classical_context]
  change (OrderFinding.Native.circuit t width).evaluatedEventDepth (fun _ => 1) = _
  exact OrderFinding.Native.circuit_unit_depth t width

/-- Every complete path has the independently stated unit-event depth. -/
public lemma code_depth (t width : Nat) (path : (code t width).Path) :
    (code t width).depth (fun _ => 1) path = depthBudget t width := by
  change (DepthExpr.depthEval (fun _ => 1)
      (ZeroPreparation.eventDepth AlgorithmGate.model
        (OrderFinding.Native.sourceModel t width)
        (runtimeLayout t width) BitWord.model .empty) +
    (DepthExpr.depthEval (fun _ => 1) ((nativeProgram t width).eventDepth BitWord.model .empty) +
      (0 + (MeasurementCells.allocate (model := model t width)
        (resultContext t width) 2 t).depth (fun _ => 1) path.1.2.2.2))) +
    ((Circuit.measurementSequence (gates := AlgorithmGate.model)
      (oracles := OrderFinding.Native.sourceModel t width)
      (operations := BitWord.model) (classicalOracles := .empty)
      (readouts t width)).depth (fun _ => 1) path.2.1 + 1) = _
  rw [preparation_depth, program_depth, MeasurementCells.allocate_depth,
    Circuit.measurementSequence_unitDepth]
  simp only [readouts, List.length_ofFn, zero_add]
  unfold depthBudget
  omega

end

end QuantumAlg.OrderFinding.Sampling.Native
