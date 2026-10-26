/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Placement.Subtraction
import all QuantumAlg.Primitives.MAU.Addition.TTK.Parallel
import all QuantumAlg.Primitives.MAU.Addition.TTK.Resources
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources

/-!
# Exact native resources of placed parallel TTK addition and subtraction

Physical placement preserves the source native event pool and dependency
schedule. Subtraction emits the actual native adjoint, with one inverse
per source gate, preserving every coordinate count and unit dependency
depth. No fresh system or free arithmetic action is supplied.
-/

namespace QuantumAlg.MAU.Addition.TTK.WordPlacement

noncomputable section

variable {Data : Type} {frame : BinaryLabelEncoding Data} {width : Nat}
    (placement : WordPlacement frame width)

/-- The actual physical parallel placement retains every original source event occurrence. -/
lemma program_eventCost : placement.program.eventCost = (lowRippleProgram width).eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, placement.program_eventTrace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost, ttkParallelLowRipple_eventCost]

/-- Every actual placed inverse gate has the same native coordinate as its source gate. -/
lemma subtractProgram_eventCost :
    placement.subtractProgram.eventCost = (lowRippleProgram width).eventCost := by
  have inverse : placement.subtractProgram.eventCost = placement.program.eventCost := by
    apply UnitaryCircuit.dagger_eventCost placement.program
      (AlgorithmGate.oracleFreeAdjoints .empty) (AddMonoidHom.id _)
    · intro count layout application
      change ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
          (.gate (AlgorithmGate.adjointApplication application).coordinate) =
        ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
          (.gate application.coordinate)
      rw [AlgorithmGate.algorithmGate_adjointApplication_coordinate]
    · intro count layout application
      exact False.elim (OracleModel.Occurrence.no_empty_oracle_occurrence application.occurrence)
  exact inverse.trans placement.program_eventCost

/-- Complete all-width Toffoli count of the actual inverse placed word. -/
lemma subtractProgram_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      placement.subtractProgram.eventCost = 2 * (width - 1) := by
  rw [placement.subtractProgram_eventCost, ttkLowRipple_toffoli_count]

/-- Complete all-width CNOT count of the actual inverse placed word. -/
lemma subtractProgram_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      placement.subtractProgram.eventCost = width + 2 * (width - 1) + 2 * (width - 2) := by
  rw [placement.subtractProgram_eventCost, ttkLowRipple_cnot_count]

/-- Reversing the actual parallel source schedule preserves its complete dependency duration. -/
lemma subtractProgram_unitDepth :
    placement.subtractProgram.evaluatedEventDepth (fun _ => 1) =
      (parallelLowRippleProgram width).evaluatedEventDepth (fun _ => 1) :=
  (AlgorithmGate.algorithmGate_oracleFreeAdjoints_unit_depth .empty placement.program).trans
    (placement.program_evaluatedEventDepth (fun _ => 1))

/-- The default duration bound uses the actual inverse parallel dependencies at valid widths. -/
lemma subtractProgram_quantumTime_le (enough : 2 ≤ width) :
    placement.subtractProgram.evaluatedEventDepth Resource.Event.quantumDuration ≤ 5 * width - 5 :=
  (DepthExpr.depthEval_mono Resource.Event.quantumDuration_le_one _).trans
    ((placement.subtractProgram_unitDepth).trans
      (ttkParallelLowRipple_depth_of_two_le width enough)).le

end

end QuantumAlg.MAU.Addition.TTK.WordPlacement
