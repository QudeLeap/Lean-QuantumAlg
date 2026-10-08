/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Refinement
import all QuantumAlg.Core.Base.UnitaryCircuit.Refinement
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Sequence
import all QuantumAlg.Core.Base.UnitaryCircuit.Realization.Placement

/-!
# Resource substitution certified against actual replacement words

An additive accounting map is valid only after proving its value for every
actual native and query implementation. The complete construction then has
that mapped event pool, including repetitions and expanded macro bodies.
-/

namespace QuantumAlg.UnitaryCircuit
noncomputable section

variable {sourceGates targetGates : GateModel} {sourceOracles targetOracles : OracleModel}
variable (implementations :
  InstructionRealizations sourceGates sourceOracles targetGates targetOracles)
variable (accounting : ResourcePool (.quantum sourceGates sourceOracles) →+
  ResourcePool (.quantum targetGates targetOracles))
variable (nativeCost : ∀ {count : Nat} {layout : QuantumLayout count}
  (application : GateModel.Application sourceGates layout),
  (implementations.native application).circuit.eventCost =
    accounting (ResourcePool.singleton (.gate application.coordinate)))
variable (queryCost : ∀ {count : Nat} {layout : QuantumLayout count}
  (application : OracleModel.Application sourceOracles layout),
  (implementations.query application).circuit.eventCost =
    accounting (ResourcePool.singleton (.oracle application.coordinate)))

include nativeCost queryCost

private theorem realizeSequence_eventCost {count : Nat} {layout : QuantumLayout count}
    (sequence : UnitarySequence sourceGates sourceOracles layout) :
    (realizeSequence implementations sequence).circuit.eventCost =
      accounting sequence.eventCost := by
  induction sequence with
  | id layout => simp [realizeSequence, UnitarySequence.eventCost]
  | leaf atom =>
      cases atom with
      | gate application => exact nativeCost application
      | oracle application => exact queryCost application
  | seq left right leftIH rightIH =>
      simp [realizeSequence, UnitarySequence.eventCost, leftIH, rightIH]
  | embed placement body bodyIH =>
      simpa only [realizeSequence, eventCost, embed, UnitarySequence.eventCost] using bodyIH
  | parallel left right leftPlacement rightPlacement disjoint leftIH rightIH =>
      change (realizeSequence implementations left).circuit.eventCost +
        (realizeSequence implementations right).circuit.eventCost = _
      rw [leftIH, rightIH, ← map_add]
      rfl
  | iterate repetitions body bodyIH =>
      simp [realizeSequence, UnitarySequence.eventCost, bodyIH]
  | indexedProduct label steps start step startIH stepIH =>
      simp [realizeSequence, UnitarySequence.eventCost, startIH, stepIH, map_sum]
  | macroCall name body bodyIH =>
      simpa only [realizeSequence, macroCall_eventCost, UnitarySequence.eventCost] using bodyIH

/-- The substituted event pool belongs to the same actual refined circuit as its matrix. -/
public theorem refine_eventCost {count : Nat} {layout : QuantumLayout count}
    (circuit : UnitaryCircuit sourceGates sourceOracles layout) :
    (circuit.refine implementations).eventCost = accounting circuit.eventCost :=
  realizeSequence_eventCost implementations accounting nativeCost queryCost circuit.sequence

end
end QuantumAlg.UnitaryCircuit
