/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Adjoint
import all QuantumAlg.Core.Base.UnitaryCircuit.Adjoint
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Sequence
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Resource equations for actual generated adjoint circuits

A resource equation lifts through reversal only after it is proved for every
actual native and query replacement. The additive map below is a theorem
parameter; it cannot supply resources or execution semantics to a circuit.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

variable {sourceGates targetGates : GateModel} {sourceOracles targetOracles : OracleModel}

private theorem reverseWords_eventCost {count : Nat} {layout : QuantumLayout count}
    (words : List (UnitaryCircuit targetGates targetOracles layout)) :
    (reverseWords words).eventCost = (words.map fun word => word.eventCost).sum := by
  induction words with
  | nil => rfl
  | cons next rest ih =>
      change (reverseWords rest |>.seq next).eventCost = _
      rw [seq_eventCost, ih, List.map_cons, List.sum_cons]
      exact add_comm _ _

private theorem inverseSequence_eventCost
    (implementations : AdjointRealizations sourceGates sourceOracles targetGates targetOracles)
    (transform : ResourcePool (.quantum sourceGates sourceOracles) →+
      ResourcePool (.quantum targetGates targetOracles))
    (leafCost : ∀ {count : Nat} {layout : QuantumLayout count}
      (leaf : UnitaryLeaf sourceGates sourceOracles layout),
      (inverseLeaf implementations leaf).circuit.eventCost =
        transform (ResourcePool.singleton leaf.event))
    {count : Nat} {layout : QuantumLayout count}
    (sequence : UnitarySequence sourceGates sourceOracles layout) :
    (inverseSequence implementations sequence).circuit.eventCost =
      transform sequence.eventCost := by
  induction sequence with
  | id layout => exact (map_zero transform).symm
  | leaf leaf => exact leafCost leaf
  | seq left right leftIH rightIH =>
      change (inverseSequence implementations right).circuit.eventCost +
        (inverseSequence implementations left).circuit.eventCost =
          transform (left.eventCost + right.eventCost)
      rw [leftIH, rightIH, map_add, add_comm]
  | embed placement body ih => exact ih
  | parallel left right leftPlacement rightPlacement disjoint leftIH rightIH =>
      change (inverseSequence implementations right).circuit.eventCost +
        (inverseSequence implementations left).circuit.eventCost =
          transform (left.eventCost + right.eventCost)
      rw [leftIH, rightIH, map_add, add_comm]
  | iterate repetitions body ih =>
      change repetitions • (inverseSequence implementations body).circuit.eventCost =
        transform (repetitions • body.eventCost)
      rw [ih, map_nsmul]
  | indexedProduct label steps start step startIH stepIH =>
      change ((reverseWords (List.ofFn fun index =>
        (inverseSequence implementations (step index)).circuit)).seq
          (inverseSequence implementations start).circuit).eventCost =
        transform (start.eventCost + ∑ index, (step index).eventCost)
      rw [seq_eventCost, reverseWords_eventCost, startIH, map_add, map_sum]
      simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def, stepIH]
      exact add_comm _ _
  | macroCall name body ih => exact ih

/-- A proved resource map for every actual inverse replacement holds for the generated circuit. -/
public theorem dagger_eventCost
    {count : Nat} {layout : QuantumLayout count}
    (circuit : UnitaryCircuit sourceGates sourceOracles layout)
    (implementations : AdjointRealizations sourceGates sourceOracles targetGates targetOracles)
    (transform : ResourcePool (.quantum sourceGates sourceOracles) →+
      ResourcePool (.quantum targetGates targetOracles))
    (nativeCost : ∀ {count : Nat} {layout : QuantumLayout count}
      (application : GateModel.Application sourceGates layout),
      (implementations.native application).circuit.eventCost =
        transform (ResourcePool.singleton (.gate application.coordinate)))
    (queryCost : ∀ {count : Nat} {layout : QuantumLayout count}
      (application : OracleModel.Application sourceOracles layout),
      (implementations.query application).circuit.eventCost =
        transform (ResourcePool.singleton (.oracle application.coordinate))) :
    (circuit.dagger implementations).eventCost = transform circuit.eventCost := by
  apply inverseSequence_eventCost implementations transform
  intro count layout leaf
  cases leaf with
  | gate application => exact nativeCost application
  | oracle application => exact queryCost application

end

end QuantumAlg.UnitaryCircuit
