/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Control
import all QuantumAlg.Core.Base.Depth.EventCount

/-!
# Native accounting of an addressed coherent control

Placing the control within an existing encoded prefix changes each native
coordinate by one dimension-two control. It adds no separate initialization
or helper wire. Its shared control serializes the body events, including
events that originally belonged to parallel body branches.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

/-- The actual addressed control preserves each event and records its additional control. -/
theorem controlAtEncodedBit_native_pool {Data : Type} {encoding : BinaryLabelEncoding Data}
    (control : EncodedBit encoding) {width : Nat} (body : UnitaryCircuit (Qubits width)) :
    (controlAtEncodedBit control body).eventCost =
      ResourcePool.controlForDimension 2 body.eventCost := by
  unfold controlAtEncodedBit
  change (prodRight (m := encodedControlPrefixWidth control)
    (controlLeading (prodRight (m := encodedControlSuffixWidth control) body))).eventCost = _
  rw [prodRight_eventCost, controlLeading_eventCost, prodRight_eventCost]

/-- The same shared physical control serializes exactly the actual native occurrences. -/
theorem controlAtEncodedBit_unit_depth {Data : Type} {encoding : BinaryLabelEncoding Data}
    (control : EncodedBit encoding) {width : Nat} (body : UnitaryCircuit (Qubits width)) :
    (controlAtEncodedBit control body).evaluatedEventDepth (fun _ => 1) =
      body.eventCost.card := by
  let suffix := prodRight (m := encodedControlSuffixWidth control) body
  change (prodRight (m := encodedControlPrefixWidth control)
    (controlLeading suffix)).evaluatedEventDepth (fun _ => 1) = _
  rw [prodRight_evaluatedEventDepth]
  calc
    _ = DepthExpr.costEval (fun _ => (1 : Nat)) (shiftPhysicalIdx 1 suffix).eventDepth :=
      evaluatedEventDepth_controlQubitsAt (fun _ => 1) [0]
        (shiftPhysicalIdx 1 suffix) (leadingControlLayout suffix) (1 : Fin 2)
    _ = suffix.resourcesFromEventDepth.card := by
      rw [shiftPhysicalIdx_eventDepth]
      exact DepthExpr.unitCost_eq_eventPool_card _
    _ = suffix.eventCost.card :=
      congrArg Multiset.card (resourcesFromEventDepth_eq_eventCost suffix)
    _ = body.eventCost.card := congrArg Multiset.card (prodRight_eventCost body)

end

end QuantumAlg.UnitaryCircuit
