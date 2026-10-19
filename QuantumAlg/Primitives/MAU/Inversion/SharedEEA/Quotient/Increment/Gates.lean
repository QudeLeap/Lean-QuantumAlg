/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Quotient.Increment
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.LowShift.Increment.Gates

/-!
# Literal HRS quotient instructions at their complete original placement

Both exchanges transport actual gates and physical wire addresses. All dirty
Work1 bits and every other field are retained, including zero counter width.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.QuotientIncrement

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit GateSpec

/-- The actual low-counter list placed first at Ctrl and then at the quotient field. -/
def gates (width : Nat) : List (GateSpec (encoding width)) :=
  ((LowShiftIncrement.gates width).map (ControlPlacement.placement width).placeGate).map
    (QuotientPlacement.placement width).placeGate

/-- The complete list increments only the selected quotient and restores all dirty data. -/
lemma quotientIncrement_gates_step (width : Nat) (state : Registers width) :
    stepList (gates width) state = step state := by
  rw [gates, EncodedBit.FullPlacement.placeGates_step]
  unfold EncodedBit.FullPlacement.step
  rw [EncodedBit.FullPlacement.placeGates_step]
  unfold EncodedBit.FullPlacement.step
  rw [LowShiftIncrement.lowShiftIncrement_gates_step]
  simp only [QuotientPlacement.placement_grouping_eq, ControlPlacement.placement_grouping_eq,
    QuotientPlacement.fieldEquiv, ControlPlacement.fieldEquiv, Equiv.coe_fn_mk,
    Equiv.coe_fn_symm_mk]
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨p1, p2, sign, iter⟩, control⟩
  cases control <;> rfl

/-- Exact amplitude realization imposes no condition on the borrowed word or incoming Ctrl. -/
lemma quotientIncrement_gates_realizes (width : Nat)
    (layout : QubitLayout (encoding width).width) :
    UnitaryCircuit.Realizes (layout := layout) (encoding width)
      (programList layout .empty (gates width)) environment step :=
  realizesList_congrStep layout .empty _ (quotientIncrement_gates_step width) environment

/-- Both complete wire placements preserve the original ordered HRS trace. -/
lemma quotientIncrement_gates_trace (width : Nat) :
    (gates width).map (event .empty) = (program width).eventTrace := by
  simp only [gates, List.map_map, Function.comp_def, EncodedBit.FullPlacement.placeGate_event]
  rw [LowShiftIncrement.lowShiftIncrement_gates_trace, program_eventTrace]

/-- Every native gate multiplicity is the original actual quotient incrementer's multiplicity. -/
lemma quotientIncrement_gates_eventCost (width : Nat) :
    ResourcePool.ofList ((gates width).map (event .empty)) = (program width).eventCost := by
  rw [quotientIncrement_gates_trace, UnitaryCircuit.ofList_eventTrace_eq_eventCost]

end

end QuantumAlg.MAU.Inversion.SharedEEA.QuotientIncrement
